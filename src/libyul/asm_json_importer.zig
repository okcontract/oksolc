// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Imports the stable inline-assembly JSON representation into an owned Yul AST.
//!
//! JSON strings and source-name entries are borrowed. Every recursive AST
//! container and literal representation is owned by the caller-provided
//! allocator and released by `AST.deinit`.

const std = @import("std");
const AST = @import("ast.zig");
const AsmJsonConverter = @import("asm_json_converter.zig");
const AsmParser = @import("asm_parser.zig");
const AsmPrinter = @import("asm_printer.zig");
const CommonData = @import("../libsolutil/common_data.zig");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const JSON = @import("../libsolutil/json.zig");
const Scanner = @import("../liblangutil/scanner.zig");
const SourceLocationModule = @import("../liblangutil/source_location.zig");
const Utilities = @import("utilities.zig");
const YulName = @import("yul_name.zig").YulName;

pub const ImportError = std.mem.Allocator.Error ||
    CommonData.FromHexError ||
    Scanner.ScanFailure ||
    SourceLocationModule.ParseError ||
    Utilities.LiteralError ||
    error{
        ExpectedArray,
        ExpectedObject,
        ExpectedString,
        InvalidBooleanLiteralToken,
        InvalidDefaultCase,
        InvalidExpressionNodeType,
        InvalidLiteral,
        InvalidLiteralKind,
        InvalidLiteralType,
        InvalidNodeTypePrefix,
        InvalidNumberLiteralToken,
        InvalidSourceLocation,
        InvalidStatementNodeType,
        MissingLiteralValue,
        MissingMember,
        StringLiteralTooLong,
    };

pub const AsmJsonImporter = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    source_names: []const []const u8,

    pub fn init(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        source_names: []const []const u8,
    ) AsmJsonImporter {
        return .{
            .allocator = allocator,
            .dialect = dialect,
            .source_names = source_names,
        };
    }

    pub fn createAST(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.AST {
        return AST.AST.init(self.allocator, self.dialect, try self.createBlock(node));
    }

    fn createDebugData(self: *const AsmJsonImporter, node: JSON.Json) ImportError!DebugData {
        const source_text = try stringValue(member(node, "src"));
        const location = try SourceLocationModule.parseSourceLocation(source_text, self.source_names);
        if (!location.hasText()) return error.InvalidSourceLocation;
        // The legacy JSON surface does not carry a separately importable
        // origin location. Inline assembly has identical native/origin spans.
        return .{
            .native_location = location,
            .origin_location = location,
        };
    }

    fn createNameWithDebugData(
        self: *AsmJsonImporter,
        node: JSON.Json,
    ) ImportError!AST.NameWithDebugData {
        return .{
            .debug_data = try self.createDebugData(node),
            .name = try YulName.init(try stringValue(member(node, "name"))),
        };
    }

    fn createStatement(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Statement {
        const node_type = try yulNodeType(node);
        if (std.mem.eql(u8, node_type, "ExpressionStatement"))
            return .{ .expression_statement = try self.createExpressionStatement(node) };
        if (std.mem.eql(u8, node_type, "Assignment"))
            return .{ .assignment = try self.createAssignment(node) };
        if (std.mem.eql(u8, node_type, "VariableDeclaration"))
            return .{ .variable_declaration = try self.createVariableDeclaration(node) };
        if (std.mem.eql(u8, node_type, "FunctionDefinition"))
            return .{ .function_definition = try self.createFunctionDefinition(node) };
        if (std.mem.eql(u8, node_type, "If"))
            return .{ .if_statement = try self.createIf(node) };
        if (std.mem.eql(u8, node_type, "Switch"))
            return .{ .switch_statement = try self.createSwitch(node) };
        if (std.mem.eql(u8, node_type, "ForLoop"))
            return .{ .for_loop = try self.createForLoop(node) };
        if (std.mem.eql(u8, node_type, "Break"))
            return .{ .break_statement = .{ .debug_data = try self.createDebugData(node) } };
        if (std.mem.eql(u8, node_type, "Continue"))
            return .{ .continue_statement = .{ .debug_data = try self.createDebugData(node) } };
        if (std.mem.eql(u8, node_type, "Leave"))
            return .{ .leave_statement = .{ .debug_data = try self.createDebugData(node) } };
        if (std.mem.eql(u8, node_type, "Block"))
            return .{ .block = try self.createBlock(node) };
        return error.InvalidStatementNodeType;
    }

    fn createExpression(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Expression {
        const node_type = try yulNodeType(node);
        if (std.mem.eql(u8, node_type, "FunctionCall"))
            return .{ .function_call = try self.createFunctionCall(node) };
        if (std.mem.eql(u8, node_type, "Identifier"))
            return .{ .identifier = try self.createIdentifier(node) };
        if (std.mem.eql(u8, node_type, "Literal"))
            return .{ .literal = try self.createLiteral(node) };
        return error.InvalidExpressionNodeType;
    }

    fn createBlock(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Block {
        var result: AST.Block = .{ .debug_data = try self.createDebugData(node) };
        errdefer result.deinit(self.allocator);
        for (try arrayItems(member(node, "statements"))) |statement_node| {
            var statement = try self.createStatement(statement_node);
            errdefer statement.deinit(self.allocator);
            try result.statements.append(self.allocator, statement);
        }
        return result;
    }

    fn createLiteral(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Literal {
        const kind_text = try stringValue(member(node, "kind"));
        const has_hex_value = contains(node, "hexValue");
        const has_string_value = isString(member(node, "value"));
        if ((!has_hex_value or !isString(member(node, "hexValue"))) and !has_string_value)
            return error.MissingLiteralValue;

        var owned_value: ?[]u8 = null;
        defer if (owned_value) |value| self.allocator.free(value);
        const value = if (has_hex_value) value: {
            owned_value = try CommonData.fromHexAlloc(
                self.allocator,
                try stringValue(member(node, "hexValue")),
                .throw,
            );
            break :value owned_value.?;
        } else try stringValue(member(node, "value"));

        const type_node = member(node, "type");
        if (!jsonEmpty(type_node)) {
            const literal_type = try stringValue(type_node);
            if (literal_type.len != 0) return error.InvalidLiteralType;
        }

        const kind: AST.LiteralKind = if (std.mem.eql(u8, kind_text, "number")) kind: {
            try validateLiteralToken(self.allocator, value, .Number);
            break :kind .Number;
        } else if (std.mem.eql(u8, kind_text, "bool")) kind: {
            try validateLiteralToken(self.allocator, value, .Boolean);
            break :kind .Boolean;
        } else if (std.mem.eql(u8, kind_text, "string")) kind: {
            if (value.len > 32) return error.StringLiteralTooLong;
            break :kind .String;
        } else return error.InvalidLiteralKind;

        var result: AST.Literal = .{
            .debug_data = try self.createDebugData(node),
            .kind = kind,
            .value = try Utilities.valueOfLiteral(self.allocator, value, kind, false),
        };
        errdefer result.deinit(self.allocator);
        if (!Utilities.validLiteral(&result)) return error.InvalidLiteral;
        return result;
    }

    fn createIdentifier(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Identifier {
        return .{
            .debug_data = try self.createDebugData(node),
            .name = try YulName.init(try stringValue(member(node, "name"))),
        };
    }

    fn createAssignment(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Assignment {
        var result: AST.Assignment = .{ .debug_data = try self.createDebugData(node) };
        errdefer result.deinit(self.allocator);
        if (contains(node, "variableNames")) {
            for (try arrayItems(member(node, "variableNames"))) |variable_node|
                try result.variable_names.append(self.allocator, try self.createIdentifier(variable_node));
        }
        result.value = try AST.createExpression(
            self.allocator,
            try self.createExpression(member(node, "value")),
        );
        return result;
    }

    fn createFunctionCall(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.FunctionCall {
        const function_name_node = member(node, "functionName");
        const function_name_text = try stringValue(member(function_name_node, "name"));
        const function_name: AST.FunctionName = if (self.dialect.findBuiltin(function_name_text)) |handle|
            .{ .builtin = .{
                .debug_data = try self.createDebugData(function_name_node),
                .handle = handle,
            } }
        else
            .{ .identifier = try self.createIdentifier(function_name_node) };

        var result: AST.FunctionCall = .{
            .debug_data = try self.createDebugData(node),
            .function_name = function_name,
        };
        errdefer result.deinit(self.allocator);
        for (try arrayItems(member(node, "arguments"))) |argument_node| {
            var argument = try self.createExpression(argument_node);
            errdefer argument.deinit(self.allocator);
            try result.arguments.append(self.allocator, argument);
        }
        return result;
    }

    fn createExpressionStatement(
        self: *AsmJsonImporter,
        node: JSON.Json,
    ) ImportError!AST.ExpressionStatement {
        return .{
            .debug_data = try self.createDebugData(node),
            .expression = try self.createExpression(member(node, "expression")),
        };
    }

    fn createVariableDeclaration(
        self: *AsmJsonImporter,
        node: JSON.Json,
    ) ImportError!AST.VariableDeclaration {
        var result: AST.VariableDeclaration = .{ .debug_data = try self.createDebugData(node) };
        errdefer result.deinit(self.allocator);
        for (try arrayItems(member(node, "variables"))) |variable_node|
            try result.variables.append(self.allocator, try self.createNameWithDebugData(variable_node));
        // Preserve the C++ importer's `contains` behavior: an explicitly null
        // value is not treated like an absent initializer.
        if (contains(node, "value"))
            result.value = try AST.createExpression(
                self.allocator,
                try self.createExpression(member(node, "value")),
            );
        return result;
    }

    fn createFunctionDefinition(
        self: *AsmJsonImporter,
        node: JSON.Json,
    ) ImportError!AST.FunctionDefinition {
        var result: AST.FunctionDefinition = .{
            .debug_data = try self.createDebugData(node),
            .name = try YulName.init(try stringValue(member(node, "name"))),
        };
        errdefer result.deinit(self.allocator);
        if (contains(node, "parameters")) {
            for (try arrayItems(member(node, "parameters"))) |parameter_node|
                try result.parameters.append(self.allocator, try self.createNameWithDebugData(parameter_node));
        }
        if (contains(node, "returnVariables")) {
            for (try arrayItems(member(node, "returnVariables"))) |return_node|
                try result.return_variables.append(self.allocator, try self.createNameWithDebugData(return_node));
        }
        result.body = try self.createBlock(member(node, "body"));
        return result;
    }

    fn createIf(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.If {
        var result: AST.If = .{ .debug_data = try self.createDebugData(node) };
        errdefer result.deinit(self.allocator);
        result.condition = try AST.createExpression(
            self.allocator,
            try self.createExpression(member(node, "condition")),
        );
        result.body = try self.createBlock(member(node, "body"));
        return result;
    }

    fn createCase(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Case {
        var result: AST.Case = .{ .debug_data = try self.createDebugData(node) };
        errdefer result.deinit(self.allocator);
        const value_node = member(node, "value");
        if (isString(value_node)) {
            if (!std.mem.eql(u8, try stringValue(value_node), "default"))
                return error.InvalidDefaultCase;
        } else {
            result.value = try AST.createLiteral(self.allocator, try self.createLiteral(value_node));
        }
        result.body = try self.createBlock(member(node, "body"));
        return result;
    }

    fn createSwitch(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.Switch {
        var result: AST.Switch = .{ .debug_data = try self.createDebugData(node) };
        errdefer result.deinit(self.allocator);
        result.expression = try AST.createExpression(
            self.allocator,
            try self.createExpression(member(node, "expression")),
        );
        for (try arrayItems(member(node, "cases"))) |case_node| {
            var case_value = try self.createCase(case_node);
            errdefer case_value.deinit(self.allocator);
            try result.cases.append(self.allocator, case_value);
        }
        return result;
    }

    fn createForLoop(self: *AsmJsonImporter, node: JSON.Json) ImportError!AST.ForLoop {
        var result: AST.ForLoop = .{ .debug_data = try self.createDebugData(node) };
        errdefer result.deinit(self.allocator);
        result.pre = try self.createBlock(member(node, "pre"));
        result.condition = try AST.createExpression(
            self.allocator,
            try self.createExpression(member(node, "condition")),
        );
        result.post = try self.createBlock(member(node, "post"));
        result.body = try self.createBlock(member(node, "body"));
        return result;
    }
};

fn member(node: JSON.Json, name: []const u8) JSON.Json {
    return switch (node) {
        .object => |object| object.get(name) orelse .null,
        else => .null,
    };
}

fn contains(node: JSON.Json, name: []const u8) bool {
    return switch (node) {
        .object => |object| object.contains(name),
        else => false,
    };
}

fn stringValue(node: JSON.Json) ImportError![]const u8 {
    return switch (node) {
        .string => |value| value,
        .null => error.MissingMember,
        else => error.ExpectedString,
    };
}

fn arrayItems(node: JSON.Json) ImportError![]const JSON.Json {
    return switch (node) {
        .array => |array| array.items,
        .null => error.MissingMember,
        else => error.ExpectedArray,
    };
}

fn isString(node: JSON.Json) bool {
    return switch (node) {
        .string => true,
        else => false,
    };
}

fn jsonEmpty(node: JSON.Json) bool {
    return switch (node) {
        .null => true,
        .string => |value| value.len == 0,
        .array => |value| value.items.len == 0,
        .object => |value| value.count() == 0,
        else => false,
    };
}

fn yulNodeType(node: JSON.Json) ImportError![]const u8 {
    if (node != .object) return error.ExpectedObject;
    const node_type = try stringValue(member(node, "nodeType"));
    if (!std.mem.startsWith(u8, node_type, "Yul")) return error.InvalidNodeTypePrefix;
    return node_type[3..];
}

fn validateLiteralToken(
    allocator: std.mem.Allocator,
    value: []const u8,
    kind: AST.LiteralKind,
) ImportError!void {
    var stream = Scanner.CharStream.initBorrowed(value, "");
    var scanner = try Scanner.Scanner.init(allocator, &stream, .Solidity);
    defer scanner.deinit();
    switch (kind) {
        .Number => if (scanner.currentToken() != .Number)
            return error.InvalidNumberLiteralToken,
        .Boolean => if (scanner.currentToken() != .TrueLiteral and
            scanner.currentToken() != .FalseLiteral)
            return error.InvalidBooleanLiteralToken,
        .String => unreachable,
    }
}

test "inline assembly JSON round-trips all Yul statement families" {
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const source =
        \\{
        \\  let x := 1
        \\  x := foo(x)
        \\  if x { x := 2 }
        \\  switch x case 1 { x := 3 } default { x := 4 }
        \\  for { let i := 0 } lt(i, 10) { i := add(i, 1) } { if i { continue } break }
        \\  function f(a) -> r { r := a leave }
        \\}
    ;
    var original = (try AsmParser.Parser.parseSource(
        allocator,
        source,
        "input.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer original.deinit();
    var json = try AsmJsonConverter.AsmJsonConverter.convertAlloc(allocator, &original, 0);
    defer json.deinit();
    const source_names = [_][]const u8{"input.yul"};
    var importer = AsmJsonImporter.init(allocator, .{}, &source_names);
    var imported = try importer.createAST(json.value);
    defer imported.deinit();
    const original_text = try AsmPrinter.AsmPrinter.formatDefault(allocator, &original);
    defer allocator.free(original_text);
    const imported_text = try AsmPrinter.AsmPrinter.formatDefault(allocator, &imported);
    defer allocator.free(imported_text);
    try std.testing.expectEqualStrings(original_text, imported_text);
    try std.testing.expectEqualStrings(
        "input.yul",
        imported.root().debug_data.?.native_location.source_name.?,
    );
}

test "explicit null variable initializer preserves upstream rejection" {
    const allocator = std.testing.allocator;
    var parsed = try JSON.jsonParseStrict(allocator,
        \\{"nodeType":"YulBlock","src":"0:1:0","statements":[{"nodeType":"YulVariableDeclaration","src":"0:1:0","variables":[],"value":null}]}
    );
    defer parsed.deinit();
    const source_names = [_][]const u8{"input.yul"};
    var importer = AsmJsonImporter.init(allocator, .{}, &source_names);
    switch (parsed) {
        .document => |*document| try std.testing.expectError(
            error.ExpectedObject,
            importer.createAST(document.parsed.value),
        ),
        .failure => return error.UnexpectedJsonFailure,
    }
}
