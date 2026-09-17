// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Compact JSON conversion for Yul ASTs.

const std = @import("std");
const AST = @import("ast.zig");
const CommonData = @import("../libsolutil/common_data.zig");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const JSON = @import("../libsolutil/json.zig");
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;
const UTF8 = @import("../libsolutil/utf8.zig");
const Utilities = @import("utilities.zig");

pub const JsonError = std.mem.Allocator.Error || Utilities.LiteralError || error{
    InvalidAst,
    InvalidYulStringHandle,
    UnknownBuiltin,
};

/// Arena-owned dynamic JSON. The arena itself is heap-stable because the
/// managed JSON arrays retain its allocator context after this value moves.
pub const OwnedYulJson = struct {
    backing_allocator: std.mem.Allocator,
    arena: *std.heap.ArenaAllocator,
    value: JSON.Json,

    pub fn init(backing_allocator: std.mem.Allocator) std.mem.Allocator.Error!OwnedYulJson {
        const arena = try backing_allocator.create(std.heap.ArenaAllocator);
        arena.* = std.heap.ArenaAllocator.init(backing_allocator);
        return .{
            .backing_allocator = backing_allocator,
            .arena = arena,
            .value = .null,
        };
    }

    pub fn allocator(self: *const OwnedYulJson) std.mem.Allocator {
        return self.arena.allocator();
    }

    pub fn root(self: *OwnedYulJson) *JSON.Json {
        return &self.value;
    }

    pub fn rootConst(self: *const OwnedYulJson) *const JSON.Json {
        return &self.value;
    }

    pub fn deinit(self: *OwnedYulJson) void {
        self.arena.deinit();
        self.backing_allocator.destroy(self.arena);
        self.* = undefined;
    }
};

pub const AsmJsonConverter = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    source_index: ?usize,

    pub fn init(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        source_index: ?usize,
    ) AsmJsonConverter {
        return .{
            .allocator = allocator,
            .dialect = dialect,
            .source_index = source_index,
        };
    }

    pub fn convertAlloc(
        backing_allocator: std.mem.Allocator,
        ast: *const AST.AST,
        source_index: ?usize,
    ) JsonError!OwnedYulJson {
        var result = try OwnedYulJson.init(backing_allocator);
        errdefer result.deinit();
        var converter = AsmJsonConverter.init(
            result.allocator(),
            ast.dialect().*,
            source_index,
        );
        result.value = try converter.convertBlock(ast.root());
        return result;
    }

    pub fn convertBlock(self: *AsmJsonConverter, node: *const AST.Block) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulBlock");
        var statements = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (node.statements.items) |*statement| {
            try statements.append(try self.convertStatement(statement));
        }
        try result.object.put(self.allocator, "statements", .{ .array = statements });
        return result;
    }

    pub fn convertName(self: *AsmJsonConverter, node: *const AST.NameWithDebugData) JsonError!JSON.Json {
        if (node.name.empty()) return error.InvalidAst;
        var result = try self.createAstNode(node.debug_data, "YulTypedName");
        try result.object.put(self.allocator, "name", try self.ownedString(try node.name.str()));
        try result.object.put(self.allocator, "type", try self.ownedString(""));
        return result;
    }

    pub fn convertLiteral(self: *AsmJsonConverter, node: *const AST.Literal) JsonError!JSON.Json {
        if (!Utilities.validLiteral(node)) return error.InvalidAst;
        var result = try self.createAstNode(node.debug_data, "YulLiteral");
        const formatted = try Utilities.formatLiteralAlloc(self.allocator, node, true);
        switch (node.kind) {
            .Number => try result.object.put(self.allocator, "kind", try self.ownedString("number")),
            .Boolean => try result.object.put(self.allocator, "kind", try self.ownedString("bool")),
            .String => {
                try result.object.put(self.allocator, "kind", try self.ownedString("string"));
                const hex_value = try CommonData.toHexAlloc(
                    self.allocator,
                    formatted,
                    .dont_add,
                    .lower,
                );
                try result.object.put(self.allocator, "hexValue", .{ .string = hex_value });
            },
        }
        try result.object.put(self.allocator, "type", try self.ownedString(""));
        if (UTF8.isValidUTF8(formatted)) {
            try result.object.put(self.allocator, "value", try self.ownedString(formatted));
        }
        return result;
    }

    pub fn convertIdentifier(self: *AsmJsonConverter, node: *const AST.Identifier) JsonError!JSON.Json {
        if (node.name.empty()) return error.InvalidAst;
        var result = try self.createAstNode(node.debug_data, "YulIdentifier");
        try result.object.put(self.allocator, "name", try self.ownedString(try node.name.str()));
        return result;
    }

    pub fn convertBuiltinName(self: *AsmJsonConverter, node: *const AST.BuiltinName) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulIdentifier");
        const builtin = self.dialect.builtin(node.handle) catch return error.UnknownBuiltin;
        try result.object.put(self.allocator, "name", try self.ownedString(builtin.name));
        return result;
    }

    pub fn convertAssignment(self: *AsmJsonConverter, node: *const AST.Assignment) JsonError!JSON.Json {
        if (node.variable_names.items.len == 0) return error.InvalidAst;
        var result = try self.createAstNode(node.debug_data, "YulAssignment");
        var variable_names = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (node.variable_names.items) |*variable| {
            try variable_names.append(try self.convertIdentifier(variable));
        }
        try result.object.put(self.allocator, "variableNames", .{ .array = variable_names });
        try result.object.put(
            self.allocator,
            "value",
            if (node.value) |value| try self.convertExpression(value) else .null,
        );
        return result;
    }

    pub fn convertVariableDeclaration(
        self: *AsmJsonConverter,
        node: *const AST.VariableDeclaration,
    ) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulVariableDeclaration");
        var variables = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (node.variables.items) |*variable| {
            try variables.append(try self.convertName(variable));
        }
        try result.object.put(self.allocator, "variables", .{ .array = variables });
        try result.object.put(
            self.allocator,
            "value",
            if (node.value) |value| try self.convertExpression(value) else .null,
        );
        return result;
    }

    pub fn convertFunctionDefinition(
        self: *AsmJsonConverter,
        node: *const AST.FunctionDefinition,
    ) JsonError!JSON.Json {
        if (node.name.empty()) return error.InvalidAst;
        var result = try self.createAstNode(node.debug_data, "YulFunctionDefinition");
        try result.object.put(self.allocator, "name", try self.ownedString(try node.name.str()));
        var parameters = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (node.parameters.items) |*parameter| {
            try parameters.append(try self.convertName(parameter));
        }
        try result.object.put(self.allocator, "parameters", .{ .array = parameters });
        var return_variables = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (node.return_variables.items) |*variable| {
            try return_variables.append(try self.convertName(variable));
        }
        try result.object.put(self.allocator, "returnVariables", .{ .array = return_variables });
        try result.object.put(self.allocator, "body", try self.convertBlock(&node.body));
        return result;
    }

    pub fn convertFunctionCall(
        self: *AsmJsonConverter,
        node: *const AST.FunctionCall,
    ) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulFunctionCall");
        try result.object.put(
            self.allocator,
            "functionName",
            try self.convertFunctionName(&node.function_name),
        );
        var arguments = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (node.arguments.items) |*argument| {
            try arguments.append(try self.convertExpression(argument));
        }
        try result.object.put(self.allocator, "arguments", .{ .array = arguments });
        return result;
    }

    pub fn convertExpressionStatement(
        self: *AsmJsonConverter,
        node: *const AST.ExpressionStatement,
    ) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulExpressionStatement");
        try result.object.put(self.allocator, "expression", try self.convertExpression(&node.expression));
        return result;
    }

    pub fn convertIf(self: *AsmJsonConverter, node: *const AST.If) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulIf");
        try result.object.put(
            self.allocator,
            "condition",
            try self.convertExpression(node.condition orelse return error.InvalidAst),
        );
        try result.object.put(self.allocator, "body", try self.convertBlock(&node.body));
        return result;
    }

    pub fn convertSwitch(self: *AsmJsonConverter, node: *const AST.Switch) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulSwitch");
        try result.object.put(
            self.allocator,
            "expression",
            try self.convertExpression(node.expression orelse return error.InvalidAst),
        );
        var cases = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (node.cases.items) |*case_value| {
            try cases.append(try self.convertCase(case_value));
        }
        try result.object.put(self.allocator, "cases", .{ .array = cases });
        return result;
    }

    pub fn convertCase(self: *AsmJsonConverter, node: *const AST.Case) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulCase");
        try result.object.put(
            self.allocator,
            "value",
            if (node.value) |value|
                try self.convertLiteral(value)
            else
                try self.ownedString("default"),
        );
        try result.object.put(self.allocator, "body", try self.convertBlock(&node.body));
        return result;
    }

    pub fn convertForLoop(self: *AsmJsonConverter, node: *const AST.ForLoop) JsonError!JSON.Json {
        var result = try self.createAstNode(node.debug_data, "YulForLoop");
        try result.object.put(self.allocator, "pre", try self.convertBlock(&node.pre));
        try result.object.put(
            self.allocator,
            "condition",
            try self.convertExpression(node.condition orelse return error.InvalidAst),
        );
        try result.object.put(self.allocator, "post", try self.convertBlock(&node.post));
        try result.object.put(self.allocator, "body", try self.convertBlock(&node.body));
        return result;
    }

    pub fn convertExpression(self: *AsmJsonConverter, node: *const AST.Expression) JsonError!JSON.Json {
        return switch (node.*) {
            .function_call => |*value| self.convertFunctionCall(value),
            .identifier => |*value| self.convertIdentifier(value),
            .literal => |*value| self.convertLiteral(value),
        };
    }

    pub fn convertStatement(self: *AsmJsonConverter, node: *const AST.Statement) JsonError!JSON.Json {
        return switch (node.*) {
            .expression_statement => |*value| self.convertExpressionStatement(value),
            .assignment => |*value| self.convertAssignment(value),
            .variable_declaration => |*value| self.convertVariableDeclaration(value),
            .function_definition => |*value| self.convertFunctionDefinition(value),
            .if_statement => |*value| self.convertIf(value),
            .switch_statement => |*value| self.convertSwitch(value),
            .for_loop => |*value| self.convertForLoop(value),
            .break_statement => |*value| self.createAstNode(value.debug_data, "YulBreak"),
            .continue_statement => |*value| self.createAstNode(value.debug_data, "YulContinue"),
            .leave_statement => |*value| self.createAstNode(value.debug_data, "YulLeave"),
            .block => |*value| self.convertBlock(value),
        };
    }

    fn convertFunctionName(
        self: *AsmJsonConverter,
        node: *const AST.FunctionName,
    ) JsonError!JSON.Json {
        return switch (node.*) {
            .identifier => |*value| self.convertIdentifier(value),
            .builtin => |*value| self.convertBuiltinName(value),
        };
    }

    fn createAstNode(
        self: *AsmJsonConverter,
        debug_data: ?DebugData,
        node_type: []const u8,
    ) JsonError!JSON.Json {
        var result: JSON.Json = .{ .object = .empty };
        const origin_location = if (debug_data) |debug| debug.origin_location else SourceLocation{};
        const native_location = if (debug_data) |debug| debug.native_location else SourceLocation{};
        try result.object.put(self.allocator, "nodeType", try self.ownedString(node_type));
        try result.object.put(
            self.allocator,
            "src",
            try self.locationString(origin_location),
        );
        try result.object.put(
            self.allocator,
            "nativeSrc",
            try self.locationString(native_location),
        );
        return result;
    }

    fn locationString(self: *AsmJsonConverter, location: SourceLocation) JsonError!JSON.Json {
        const length: i64 = if (location.start >= 0 and
            location.end >= 0 and location.end >= location.start)
            @as(i64, location.end) - @as(i64, location.start)
        else
            -1;
        const source_index = if (self.source_index) |index|
            try std.fmt.allocPrint(self.allocator, "{d}", .{index})
        else
            try self.allocator.dupe(u8, "-1");
        const value = try std.fmt.allocPrint(
            self.allocator,
            "{d}:{d}:{s}",
            .{ location.start, length, source_index },
        );
        return .{ .string = value };
    }

    fn ownedString(self: *AsmJsonConverter, value: []const u8) JsonError!JSON.Json {
        return .{ .string = try self.allocator.dupe(u8, value) };
    }
};

test "Yul AST JSON owns its arena and preserves compatibility fields" {
    const Parser = @import("asm_parser.zig").Parser;
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x := 1 switch x case 1 { break } default { leave } }",
        "input.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var json = try AsmJsonConverter.convertAlloc(allocator, &ast, 0);
    defer json.deinit();
    const encoded = try JSON.jsonCompactPrintAlloc(allocator, json.rootConst());
    defer allocator.free(encoded);
    try std.testing.expect(std.mem.find(u8, encoded, "\"nodeType\":\"YulBlock\"") != null);
    try std.testing.expect(std.mem.find(u8, encoded, "\"nativeSrc\"") != null);
    try std.testing.expect(std.mem.find(u8, encoded, "\"type\":\"\"") != null);
}
