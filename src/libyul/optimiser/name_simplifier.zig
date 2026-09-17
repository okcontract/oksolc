// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Simplifies compiler-generated identifier spellings without introducing
//! collisions, reserved words, or dialect builtins.

const std = @import("std");
const AST = @import("../ast.zig");
const NameCollector = @import("name_collector.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const YulName = @import("../yul_name.zig").YulName;

pub const NameSimplifier = struct {
    allocator: std.mem.Allocator,
    context: *OptimiserStepContext,
    translations: std.AutoHashMap(YulName, YulName),

    pub const name = "NameSimplifier";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        var simplifier: NameSimplifier = .{
            .allocator = allocator,
            .context = context,
            .translations = std.AutoHashMap(YulName, YulName).init(allocator),
        };
        defer simplifier.deinit();
        for (0..context.reserved_identifiers.len()) |index| {
            const reserved = context.reserved_identifiers.at(index);
            try simplifier.translations.put(reserved, reserved);
        }
        var names = try NameCollector.NameCollector.initBlock(
            allocator,
            ast,
            .variables_and_functions,
        );
        defer names.deinit();
        for (0..names.names().len()) |index|
            try simplifier.findSimplification(names.names().at(index));
        try simplifier.visitBlock(ast);
    }

    fn deinit(self: *NameSimplifier) void {
        self.translations.deinit();
        self.* = undefined;
    }

    fn findSimplification(self: *NameSimplifier, original: YulName) anyerror!void {
        if (self.translations.contains(original)) return;
        var current = try self.allocator.dupe(u8, try original.str());
        defer self.allocator.free(current);
        for (0..17) |step| {
            const candidate = try simplifyStep(self.allocator, current, step);
            if (candidate.len != 0) {
                const candidate_name = try YulName.init(candidate);
                if (!try self.context.dispenser.illegalName(candidate_name)) {
                    self.allocator.free(current);
                    current = candidate;
                    continue;
                }
            }
            self.allocator.free(candidate);
        }
        if (!std.mem.eql(u8, current, try original.str())) {
            const translated = try YulName.init(current);
            try self.context.dispenser.markUsed(translated);
            try self.translations.put(original, translated);
        }
    }

    fn translate(self: *const NameSimplifier, name_value: *YulName) void {
        if (self.translations.get(name_value.*)) |translated| name_value.* = translated;
    }

    fn visitBlock(self: *NameSimplifier, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *NameSimplifier, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| {
                for (value.variable_names.items) |*identifier| self.translate(&identifier.name);
                try self.visitExpression(value.value orelse return error.InvalidAst);
            },
            .variable_declaration => |*value| {
                for (value.variables.items) |*variable| self.translate(&variable.name);
                if (value.value) |expression| try self.visitExpression(expression);
            },
            .function_definition => |*value| {
                self.translate(&value.name);
                for (value.parameters.items) |*parameter| self.translate(&parameter.name);
                for (value.return_variables.items) |*variable| self.translate(&variable.name);
                try self.visitBlock(&value.body);
            },
            .if_statement => |*value| {
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                try self.visitExpression(value.expression orelse return error.InvalidAst);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *NameSimplifier, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .identifier => |*identifier| self.translate(&identifier.name),
            .literal => {},
            .function_call => |*call| {
                if (call.function_name == .identifier)
                    self.translate(&call.function_name.identifier.name);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
        }
    }
};

fn simplifyStep(allocator: std.mem.Allocator, input: []const u8, step: usize) ![]u8 {
    return switch (step) {
        0 => replaceMangleDelimiters(allocator, input),
        1 => removeNumericIdsBeforeNonHex(allocator, input),
        2 => removeTrailingNumericId(allocator, input),
        3 => replaceAll(allocator, input, "_t_", "_"),
        4 => replaceAll(allocator, input, "__", "_"),
        5 => shortenAbiName(allocator, input),
        6 => shortenStringLiteral(allocator, input),
        7 => replaceAll(allocator, input, "tuple_", ""),
        8 => replaceAll(allocator, input, "_memory_ptr", ""),
        9 => replaceAll(allocator, input, "_calldata_ptr", "_calldata"),
        10 => replaceAll(allocator, input, "_fromStack", ""),
        11 => replaceAll(allocator, input, "_storage_storage", "_storage"),
        12 => removeLastStorageWord(allocator, input),
        13 => replaceAll(allocator, input, "_memory_memory", "_memory"),
        14 => removeContractMangle(allocator, input),
        15 => replaceIndexAccessArray(allocator, input),
        16 => removeTrailingDigitsUnderscore(allocator, input),
        else => unreachable,
    };
}

fn replaceAll(
    allocator: std.mem.Allocator,
    input: []const u8,
    needle: []const u8,
    replacement: []const u8,
) ![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var offset: usize = 0;
    while (std.mem.findPos(u8, input, offset, needle)) |index| {
        try output.appendSlice(allocator, input[offset..index]);
        try output.appendSlice(allocator, replacement);
        offset = index + needle.len;
    }
    try output.appendSlice(allocator, input[offset..]);
    return output.toOwnedSlice(allocator);
}

fn replaceMangleDelimiters(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var index: usize = 0;
    while (index < input.len) {
        if (index + 1 < input.len and
            ((input[index] == '_' and input[index + 1] == '$') or
                (input[index] == '$' and input[index + 1] == '_')))
        {
            try output.append(allocator, '_');
            index += 2;
        } else {
            try output.append(allocator, input[index]);
            index += 1;
        }
    }
    return output.toOwnedSlice(allocator);
}

fn removeNumericIdsBeforeNonHex(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var index: usize = 0;
    while (index < input.len) {
        if (input[index] == '_' and index + 1 < input.len and std.ascii.isDigit(input[index + 1])) {
            var end = index + 1;
            while (end < input.len and std.ascii.isDigit(input[end])) end += 1;
            if (end < input.len and !std.ascii.isHex(input[end]) and input[end] != 'x') {
                try output.append(allocator, input[end]);
                index = end + 1;
                continue;
            }
        }
        try output.append(allocator, input[index]);
        index += 1;
    }
    return output.toOwnedSlice(allocator);
}

fn removeTrailingNumericId(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    var start = input.len;
    while (start > 0 and std.ascii.isDigit(input[start - 1])) start -= 1;
    if (start < input.len and start > 0 and input[start - 1] == '_') start -= 1 else start = input.len;
    return allocator.dupe(u8, input[0..start]);
}

fn shortenAbiName(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    var search: usize = 0;
    while (std.mem.findPos(u8, input, search, "abi_")) |start| {
        if (start + 10 <= input.len and std.mem.eql(u8, input[start + 6 .. start + 10], "code")) {
            if (std.mem.findLast(u8, input[start + 10 ..], "_to_")) |relative| {
                const end = start + 10 + relative;
                return allocator.dupe(u8, input[0..end]);
            }
        }
        search = start + 1;
    }
    return allocator.dupe(u8, input);
}

fn shortenStringLiteral(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    const marker = "stringliteral";
    const start = std.mem.find(u8, input, marker) orelse return allocator.dupe(u8, input);
    var digits_start = start + marker.len;
    if (digits_start < input.len and input[digits_start] == '_') digits_start += 1;
    if (digits_start + 4 > input.len) return allocator.dupe(u8, input);
    for (input[digits_start .. digits_start + 4]) |character|
        if (!isLowerHex(character)) return allocator.dupe(u8, input);
    var end = digits_start + 4;
    while (end < input.len and isLowerHex(input[end])) end += 1;
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.appendSlice(allocator, input[0 .. digits_start + 4]);
    try output.appendSlice(allocator, input[end..]);
    return output.toOwnedSlice(allocator);
}

fn removeLastStorageWord(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    const first = std.mem.find(u8, input, "storage") orelse return allocator.dupe(u8, input);
    const remaining = input[first + "storage".len ..];
    const relative_last = std.mem.findLast(u8, remaining, "storage") orelse
        return allocator.dupe(u8, input);
    const last = first + "storage".len + relative_last;
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.appendSlice(allocator, input[0..last]);
    try output.appendSlice(allocator, input[last + "storage".len ..]);
    return output.toOwnedSlice(allocator);
}

fn removeContractMangle(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    const marker = "_contract$_";
    const start = std.mem.find(u8, input, marker) orelse return allocator.dupe(u8, input);
    const capture_start = start + marker.len;
    var capture_end = capture_start;
    while (capture_end < input.len and input[capture_end] != '_') capture_end += 1;
    const consumed_end = if (capture_end < input.len) capture_end + 1 else capture_end;
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.appendSlice(allocator, input[0..start]);
    try output.appendSlice(allocator, input[capture_start..capture_end]);
    try output.append(allocator, '_');
    try output.appendSlice(allocator, input[consumed_end..]);
    return output.toOwnedSlice(allocator);
}

fn replaceIndexAccessArray(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    const result = try replaceAll(allocator, input, "index_access_t_array", "index_access");
    defer allocator.free(result);
    return replaceAll(allocator, result, "index_access_array", "index_access");
}

fn removeTrailingDigitsUnderscore(allocator: std.mem.Allocator, input: []const u8) ![]u8 {
    if (input.len == 0 or input[input.len - 1] != '_') return allocator.dupe(u8, input);
    var start = input.len - 1;
    while (start > 0 and std.ascii.isDigit(input[start - 1])) start -= 1;
    return allocator.dupe(u8, input[0..start]);
}

fn isLowerHex(character: u8) bool {
    return std.ascii.isDigit(character) or (character >= 'a' and character <= 'f');
}

test "name simplifier applies ordered generated-name rewrites" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let tuple_foo_memory_ptr_123 := 1 pop(tuple_foo_memory_ptr_123) }",
        "name-simplifier.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(
        allocator,
        dialect.dialect(),
        ast.root(),
        &reserved,
    );
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = dialect.dialect(),
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    try NameSimplifier.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "let foo := 1") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "pop(foo)") != null);
}
