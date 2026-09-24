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
    candidate_buffer: std.ArrayList(u8) = .empty,

    pub const name = "NameSimplifier";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.scratchAllocator();
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
        self.candidate_buffer.deinit(self.allocator);
        self.* = undefined;
    }

    fn findSimplification(self: *NameSimplifier, original: YulName) anyerror!void {
        if (self.translations.contains(original)) return;
        const spelling = try original.str();
        var current = spelling;
        // Every rewrite is non-growing. Reuse one pass-owned candidate buffer;
        // accepted spellings borrow the existing immutable intern repository,
        // so rejecting or overwriting a candidate cannot change the current name.
        try self.candidate_buffer.resize(self.allocator, spelling.len);
        for (0..17) |step| {
            const candidate = simplifyStep(self.candidate_buffer.items, current, step);
            if (candidate.len == 0 or std.mem.eql(u8, candidate, current)) continue;
            const candidate_name = try YulName.init(candidate);
            if (try self.context.dispenser.illegalName(candidate_name)) continue;
            current = try candidate_name.str();
        }
        if (!std.mem.eql(u8, current, spelling)) {
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

/// Returns a borrowed prefix of input or a spelling written into buffer. Except
/// for replaceAll's documented in-place case, input and buffer must not overlap.
fn simplifyStep(buffer: []u8, input: []const u8, step: usize) []const u8 {
    std.debug.assert(buffer.len >= input.len);
    return switch (step) {
        0 => replaceMangleDelimiters(buffer, input),
        1 => removeNumericIdsBeforeNonHex(buffer, input),
        2 => removeTrailingNumericId(buffer, input),
        3 => replaceAll(buffer, input, "_t_", "_"),
        4 => replaceAll(buffer, input, "__", "_"),
        5 => shortenAbiName(buffer, input),
        6 => shortenStringLiteral(buffer, input),
        7 => replaceAll(buffer, input, "tuple_", ""),
        8 => replaceAll(buffer, input, "_memory_ptr", ""),
        9 => replaceAll(buffer, input, "_calldata_ptr", "_calldata"),
        10 => replaceAll(buffer, input, "_fromStack", ""),
        11 => replaceAll(buffer, input, "_storage_storage", "_storage"),
        12 => removeLastStorageWord(buffer, input),
        13 => replaceAll(buffer, input, "_memory_memory", "_memory"),
        14 => removeContractMangle(buffer, input),
        15 => replaceIndexAccessArray(buffer, input),
        16 => removeTrailingDigitsUnderscore(buffer, input),
        else => unreachable,
    };
}

/// Also supports shrinking in place (used by the two index-access rewrites).
fn replaceAll(buffer: []u8, input: []const u8, needle: []const u8, replacement: []const u8) []const u8 {
    std.debug.assert(needle.len != 0 and replacement.len <= needle.len);
    std.debug.assert(buffer.len >= input.len);
    var match = std.mem.find(u8, input, needle) orelse return input;
    var read: usize = 0;
    var written: usize = 0;
    while (true) {
        const prefix = input[read..match];
        std.mem.copyForwards(u8, buffer[written..][0..prefix.len], prefix);
        written += prefix.len;
        std.mem.copyForwards(u8, buffer[written..][0..replacement.len], replacement);
        written += replacement.len;
        read = match + needle.len;
        match = std.mem.findPos(u8, input, read, needle) orelse break;
    }
    const suffix = input[read..];
    std.mem.copyForwards(u8, buffer[written..][0..suffix.len], suffix);
    return buffer[0 .. written + suffix.len];
}

fn replaceMangleDelimiters(buffer: []u8, input: []const u8) []const u8 {
    var output: std.ArrayList(u8) = .{ .items = buffer[0..0], .capacity = buffer.len };
    var index: usize = 0;
    while (index < input.len) {
        if (index + 1 < input.len and
            ((input[index] == '_' and input[index + 1] == '$') or
                (input[index] == '$' and input[index + 1] == '_')))
        {
            output.appendAssumeCapacity('_');
            index += 2;
        } else {
            output.appendAssumeCapacity(input[index]);
            index += 1;
        }
    }
    return output.items;
}

fn removeNumericIdsBeforeNonHex(buffer: []u8, input: []const u8) []const u8 {
    var output: std.ArrayList(u8) = .{ .items = buffer[0..0], .capacity = buffer.len };
    var index: usize = 0;
    while (index < input.len) {
        if (input[index] == '_' and index + 1 < input.len and std.ascii.isDigit(input[index + 1])) {
            var end = index + 1;
            while (end < input.len and std.ascii.isDigit(input[end])) end += 1;
            if (end < input.len and !std.ascii.isHex(input[end]) and input[end] != 'x') {
                output.appendAssumeCapacity(input[end]);
                index = end + 1;
                continue;
            }
        }
        output.appendAssumeCapacity(input[index]);
        index += 1;
    }
    return output.items;
}

fn removeTrailingNumericId(_: []u8, input: []const u8) []const u8 {
    var start = input.len;
    while (start > 0 and std.ascii.isDigit(input[start - 1])) start -= 1;
    if (start < input.len and start > 0 and input[start - 1] == '_') start -= 1 else start = input.len;
    return input[0..start];
}

fn shortenAbiName(_: []u8, input: []const u8) []const u8 {
    var search: usize = 0;
    while (std.mem.findPos(u8, input, search, "abi_")) |start| {
        if (start + 10 <= input.len and std.mem.eql(u8, input[start + 6 .. start + 10], "code")) {
            if (std.mem.findLast(u8, input[start + 10 ..], "_to_")) |relative| {
                const end = start + 10 + relative;
                return input[0..end];
            }
        }
        search = start + 1;
    }
    return input;
}

fn shortenStringLiteral(buffer: []u8, input: []const u8) []const u8 {
    const marker = "stringliteral";
    const start = std.mem.find(u8, input, marker) orelse return input;
    var digits_start = start + marker.len;
    if (digits_start < input.len and input[digits_start] == '_') digits_start += 1;
    if (digits_start + 4 > input.len) return input;
    for (input[digits_start .. digits_start + 4]) |character|
        if (!isLowerHex(character)) return input;
    var end = digits_start + 4;
    while (end < input.len and isLowerHex(input[end])) end += 1;
    var output: std.ArrayList(u8) = .{ .items = buffer[0..0], .capacity = buffer.len };
    output.appendSliceAssumeCapacity(input[0 .. digits_start + 4]);
    output.appendSliceAssumeCapacity(input[end..]);
    return output.items;
}

fn removeLastStorageWord(buffer: []u8, input: []const u8) []const u8 {
    const first = std.mem.find(u8, input, "storage") orelse return input;
    const remaining = input[first + "storage".len ..];
    const relative_last = std.mem.findLast(u8, remaining, "storage") orelse
        return input;
    const last = first + "storage".len + relative_last;
    var output: std.ArrayList(u8) = .{ .items = buffer[0..0], .capacity = buffer.len };
    output.appendSliceAssumeCapacity(input[0..last]);
    output.appendSliceAssumeCapacity(input[last + "storage".len ..]);
    return output.items;
}

fn removeContractMangle(buffer: []u8, input: []const u8) []const u8 {
    const marker = "_contract$_";
    const start = std.mem.find(u8, input, marker) orelse return input;
    const capture_start = start + marker.len;
    var capture_end = capture_start;
    while (capture_end < input.len and input[capture_end] != '_') capture_end += 1;
    const consumed_end = if (capture_end < input.len) capture_end + 1 else capture_end;
    var output: std.ArrayList(u8) = .{ .items = buffer[0..0], .capacity = buffer.len };
    output.appendSliceAssumeCapacity(input[0..start]);
    output.appendSliceAssumeCapacity(input[capture_start..capture_end]);
    output.appendAssumeCapacity('_');
    output.appendSliceAssumeCapacity(input[consumed_end..]);
    return output.items;
}

fn replaceIndexAccessArray(buffer: []u8, input: []const u8) []const u8 {
    const result = replaceAll(buffer, input, "index_access_t_array", "index_access");
    return replaceAll(buffer, result, "index_access_array", "index_access");
}

fn removeTrailingDigitsUnderscore(_: []u8, input: []const u8) []const u8 {
    if (input.len == 0 or input[input.len - 1] != '_') return input;
    var start = input.len - 1;
    while (start > 0 and std.ascii.isDigit(input[start - 1])) start -= 1;
    return input[0..start];
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
        "{ let tuple_foo_memory_ptr_123 := 1 pop(tuple_foo_memory_ptr_123) " ++
            "let bar := 2 let bar_123 := 3 let a_123 := 4 let tuple_add := 5 " ++
            "pop(bar) pop(bar_123) pop(a_123) pop(tuple_add) }",
        "name-simplifier.yul",
        &reporter,
        dialect.dialect(),
        .{},
    )).?;
    defer ast.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    _ = try reserved.insert(allocator, try YulName.init("a"));
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
    for ([_][]const u8{ "let bar_123 := 3", "let a_123 := 4", "let tuple_add := 5", "pop(bar_123)", "pop(a_123)", "pop(tuple_add)" }) |expected|
        try std.testing.expect(std.mem.find(u8, rendered, expected) != null);
}

test "name simplifier preserves rewrite boundaries and overlapping replacements" {
    const Case = struct { step: usize, input: []const u8, expected: []const u8 };
    const cases = [_]Case{
        .{ .step = 0, .input = "a_$_b$_c", .expected = "a__b_c" },
        .{ .step = 0, .input = "$_$", .expected = "_$" },
        .{ .step = 1, .input = "a_123g_4z", .expected = "agz" },
        .{ .step = 1, .input = "a_123f_4x_5A_6", .expected = "a_123f_4x_5A_6" },
        .{ .step = 2, .input = "foo_123", .expected = "foo" },
        .{ .step = 2, .input = "foo123", .expected = "foo123" },
        .{ .step = 2, .input = "_123", .expected = "" },
        .{ .step = 3, .input = "a_t_b_t_c", .expected = "a_b_c" },
        .{ .step = 4, .input = "____", .expected = "__" },
        .{ .step = 5, .input = "pre_abi_encode_x_to_y_to_z", .expected = "pre_abi_encode_x_to_y" },
        .{ .step = 5, .input = "abi_x_abi_decode_a_to_b", .expected = "abi_x_abi_decode_a" },
        .{ .step = 5, .input = "abi_encode_a", .expected = "abi_encode_a" },
        .{ .step = 6, .input = "stringliteral_0123abcdef_end", .expected = "stringliteral_0123_end" },
        .{ .step = 6, .input = "stringliteral0123fA", .expected = "stringliteral0123A" },
        .{ .step = 6, .input = "stringliteral_ABCDef", .expected = "stringliteral_ABCDef" },
        .{ .step = 6, .input = "stringliteral_123", .expected = "stringliteral_123" },
        .{ .step = 7, .input = "tuple_tuple_x", .expected = "x" },
        .{ .step = 8, .input = "x_memory_ptr_y", .expected = "x_y" },
        .{ .step = 9, .input = "x_calldata_ptr", .expected = "x_calldata" },
        .{ .step = 10, .input = "x_fromStack_fromStack", .expected = "x" },
        .{ .step = 11, .input = "x_storage_storage_storage", .expected = "x_storage_storage" },
        .{ .step = 12, .input = "storage_x_storage_y_storage_z", .expected = "storage_x_storage_y__z" },
        .{ .step = 12, .input = "x_storage_y", .expected = "x_storage_y" },
        .{ .step = 13, .input = "x_memory_memory_memory", .expected = "x_memory_memory" },
        .{ .step = 14, .input = "x_contract$_C_tail", .expected = "xC_tail" },
        .{ .step = 14, .input = "x_contract$_C", .expected = "xC_" },
        .{ .step = 14, .input = "_contract$_", .expected = "_" },
        .{ .step = 15, .input = "index_access_t_array_array", .expected = "index_access" },
        .{ .step = 15, .input = "index_access_array_array", .expected = "index_access_array" },
        .{ .step = 15, .input = "index_access_t_array_x_index_access_array", .expected = "index_access_x_index_access" },
        .{ .step = 16, .input = "foo123_", .expected = "foo" },
        .{ .step = 16, .input = "foo_", .expected = "foo" },
        .{ .step = 16, .input = "_", .expected = "" },
    };
    var buffer: [128]u8 = undefined;
    for (cases) |case| {
        const result = simplifyStep(&buffer, case.input, case.step);
        try std.testing.expectEqualStrings(case.expected, result);
        try std.testing.expect(result.len <= case.input.len);
    }
    for (0..17) |step| {
        try std.testing.expectEqualStrings("plain", simplifyStep(&buffer, "plain", step));
        try std.testing.expectEqualStrings("", simplifyStep(&buffer, "", step));
    }
}
