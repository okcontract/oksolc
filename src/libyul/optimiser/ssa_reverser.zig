// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reorders SSA value declarations with their compatibility assignments.

const std = @import("std");
const AST = @import("../ast.zig");
const Metrics = @import("metrics.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const SSAReverser = struct {
    pub const name = "SSAReverser";
    pub const preserves_function_analysis = true;

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const allocator = context.dispenser.allocator;
        var counter = Metrics.AssignmentCounter.init(context.scratchAllocator());
        defer counter.deinit();
        try counter.run(ast);
        var reverser: Reverser = .{ .allocator = allocator, .assignment_counter = &counter };
        reverser.visitBlock(ast);
    }
};

const Reverser = struct {
    allocator: std.mem.Allocator,
    assignment_counter: *const Metrics.AssignmentCounter,

    fn visitBlock(self: *Reverser, block: *AST.Block) void {
        for (block.statements.items) |*statement| self.visitStatement(statement);

        var index: usize = 0;
        while (index + 1 < block.statements.items.len) {
            const replacement_size = self.reversePair(
                &block.statements.items[index],
                &block.statements.items[index + 1],
            );
            if (replacement_size) |size| {
                if (size == 1) {
                    var removed = block.statements.orderedRemove(index + 1);
                    removed.deinit(self.allocator);
                }
                index += size;
            } else {
                index += 1;
            }
        }
    }

    fn visitStatement(self: *Reverser, statement: *AST.Statement) void {
        switch (statement.*) {
            .function_definition => |*function| self.visitBlock(&function.body),
            .if_statement => |*if_statement| self.visitBlock(&if_statement.body),
            .switch_statement => |*switch_statement| for (switch_statement.cases.items) |*case_value|
                self.visitBlock(&case_value.body),
            .for_loop => |*loop| {
                self.visitBlock(&loop.pre);
                self.visitBlock(&loop.post);
                self.visitBlock(&loop.body);
            },
            .block => |*nested| self.visitBlock(nested),
            else => {},
        }
    }

    /// Returns the replacement width when a pair was transformed.
    fn reversePair(
        self: *Reverser,
        first: *AST.Statement,
        second: *AST.Statement,
    ) ?usize {
        if (first.* != .variable_declaration) return null;
        const first_declaration = &first.variable_declaration;
        if (first_declaration.variables.items.len != 1 or first_declaration.value == null) return null;
        const ssa_name = first_declaration.variables.items[0].name;

        switch (second.*) {
            .assignment => |*assignment| {
                if (assignment.variable_names.items.len != 1 or assignment.value == null or
                    assignment.value.?.* != .identifier or
                    !assignment.value.?.identifier.name.eql(ssa_name)) return null;

                const assigned_identifier = assignment.variable_names.items[0];
                if (assigned_identifier.name.eql(ssa_name)) return 1;

                // The matched identifier has no child owners. Reuse its box,
                // replacing its annotation with the assigned binding's data.
                const reverse_value = assignment.value.?;
                reverse_value.* = .{ .identifier = assigned_identifier };
                const first_debug_data = first_declaration.debug_data;
                const second_debug_data = assignment.debug_data;
                const original_value = first_declaration.value;
                const first_variables = first_declaration.variables;
                const assignment_variables = assignment.variable_names;
                first_declaration.value = null;
                first_declaration.variables = .empty;
                assignment.value = null;
                assignment.variable_names = .empty;
                first.* = .{ .assignment = .{
                    .debug_data = second_debug_data,
                    .variable_names = assignment_variables,
                    .value = original_value,
                } };
                second.* = .{ .variable_declaration = .{
                    .debug_data = first_debug_data,
                    .variables = first_variables,
                    .value = reverse_value,
                } };
                return 2;
            },
            .variable_declaration => |*second_declaration| {
                if (second_declaration.variables.items.len != 1 or second_declaration.value == null or
                    second_declaration.value.?.* != .identifier or
                    !second_declaration.value.?.identifier.name.eql(ssa_name)) return null;
                const second_name = second_declaration.variables.items[0];
                if (self.assignment_counter.assignmentCount(second_name.name) <=
                    self.assignment_counter.assignmentCount(ssa_name)) return null;

                const reverse_value = second_declaration.value.?;
                reverse_value.* = .{ .identifier = .{
                    .debug_data = second_name.debug_data,
                    .name = second_name.name,
                } };
                const first_debug_data = first_declaration.debug_data;
                const second_debug_data = second_declaration.debug_data;
                const original_value = first_declaration.value;
                const first_variables = first_declaration.variables;
                const second_variables = second_declaration.variables;
                first_declaration.value = null;
                first_declaration.variables = .empty;
                second_declaration.value = null;
                second_declaration.variables = .empty;
                first.* = .{ .variable_declaration = .{
                    .debug_data = second_debug_data,
                    .variables = second_variables,
                    .value = original_value,
                } };
                second.* = .{ .variable_declaration = .{
                    .debug_data = first_debug_data,
                    .variables = first_variables,
                    .value = reverse_value,
                } };
                return 2;
            },
            else => return null,
        }
    }
};

test "SSA reverser restores assignment-first form" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const NameCollector = @import("name_collector.zig");
    const NameDispenser = @import("name_dispenser.zig").NameDispenser;
    const Parser = @import("../asm_parser.zig").Parser;
    const Printer = @import("../asm_printer.zig").AsmPrinter;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(
        allocator,
        "{ let x_1 := 7 x := x_1 pop(x) }",
        "reverse.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer ast.deinit();
    var reserved: NameCollector.NameSet = .{};
    defer reserved.deinit(allocator);
    var dispenser = try NameDispenser.initFromAst(allocator, .{}, ast.root(), &reserved);
    defer dispenser.deinit();
    var context: OptimiserStepContext = .{
        .dialect = .{},
        .dispenser = &dispenser,
        .reserved_identifiers = &reserved,
    };
    try SSAReverser.run(&context, &ast.root_block);
    const rendered = try Printer.formatDefault(allocator, &ast);
    defer allocator.free(rendered);
    try std.testing.expect(std.mem.find(u8, rendered, "x := 7") != null);
    try std.testing.expect(std.mem.find(u8, rendered, "let x_1 := x") != null);
}

test "SSA reverser preserves pair decisions and complete annotations" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Converter = @import("../asm_json_converter.zig").AsmJsonConverter;
    const Encoding = @import("../ast_encoding.zig");
    const JSON = @import("../../libsolutil/json.zig");
    const cases = .{
        .{ "assignment", "{ let result := add(1, 2) target := result }", "f14693b9ef8eaa8adce033c4dab129309867d76484b5efd1e163e2ab18ec0832", "d7183e4eb144503a4b5c6fe98a99ec03d943e6cfe60755119e4ac0c888b7f334" },
        .{ "declaration", "{ let result := add(1, 2) let target := result target := 3 pop(target) }", "c84ff9d6a44c5b19ffcd467380a03873281a1b28331a4707edcc1bf051bbed69", "c9e82b47b5e4d84b0f0293b4e4ca2e0efac3e1fc0eaa585f5d12789a7eb10b2c" },
        .{ "self-copy", "{ let result := 1 result := result pop(result) }", "2b4295cf79eba90633f75b5783479c3800bcc5c6aa3a42d36febf7f9eab44616", "82764c304eff7c03a98c8f5586555be04b94568c52e46123d4701f5b5416cd5a" },
        .{ "no-match", "{ let result := 1 target := other }", "1a7270da31e30d8ccd659226fc328b703fa28f4d7a64d1849e8c180a8878fe35", "d1a34a70825a2884a43e5ae424cb9e22e0b1d6568b92fac31f71e86cb913ee58" },
        .{ "equal-counts", "{ let result := 1 let target := result pop(target) }", "fefb78e16cefd16d59c0ba55a597e3ba84757476852b8457f68817cfd907f10b", "13b3b7c2c4714fc80a14878ef936d4769b412e0924df2c16888163a1d58ee554" },
    };
    inline for (cases) |case| {
        const allocator = std.testing.allocator;
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, case[1], "ssa-reversal.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        const first = &ast.root_block.statements.items[0].variable_declaration;
        first.debug_data.?.ast_id = 41;
        first.variables.items[0].debug_data.?.ast_id = 53;
        const original_value = first.value.?;
        switch (original_value.*) {
            inline else => |*value| value.debug_data.?.ast_id = 71,
        }
        switch (ast.root_block.statements.items[1]) {
            .assignment => |*second| {
                second.debug_data.?.ast_id = 83;
                second.variable_names.items[0].debug_data = .{ .ast_id = 97 };
                second.value.?.identifier.debug_data = .{ .ast_id = 109 };
            },
            .variable_declaration => |*second| {
                second.debug_data.?.ast_id = 83;
                second.variables.items[0].debug_data = .{ .ast_id = 97 };
                second.value.?.identifier.debug_data = .{ .ast_id = 109 };
            },
            else => unreachable,
        }
        var counter = Metrics.AssignmentCounter.init(allocator);
        defer counter.deinit();
        try counter.run(ast.root());
        const second_value = switch (ast.root().statements.items[1]) {
            .assignment => |value| value.value.?,
            .variable_declaration => |value| value.value.?,
            else => unreachable,
        };
        const binding_debug = switch (ast.root().statements.items[1]) {
            .assignment => |value| value.variable_names.items[0].debug_data,
            .variable_declaration => |value| value.variables.items[0].debug_data,
            else => unreachable,
        };
        var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
        var pass: Reverser = .{ .allocator = rejecting.allocator(), .assignment_counter = &counter };
        pass.visitBlock(&ast.root_block);
        try std.testing.expect(!rejecting.has_induced_failure);
        if (comptime std.mem.eql(u8, case[0], "assignment") or std.mem.eql(u8, case[0], "declaration")) {
            const reused = ast.root().statements.items[1].variable_declaration.value.?;
            try std.testing.expect(reused == second_value);
            try std.testing.expectEqualDeep(binding_debug, reused.identifier.debug_data);
        }
        const retained_value = switch (ast.root().statements.items[0]) {
            .assignment => |value| value.value.?,
            .variable_declaration => |value| value.value.?,
            else => unreachable,
        };
        try std.testing.expect(original_value == retained_value);
        var json = try Converter.convertAlloc(allocator, &ast, 7);
        defer json.deinit();
        const bytes = try JSON.jsonCompactPrintAlloc(allocator, &json.value);
        defer allocator.free(bytes);
        var digest: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(bytes, &digest, .{});
        const encoded = std.fmt.bytesToHex(digest, .lower);
        const canonical = (try Encoding.hashBlock(ast.root())).hex();
        try std.testing.expectEqualStrings(case[2], &encoded);
        try std.testing.expectEqualStrings(case[3], &canonical);
    }
}

test "SSA reverser leaves missing values and multi-value pairs unchanged" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const Encoding = @import("../ast_encoding.zig");
    const allocator = std.testing.allocator;
    const cases = .{
        "{ let result target := result }",
        "{ let a, b := pair() target := a }",
        "{ let result := 1 x, y := result }",
        "{ let result := 1 let x, y := pair() }",
        "{ let result := 1 let target target := 2 }",
    };
    inline for (cases) |source| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, source, "reverse-guards.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        const hash = try Encoding.hashBlock(ast.root());
        var counter = Metrics.AssignmentCounter.init(allocator);
        defer counter.deinit();
        try counter.run(ast.root());
        var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
        var pass: Reverser = .{ .allocator = rejecting.allocator(), .assignment_counter = &counter };
        pass.visitBlock(&ast.root_block);
        try std.testing.expect(!rejecting.has_induced_failure);
        try std.testing.expectEqualDeep(hash, try Encoding.hashBlock(ast.root()));
    }
}

test "SSA reverser replaces every annotation field on the reused identifier" {
    const DebugData = @import("../../liblangutil/debug_data.zig").DebugData;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    const sources = .{
        "{ let result := 1 target := result }",
        "{ let result := 1 let target := result target := 2 }",
    };
    const binding_debug: DebugData = .{
        .native_location = .{ .start = 3, .end = 8, .source_name = "binding.yul" },
        .origin_location = .{ .start = 20, .end = 25, .source_name = "original.sol" },
        .ast_id = 97,
    };
    const discarded_debug: DebugData = .{
        .native_location = .{ .start = 1, .end = 3, .source_name = "rhs.yul" },
        .origin_location = .{ .start = 99, .end = 102, .source_name = "different.sol" },
        .ast_id = 109,
    };
    inline for (sources) |source| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var ast = (try Parser.parseSource(allocator, source, "annotation-owner.yul", &reporter, .{}, .{})).?;
        defer ast.deinit();
        const reused = switch (ast.root_block.statements.items[1]) {
            .assignment => |*value| blk: {
                value.variable_names.items[0].debug_data = binding_debug;
                break :blk value.value.?;
            },
            .variable_declaration => |*value| blk: {
                value.variables.items[0].debug_data = binding_debug;
                break :blk value.value.?;
            },
            else => unreachable,
        };
        reused.identifier.debug_data = discarded_debug;
        var counter = Metrics.AssignmentCounter.init(allocator);
        defer counter.deinit();
        try counter.run(ast.root());
        var rejecting = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0, .resize_fail_index = 0 });
        var pass: Reverser = .{ .allocator = rejecting.allocator(), .assignment_counter = &counter };
        pass.visitBlock(&ast.root_block);
        try std.testing.expect(!rejecting.has_induced_failure);
        try std.testing.expect(reused == ast.root().statements.items[1].variable_declaration.value.?);
        try std.testing.expectEqualDeep(@as(?DebugData, binding_debug), reused.identifier.debug_data);
    }
}
