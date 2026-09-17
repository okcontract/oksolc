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
        var counter = Metrics.AssignmentCounter.init(allocator);
        defer counter.deinit();
        try counter.run(ast);
        var reverser: Reverser = .{ .allocator = allocator, .assignment_counter = &counter };
        try reverser.visitBlock(ast);
    }
};

const Reverser = struct {
    allocator: std.mem.Allocator,
    assignment_counter: *const Metrics.AssignmentCounter,

    fn visitBlock(self: *Reverser, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);

        var index: usize = 0;
        while (index + 1 < block.statements.items.len) {
            const replacement_size = try self.reversePair(
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

    fn visitStatement(self: *Reverser, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*function| try self.visitBlock(&function.body),
            .if_statement => |*if_statement| try self.visitBlock(&if_statement.body),
            .switch_statement => |*switch_statement| for (switch_statement.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*loop| {
                try self.visitBlock(&loop.pre);
                try self.visitBlock(&loop.post);
                try self.visitBlock(&loop.body);
            },
            .block => |*nested| try self.visitBlock(nested),
            else => {},
        }
    }

    /// Returns the replacement width when a pair was transformed.
    fn reversePair(
        self: *Reverser,
        first: *AST.Statement,
        second: *AST.Statement,
    ) anyerror!?usize {
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

                const reverse_value = try AST.createExpression(self.allocator, .{ .identifier = assigned_identifier });
                const first_debug_data = first_declaration.debug_data;
                const second_debug_data = assignment.debug_data;
                const original_value = first_declaration.value;
                const first_variables = first_declaration.variables;
                const assignment_variables = assignment.variable_names;
                const discarded_value = assignment.value.?;
                first_declaration.value = null;
                first_declaration.variables = .empty;
                assignment.value = null;
                assignment.variable_names = .empty;
                discarded_value.deinit(self.allocator);
                self.allocator.destroy(discarded_value);
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

                const reverse_value = try AST.createExpression(self.allocator, .{ .identifier = .{
                    .debug_data = second_name.debug_data,
                    .name = second_name.name,
                } });
                const first_debug_data = first_declaration.debug_data;
                const second_debug_data = second_declaration.debug_data;
                const original_value = first_declaration.value;
                const first_variables = first_declaration.variables;
                const second_variables = second_declaration.variables;
                const discarded_value = second_declaration.value.?;
                first_declaration.value = null;
                first_declaration.variables = .empty;
                second_declaration.value = null;
                second_declaration.variables = .empty;
                discarded_value.deinit(self.allocator);
                self.allocator.destroy(discarded_value);
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
