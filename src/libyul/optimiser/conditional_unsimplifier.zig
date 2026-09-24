// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Removes condition-variable facts inserted by ConditionalSimplifier.

const std = @import("std");
const AST = @import("../ast.zig");
const ControlFlowCollector = @import("../control_flow_side_effects_collector.zig").ControlFlowSideEffectsCollector;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");

pub const ConditionalUnsimplifier = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    function_side_effects: *const Semantics.NamedControlFlowSideEffects,

    pub const name = "ConditionalUnsimplifier";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var collector = try ControlFlowCollector.init(
            context.scratchAllocator(),
            context.dialect,
            ast,
        );
        defer collector.deinit();
        var named = try collector.functionSideEffectsNamed(context.scratchAllocator());
        defer named.deinit();
        var pass: ConditionalUnsimplifier = .{
            .allocator = context.dispenser.allocator,
            .dialect = context.dialect,
            .function_side_effects = &named,
        };
        try pass.visitBlock(ast);
    }

    fn visitBlock(self: *ConditionalUnsimplifier, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
        var index: usize = 0;
        while (index + 1 < block.statements.items.len) {
            const first = &block.statements.items[index];
            const second = &block.statements.items[index + 1];
            if (first.* == .if_statement and second.* == .assignment) {
                const if_statement = &first.if_statement;
                const condition = if_statement.condition orelse return error.InvalidAst;
                if (condition.* == .identifier and if_statement.body.statements.items.len != 0) {
                    const finder = Semantics.TerminationFinder.init(
                        self.dialect,
                        self.function_side_effects,
                    );
                    const last = &if_statement.body.statements.items[
                        if_statement.body.statements.items.len - 1
                    ];
                    if (try finder.controlFlowKind(last) != .flow_out and
                        try isZeroAssignment(&second.assignment, condition.identifier.name))
                    {
                        var removed = block.statements.orderedRemove(index + 1);
                        removed.deinit(self.allocator);
                        index += 1;
                        continue;
                    }
                }
            }
            index += 1;
        }
    }

    fn visitStatement(self: *ConditionalUnsimplifier, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| try self.visitSwitch(value),
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        }
    }

    fn visitSwitch(self: *ConditionalUnsimplifier, switch_statement: *AST.Switch) anyerror!void {
        const expression = switch_statement.expression orelse return error.InvalidAst;
        if (expression.* != .identifier) {
            for (switch_statement.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            return;
        }
        const condition_name = expression.identifier.name;
        for (switch_statement.cases.items) |*case_value| {
            if (case_value.value) |case_literal| {
                if (case_value.body.statements.items.len != 0) {
                    const first = &case_value.body.statements.items[0];
                    if (first.* == .assignment and
                        assignmentMatchesLiteral(&first.assignment, condition_name, case_literal))
                    {
                        var removed = case_value.body.statements.orderedRemove(0);
                        removed.deinit(self.allocator);
                    }
                }
            }
            try self.visitBlock(&case_value.body);
        }
    }
};

fn assignmentMatchesLiteral(
    assignment: *const AST.Assignment,
    name: @import("../yul_name.zig").YulName,
    expected: *const AST.Literal,
) bool {
    if (assignment.variable_names.items.len != 1 or
        !assignment.variable_names.items[0].name.eql(name) or
        assignment.value == null or assignment.value.?.* != .literal)
    {
        return false;
    }
    return assignment.value.?.literal.value.eql(&expected.value);
}

fn isZeroAssignment(
    assignment: *const AST.Assignment,
    name: @import("../yul_name.zig").YulName,
) anyerror!bool {
    if (assignment.variable_names.items.len != 1 or
        !assignment.variable_names.items[0].name.eql(name) or
        assignment.value == null or assignment.value.?.* != .literal)
    {
        return false;
    }
    return try assignment.value.?.literal.value.value() == 0;
}
