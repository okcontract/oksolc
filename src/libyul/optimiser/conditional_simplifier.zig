// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Inserts condition-variable facts implied by terminating control flow.

const std = @import("std");
const AST = @import("../ast.zig");
const ControlFlowCollector = @import("../control_flow_side_effects_collector.zig").ControlFlowSideEffectsCollector;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");

pub const ConditionalSimplifier = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    function_side_effects: *const Semantics.NamedControlFlowSideEffects,

    pub const name = "ConditionalSimplifier";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var collector = try ControlFlowCollector.init(
            context.scratchAllocator(),
            context.dialect,
            ast,
        );
        defer collector.deinit();
        var named = try collector.functionSideEffectsNamed(context.scratchAllocator());
        defer named.deinit();
        var pass: ConditionalSimplifier = .{
            .allocator = context.dispenser.allocator,
            .dialect = context.dialect,
            .function_side_effects = &named,
        };
        try pass.visitBlock(ast);
    }

    fn visitBlock(self: *ConditionalSimplifier, block: *AST.Block) anyerror!void {
        var index: usize = 0;
        while (index < block.statements.items.len) {
            try self.visitStatement(&block.statements.items[index]);
            const statement = &block.statements.items[index];
            if (statement.* == .if_statement) {
                const if_statement = &statement.if_statement;
                const condition = if_statement.condition orelse return error.InvalidAst;
                if (condition.* == .identifier and if_statement.body.statements.items.len != 0) {
                    const finder = Semantics.TerminationFinder.init(
                        self.dialect,
                        self.function_side_effects,
                    );
                    const last = &if_statement.body.statements.items[
                        if_statement.body.statements.items.len - 1
                    ];
                    if (try finder.controlFlowKind(last) != .flow_out) {
                        var assignment = try self.zeroAssignment(
                            condition.identifier.name,
                            if_statement.debug_data,
                        );
                        errdefer assignment.deinit(self.allocator);
                        try block.statements.insert(self.allocator, index + 1, assignment);
                        index += 1;
                    }
                }
            }
            index += 1;
        }
    }

    fn visitStatement(self: *ConditionalSimplifier, statement: *AST.Statement) anyerror!void {
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

    fn visitSwitch(self: *ConditionalSimplifier, switch_statement: *AST.Switch) anyerror!void {
        const expression = switch_statement.expression orelse return error.InvalidAst;
        if (expression.* != .identifier) {
            for (switch_statement.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            return;
        }
        const condition_name = expression.identifier.name;
        for (switch_statement.cases.items) |*case_value| {
            if (case_value.value) |literal| {
                var variables: std.ArrayList(AST.Identifier) = .empty;
                errdefer variables.deinit(self.allocator);
                try variables.append(self.allocator, .{
                    .debug_data = case_value.body.debug_data,
                    .name = condition_name,
                });
                const value = value: {
                    var cloned_literal = try cloneLiteral(self.allocator, literal);
                    errdefer cloned_literal.deinit(self.allocator);
                    break :value try AST.createExpression(
                        self.allocator,
                        .{ .literal = cloned_literal },
                    );
                };
                errdefer {
                    value.deinit(self.allocator);
                    self.allocator.destroy(value);
                }
                try case_value.body.statements.insert(self.allocator, 0, .{ .assignment = .{
                    .debug_data = case_value.body.debug_data,
                    .variable_names = variables,
                    .value = value,
                } });
                variables = .empty;
            }
            try self.visitBlock(&case_value.body);
        }
    }

    fn zeroAssignment(
        self: *ConditionalSimplifier,
        condition_name: @import("../yul_name.zig").YulName,
        debug_data: ?@import("../../liblangutil/debug_data.zig").DebugData,
    ) anyerror!AST.Statement {
        var variables: std.ArrayList(AST.Identifier) = .empty;
        errdefer variables.deinit(self.allocator);
        try variables.append(self.allocator, .{ .debug_data = debug_data, .name = condition_name });
        var literal = try self.dialect.zeroLiteral(self.allocator);
        errdefer literal.deinit(self.allocator);
        const expression = try AST.createExpression(self.allocator, .{ .literal = literal });
        literal = undefined;
        return .{ .assignment = .{
            .debug_data = debug_data,
            .variable_names = variables,
            .value = expression,
        } };
    }
};

fn cloneLiteral(allocator: std.mem.Allocator, literal: *const AST.Literal) !AST.Literal {
    return .{
        .debug_data = literal.debug_data,
        .kind = literal.kind,
        .value = try literal.value.clone(allocator),
    };
}
