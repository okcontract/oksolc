// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reconstructs movable loop conditions from a leading conditional break.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");

pub const ForLoopConditionOutOfBody = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,

    pub const name = "ForLoopConditionOutOfBody";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var pass: ForLoopConditionOutOfBody = .{
            .allocator = context.dispenser.allocator,
            .dialect = context.dialect,
        };
        try pass.visitBlock(ast);
    }

    fn visitBlock(self: *ForLoopConditionOutOfBody, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *ForLoopConditionOutOfBody, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| try self.visitForLoop(value),
            .block => |*value| try self.visitBlock(value),
            else => {},
        }
    }

    fn visitForLoop(self: *ForLoopConditionOutOfBody, loop: *AST.ForLoop) anyerror!void {
        try self.visitBlock(&loop.pre);
        try self.visitBlock(&loop.post);
        try self.visitBlock(&loop.body);

        const iszero = self.dialect.booleanNegationFunctionHandle() orelse return;
        const loop_condition = loop.condition orelse return error.InvalidAst;
        const loop_value = switch (loop_condition.*) {
            .literal => |*literal| try literal.value.value(),
            else => return,
        };
        if (loop_value == 0 or loop.body.statements.items.len == 0) return;
        const first_statement = &loop.body.statements.items[0];
        if (first_statement.* != .if_statement) return;
        const first_if = &first_statement.if_statement;
        if (first_if.body.statements.items.len == 0 or
            first_if.body.statements.items[0] != .break_statement)
        {
            return;
        }
        const first_condition = first_if.condition orelse return error.InvalidAst;
        const effects = try Semantics.SideEffectsCollector.collectExpression(
            self.dialect,
            first_condition,
            null,
        );
        if (!effects.movable()) return;

        const replacement = try self.takeReplacementCondition(first_if, iszero);
        loop_condition.deinit(self.allocator);
        self.allocator.destroy(loop_condition);
        loop.condition = replacement;
        var removed = loop.body.statements.orderedRemove(0);
        removed.deinit(self.allocator);
    }

    fn takeReplacementCondition(
        self: *ForLoopConditionOutOfBody,
        first_if: *AST.If,
        iszero: @import("../builtins.zig").BuiltinHandle,
    ) anyerror!*AST.Expression {
        const condition = first_if.condition orelse return error.InvalidAst;
        if (condition.* == .function_call and
            condition.function_call.function_name == .builtin and
            condition.function_call.function_name.builtin.handle.eql(iszero))
        {
            if (condition.function_call.arguments.items.len == 0) return error.InvalidAst;
            var argument = condition.function_call.arguments.orderedRemove(0);
            errdefer argument.deinit(self.allocator);
            return try AST.createExpression(self.allocator, argument);
        }

        var arguments: std.ArrayList(AST.Expression) = .empty;
        errdefer {
            for (arguments.items) |*argument| argument.deinit(self.allocator);
            arguments.deinit(self.allocator);
        }
        try arguments.ensureTotalCapacity(self.allocator, 1);
        const moved = condition.*;
        const debug_data = switch (moved) {
            .function_call => |value| value.debug_data,
            .identifier => |value| value.debug_data,
            .literal => |value| value.debug_data,
        };
        first_if.condition = null;
        self.allocator.destroy(condition);
        arguments.appendAssumeCapacity(moved);
        const replacement = try AST.createExpression(self.allocator, .{ .function_call = .{
            .debug_data = debug_data,
            .function_name = .{ .builtin = .{
                .debug_data = debug_data,
                .handle = iszero,
            } },
            .arguments = arguments,
        } });
        arguments = .empty;
        return replacement;
    }
};
