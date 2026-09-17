// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Moves non-trivial for-loop conditions into a leading guarded break.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const ForLoopConditionIntoBody = struct {
    pub const name = "ForLoopConditionIntoBody";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) !void {
        try apply(context.dispenser.allocator, context.dialect, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, dialect: AST.Dialect, ast: *AST.Block) !void {
        try visitBlock(allocator, dialect, ast);
    }

    fn visitBlock(allocator: std.mem.Allocator, dialect: AST.Dialect, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try visitStatement(allocator, dialect, statement);
    }

    fn visitStatement(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        statement: *AST.Statement,
    ) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try visitBlock(allocator, dialect, &value.body),
            .if_statement => |*value| try visitBlock(allocator, dialect, &value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try visitBlock(allocator, dialect, &case_value.body),
            .for_loop => |*value| try visitForLoop(allocator, dialect, value),
            .block => |*value| try visitBlock(allocator, dialect, value),
            else => {},
        }
    }

    fn visitForLoop(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        loop: *AST.ForLoop,
    ) anyerror!void {
        if (dialect.booleanNegationFunctionHandle()) |negation_handle| {
            if (loop.condition) |condition| switch (condition.*) {
                .literal, .identifier => {},
                .function_call => try rewriteCondition(allocator, loop, condition, negation_handle),
            };
        }

        try visitBlock(allocator, dialect, &loop.pre);
        try visitBlock(allocator, dialect, &loop.post);
        try visitBlock(allocator, dialect, &loop.body);
    }

    fn rewriteCondition(
        allocator: std.mem.Allocator,
        loop: *AST.ForLoop,
        condition: *AST.Expression,
        negation_handle: @import("../builtins.zig").BuiltinHandle,
    ) !void {
        const debug_data = if (condition.debugData()) |value| value.* else null;

        try loop.body.statements.ensureUnusedCapacity(allocator, 1);
        var arguments: std.ArrayList(AST.Expression) = .empty;
        errdefer arguments.deinit(allocator);
        try arguments.ensureTotalCapacity(allocator, 1);
        var break_body: AST.Block = .{ .debug_data = debug_data };
        errdefer break_body.deinit(allocator);
        try break_body.statements.ensureTotalCapacity(allocator, 1);
        const negated_condition = try allocator.create(AST.Expression);
        errdefer allocator.destroy(negated_condition);
        var true_literal: AST.Literal = .{
            .debug_data = debug_data,
            .kind = .Boolean,
            .value = try AST.LiteralValue.initNumeric(allocator, 1, null),
        };
        errdefer true_literal.deinit(allocator);
        const true_condition = try allocator.create(AST.Expression);
        errdefer allocator.destroy(true_condition);

        arguments.appendAssumeCapacity(condition.*);
        condition.* = undefined;
        allocator.destroy(condition);
        negated_condition.* = .{ .function_call = .{
            .debug_data = debug_data,
            .function_name = .{ .builtin = .{
                .debug_data = debug_data,
                .handle = negation_handle,
            } },
            .arguments = arguments,
        } };
        arguments = .empty;
        break_body.statements.appendAssumeCapacity(.{ .break_statement = .{} });
        loop.body.statements.insertAssumeCapacity(0, .{ .if_statement = .{
            .debug_data = debug_data,
            .condition = negated_condition,
            .body = break_body,
        } });
        break_body = .{};
        true_condition.* = .{ .literal = true_literal };
        true_literal = undefined;
        loop.condition = true_condition;
    }
};

test "for-loop condition rewriter inserts an iszero guard and true condition" {
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const YulName = @import("../yul_name.zig").YulName;
    const allocator = std.testing.allocator;
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    var call: AST.FunctionCall = .{
        .function_name = .{ .identifier = .{ .name = try YulName.init("condition") } },
    };
    const condition = try AST.createExpression(allocator, .{ .function_call = call });
    call = undefined;
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .for_loop = .{ .condition = condition } });
    try ForLoopConditionIntoBody.apply(allocator, dialect.dialect(), &root);
    const loop = &root.statements.items[0].for_loop;
    try std.testing.expect(loop.condition.?.* == .literal);
    try std.testing.expectEqual(@as(usize, 1), loop.body.statements.items.len);
    try std.testing.expect(loop.body.statements.items[0] == .if_statement);
}
