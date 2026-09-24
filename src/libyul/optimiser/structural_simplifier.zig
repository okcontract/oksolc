// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Literal-driven simplification of Yul control-flow structure.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const StructuralSimplifier = struct {
    pub const name = "StructuralSimplifier";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        try apply(context.dispenser.allocator, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, ast: *AST.Block) anyerror!void {
        try simplify(allocator, &ast.statements);
    }
};

fn simplify(allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) anyerror!void {
    var index: usize = 0;
    while (index < statements.items.len) {
        if (try replacementFor(allocator, &statements.items[index])) |*replacement| {
            var owned = replacement.*;
            defer {
                // The source block no longer owns these detached statements.
                // Successful insertion clears the list; errors destroy payloads.
                for (owned.items) |*statement| statement.deinit(allocator);
                owned.deinit(allocator);
            }
            try simplify(allocator, &owned);
            try statements.ensureUnusedCapacity(allocator, owned.items.len);
            var removed = statements.orderedRemove(index);
            removed.deinit(allocator);
            statements.insertSliceAssumeCapacity(index, owned.items);
            const inserted = owned.items.len;
            owned.clearRetainingCapacity();
            index += inserted;
        } else {
            try visitStatement(allocator, &statements.items[index]);
            index += 1;
        }
    }
}

fn replacementFor(
    allocator: std.mem.Allocator,
    statement: *AST.Statement,
) anyerror!?std.ArrayList(AST.Statement) {
    return switch (statement.*) {
        .if_statement => |*if_statement| blk: {
            const value = try literalValue(if_statement.condition orelse return error.InvalidAst) orelse break :blk null;
            if (value == 0) break :blk std.ArrayList(AST.Statement).empty;
            break :blk takeStatements(&if_statement.body);
        },
        .switch_statement => |*switch_statement| blk: {
            const value = try literalValue(switch_statement.expression orelse return error.InvalidAst) orelse break :blk null;
            var matching: ?*AST.Block = null;
            var default: ?*AST.Block = null;
            for (switch_statement.cases.items) |*case_value| {
                if (case_value.value) |literal| {
                    if (try literal.value.value() == value) {
                        matching = &case_value.body;
                        break;
                    }
                } else {
                    default = &case_value.body;
                }
            }
            if (matching orelse default) |block| break :blk try takeBlockStatement(allocator, block);
            break :blk std.ArrayList(AST.Statement).empty;
        },
        .for_loop => |*loop| blk: {
            const value = try literalValue(loop.condition orelse return error.InvalidAst) orelse break :blk null;
            if (value != 0) break :blk null;
            break :blk takeStatements(&loop.pre);
        },
        else => null,
    };
}

fn literalValue(expression: *const AST.Expression) anyerror!?u256 {
    return switch (expression.*) {
        .literal => |*literal| try literal.value.value(),
        else => null,
    };
}

fn takeStatements(block: *AST.Block) std.ArrayList(AST.Statement) {
    const statements = block.statements;
    block.statements = .empty;
    return statements;
}

fn takeBlockStatement(
    allocator: std.mem.Allocator,
    block: *AST.Block,
) !std.ArrayList(AST.Statement) {
    var result: std.ArrayList(AST.Statement) = .empty;
    errdefer result.deinit(allocator);
    try result.ensureTotalCapacity(allocator, 1);
    const moved = block.*;
    block.* = .{};
    result.appendAssumeCapacity(.{ .block = moved });
    return result;
}

fn visitStatement(allocator: std.mem.Allocator, statement: *AST.Statement) anyerror!void {
    switch (statement.*) {
        .function_definition => |*value| try simplify(allocator, &value.body.statements),
        .if_statement => |*value| try simplify(allocator, &value.body.statements),
        .switch_statement => |*value| for (value.cases.items) |*case_value|
            try simplify(allocator, &case_value.body.statements),
        .for_loop => |*value| {
            try simplify(allocator, &value.pre.statements);
            try simplify(allocator, &value.body.statements);
            try simplify(allocator, &value.post.statements);
        },
        .block => |*value| try simplify(allocator, &value.statements),
        else => {},
    }
}

test "structural simplifier removes a literal-false if" {
    const allocator = std.testing.allocator;
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .if_statement = .{
        .condition = try AST.createExpression(allocator, .{ .literal = .{
            .kind = .Number,
            .value = try AST.LiteralValue.initNumeric(allocator, 0, null),
        } }),
        .body = .{},
    } });
    try StructuralSimplifier.apply(allocator, &root);
    try std.testing.expectEqual(@as(usize, 0), root.statements.items.len);
}
