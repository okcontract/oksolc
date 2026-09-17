// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Moves each Yul for-loop initialization block immediately before the loop.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const ForLoopInitRewriter = struct {
    pub const name = "ForLoopInitRewriter";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) !void {
        try apply(context.dispenser.allocator, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, ast: *AST.Block) !void {
        try visitBlock(allocator, ast);
    }

    fn visitBlock(allocator: std.mem.Allocator, block: *AST.Block) anyerror!void {
        var replacement: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(allocator, &replacement);
        try replacement.ensureTotalCapacity(allocator, block.statements.items.len);

        for (block.statements.items) |*statement| {
            if (statement.* == .for_loop) {
                const loop = &statement.for_loop;
                try visitBlock(allocator, &loop.pre);
                try visitBlock(allocator, &loop.body);
                try visitBlock(allocator, &loop.post);
                try replacement.ensureUnusedCapacity(allocator, loop.pre.statements.items.len + 1);
                for (loop.pre.statements.items) |*pre_statement| {
                    replacement.appendAssumeCapacity(pre_statement.*);
                    pre_statement.* = emptyStatement();
                }
                loop.pre.statements.deinit(allocator);
                loop.pre.statements = .empty;
                replacement.appendAssumeCapacity(statement.*);
                statement.* = emptyStatement();
            } else {
                try visitChildren(allocator, statement);
                try replacement.append(allocator, statement.*);
                statement.* = emptyStatement();
            }
        }
        block.statements.deinit(allocator);
        block.statements = replacement;
        replacement = .empty;
    }

    fn visitChildren(allocator: std.mem.Allocator, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try visitBlock(allocator, &value.body),
            .if_statement => |*value| try visitBlock(allocator, &value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try visitBlock(allocator, &case_value.body),
            .block => |*value| try visitBlock(allocator, value),
            else => {},
        }
    }
};

fn emptyStatement() AST.Statement {
    return .{ .block = .{} };
}

fn deinitStatements(allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

test "for-loop init rewriter empties pre and preserves its order before the loop" {
    const allocator = std.testing.allocator;
    var loop: AST.ForLoop = .{};
    try loop.pre.statements.append(allocator, .{ .break_statement = .{} });
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .for_loop = loop });
    try ForLoopInitRewriter.apply(allocator, &root);
    try std.testing.expectEqual(@as(usize, 2), root.statements.items.len);
    try std.testing.expect(root.statements.items[0] == .break_statement);
    try std.testing.expectEqual(@as(usize, 0), root.statements.items[1].for_loop.pre.statements.items.len);
}
