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
        const old_len = block.statements.items.len;
        var expanded_len = old_len;
        for (block.statements.items) |*statement| {
            if (statement.* == .for_loop) {
                const loop = &statement.for_loop;
                try visitBlock(allocator, &loop.pre);
                try visitBlock(allocator, &loop.body);
                try visitBlock(allocator, &loop.post);
                expanded_len = std.math.add(usize, expanded_len, loop.pre.statements.items.len) catch return error.OutOfMemory;
                if (loop.pre.statements.items.len == 0 and loop.pre.statements.capacity != 0) {
                    loop.pre.statements.deinit(allocator);
                    loop.pre.statements = .empty;
                }
            } else {
                try visitChildren(allocator, statement);
            }
        }
        if (expanded_len == old_len) return;

        // Finish all fallible work before moving owners. Reacquire statement
        // pointers after growth; each destination is at or beyond its source,
        // so backwards expansion cannot overwrite an unread statement.
        try block.statements.ensureTotalCapacityPrecise(allocator, expanded_len);
        block.statements.items.len = expanded_len;
        var source_index = old_len;
        var destination_index = expanded_len;
        while (source_index != 0) {
            source_index -= 1;
            var statement = block.statements.items[source_index];
            block.statements.items[source_index] = emptyStatement();
            destination_index -= 1;
            if (statement == .for_loop) {
                var pre = statement.for_loop.pre.statements;
                statement.for_loop.pre.statements = .empty;
                block.statements.items[destination_index] = statement;
                destination_index -= pre.items.len;
                @memcpy(block.statements.items[destination_index..][0..pre.items.len], pre.items);
                // Payloads moved into the parent; only the old header is owned.
                pre.deinit(allocator);
            } else {
                block.statements.items[destination_index] = statement;
            }
        }
        std.debug.assert(destination_index == 0);
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
