// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Removes nested block statements after the function-grouper canonical form.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const BlockFlattener = struct {
    pub const name = "BlockFlattener";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) !void {
        try apply(context.dispenser.allocator, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, ast: *AST.Block) !void {
        for (ast.statements.items) |*statement| switch (statement.*) {
            .block => |*block| try flattenBlock(allocator, block),
            .function_definition => |*function| try flattenBlock(allocator, &function.body),
            else => return error.FunctionGrouperRequired,
        };
    }

    pub fn flattenBlock(allocator: std.mem.Allocator, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try flattenChildren(allocator, statement);

        var expanded_len: usize = 0;
        for (block.statements.items) |*statement| switch (statement.*) {
            .block => |*child| expanded_len += child.statements.items.len,
            else => expanded_len += 1,
        };
        var replacement: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(allocator, &replacement);
        try replacement.ensureTotalCapacity(allocator, expanded_len);
        for (block.statements.items) |*statement| switch (statement.*) {
            .block => |*child| {
                for (child.statements.items) |*nested| {
                    replacement.appendAssumeCapacity(nested.*);
                    nested.* = emptyStatement();
                }
                child.statements.deinit(allocator);
                child.statements = .empty;
                statement.* = emptyStatement();
            },
            else => {
                replacement.appendAssumeCapacity(statement.*);
                statement.* = emptyStatement();
            },
        };
        block.statements.deinit(allocator);
        block.statements = replacement;
        replacement = .empty;
    }

    fn flattenChildren(allocator: std.mem.Allocator, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try flattenBlock(allocator, &value.body),
            .if_statement => |*value| try flattenBlock(allocator, &value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try flattenBlock(allocator, &case_value.body),
            .for_loop => |*value| {
                try flattenBlock(allocator, &value.pre);
                try flattenBlock(allocator, &value.post);
                try flattenBlock(allocator, &value.body);
            },
            .block => |*value| try flattenBlock(allocator, value),
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

test "block flattener recursively splices nested statements" {
    const allocator = std.testing.allocator;
    var inner: AST.Block = .{};
    try inner.statements.append(allocator, .{ .break_statement = .{} });
    var code: AST.Block = .{};
    try code.statements.append(allocator, .{ .block = inner });
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .block = code });
    try BlockFlattener.apply(allocator, &root);
    try std.testing.expectEqual(@as(usize, 1), root.statements.items[0].block.statements.items.len);
    try std.testing.expect(root.statements.items[0].block.statements.items[0] == .break_statement);
}
