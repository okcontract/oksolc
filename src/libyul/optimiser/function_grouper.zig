// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Canonical grouping of executable statements before top-level functions.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const FunctionGrouper = struct {
    pub const name = "FunctionGrouper";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) !void {
        try apply(context.dispenser.allocator, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, block: *AST.Block) !void {
        if (alreadyGrouped(block)) return;

        var function_count: usize = 0;
        for (block.statements.items) |statement|
            if (statement == .function_definition) {
                function_count += 1;
            };
        const code_count = block.statements.items.len - function_count;

        var code_statements: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(allocator, &code_statements);
        try code_statements.ensureTotalCapacity(allocator, code_count);
        var functions: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(allocator, &functions);
        try functions.ensureTotalCapacity(allocator, function_count);
        var reordered: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(allocator, &reordered);
        try reordered.ensureTotalCapacity(allocator, function_count + 1);

        for (block.statements.items) |*statement| {
            if (statement.* == .function_definition)
                functions.appendAssumeCapacity(statement.*)
            else
                code_statements.appendAssumeCapacity(statement.*);
            statement.* = emptyStatement();
        }
        block.statements.deinit(allocator);
        block.statements = .empty;

        reordered.appendAssumeCapacity(.{ .block = .{
            .debug_data = block.debug_data,
            .statements = code_statements,
        } });
        code_statements = .empty;
        for (functions.items) |*function| {
            reordered.appendAssumeCapacity(function.*);
            function.* = emptyStatement();
        }
        functions.deinit(allocator);
        functions = .empty;
        block.statements = reordered;
        reordered = .empty;
    }

    pub fn alreadyGrouped(block: *const AST.Block) bool {
        if (block.statements.items.len == 0 or block.statements.items[0] != .block) return false;
        for (block.statements.items[1..]) |statement|
            if (statement != .function_definition) return false;
        return true;
    }
};

fn emptyStatement() AST.Statement {
    return .{ .block = .{} };
}

fn deinitStatements(allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

test "function grouper preserves order in one code block followed by functions" {
    const allocator = std.testing.allocator;
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .break_statement = .{} });
    try root.statements.append(allocator, .{ .function_definition = .{} });
    try root.statements.append(allocator, .{ .leave_statement = .{} });
    try FunctionGrouper.apply(allocator, &root);
    try std.testing.expect(FunctionGrouper.alreadyGrouped(&root));
    try std.testing.expectEqual(@as(usize, 2), root.statements.items[0].block.statements.items.len);
}
