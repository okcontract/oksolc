// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Initializes every Yul variable declaration and splits uninitialized tuples.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const VarDeclInitializer = struct {
    pub const name = "VarDeclInitializer";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) !void {
        try apply(context.dispenser.allocator, context.dialect, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, dialect: AST.Dialect, ast: *AST.Block) !void {
        try visitBlock(allocator, dialect, ast);
    }

    fn visitBlock(allocator: std.mem.Allocator, dialect: AST.Dialect, block: *AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try visitChildren(allocator, dialect, statement);

        var replacement_len: usize = 0;
        for (block.statements.items) |*statement| {
            if (statement.* == .variable_declaration and statement.variable_declaration.value == null)
                replacement_len += statement.variable_declaration.variables.items.len
            else
                replacement_len += 1;
        }
        var replacement: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(allocator, &replacement);
        try replacement.ensureTotalCapacity(allocator, replacement_len);

        for (block.statements.items) |*statement| {
            if (statement.* != .variable_declaration or statement.variable_declaration.value != null) {
                replacement.appendAssumeCapacity(statement.*);
                statement.* = emptyStatement();
                continue;
            }

            const declaration = &statement.variable_declaration;
            if (declaration.variables.items.len == 1) {
                const zero = try dialect.zeroLiteral(allocator);
                declaration.value = try AST.createExpression(allocator, .{ .literal = zero });
                replacement.appendAssumeCapacity(statement.*);
                statement.* = emptyStatement();
                continue;
            }

            for (declaration.variables.items, 0..) |variable, index| {
                var variables: AST.NameWithDebugDataList = .empty;
                errdefer variables.deinit(allocator);
                try variables.append(allocator, variable);
                const zero = try dialect.zeroLiteral(allocator);
                errdefer {
                    var owned_zero = zero;
                    owned_zero.deinit(allocator);
                }
                const value = try AST.createExpression(allocator, .{ .literal = zero });
                replacement.appendAssumeCapacity(.{ .variable_declaration = .{
                    .debug_data = if (index == 0) declaration.debug_data else null,
                    .variables = variables,
                    .value = value,
                } });
                variables = .empty;
            }
            declaration.variables.deinit(allocator);
            declaration.variables = .empty;
            statement.* = emptyStatement();
        }
        block.statements.deinit(allocator);
        block.statements = replacement;
        replacement = .empty;
    }

    fn visitChildren(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        statement: *AST.Statement,
    ) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try visitBlock(allocator, dialect, &value.body),
            .if_statement => |*value| try visitBlock(allocator, dialect, &value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try visitBlock(allocator, dialect, &case_value.body),
            .for_loop => |*value| {
                try visitBlock(allocator, dialect, &value.pre);
                try visitBlock(allocator, dialect, &value.post);
                try visitBlock(allocator, dialect, &value.body);
            },
            .block => |*value| try visitBlock(allocator, dialect, value),
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

test "variable declaration initializer splits tuples and supplies zero values" {
    const allocator = std.testing.allocator;
    const YulName = @import("../yul_name.zig").YulName;
    var declaration: AST.VariableDeclaration = .{};
    try declaration.variables.append(allocator, .{ .name = try YulName.init("a") });
    try declaration.variables.append(allocator, .{ .name = try YulName.init("b") });
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .variable_declaration = declaration });
    try VarDeclInitializer.apply(allocator, .{}, &root);
    try std.testing.expectEqual(@as(usize, 2), root.statements.items.len);
    for (root.statements.items) |statement|
        try std.testing.expect(statement.variable_declaration.value != null);
}
