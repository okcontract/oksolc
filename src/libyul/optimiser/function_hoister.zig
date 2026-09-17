// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Hoists every nested function definition to the outermost Yul block.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimizerUtilities = @import("optimizer_utilities.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const FunctionHoister = struct {
    allocator: std.mem.Allocator,
    functions: std.ArrayList(AST.Statement) = .empty,

    pub const name = "FunctionHoister";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) !void {
        try apply(context.dispenser.allocator, ast);
    }

    pub fn apply(allocator: std.mem.Allocator, ast: *AST.Block) !void {
        var hoister: FunctionHoister = .{ .allocator = allocator };
        errdefer hoister.deinitOwnedFunctions();
        try hoister.visitBlock(ast, true);
        hoister.functions.deinit(allocator);
        hoister.functions = .empty;
    }

    fn deinitOwnedFunctions(self: *FunctionHoister) void {
        for (self.functions.items) |*statement| statement.deinit(self.allocator);
        self.functions.deinit(self.allocator);
        self.functions = .empty;
    }

    fn visitBlock(self: *FunctionHoister, block: *AST.Block, top_level: bool) anyerror!void {
        for (block.statements.items) |*statement| {
            try self.visitStatement(statement);
            if (statement.* == .function_definition) {
                try self.functions.append(self.allocator, statement.*);
                statement.* = emptyStatement();
            }
        }
        OptimizerUtilities.removeEmptyBlocks(self.allocator, block);
        if (top_level) {
            try block.statements.ensureUnusedCapacity(self.allocator, self.functions.items.len);
            for (self.functions.items) |*function| {
                block.statements.appendAssumeCapacity(function.*);
                function.* = emptyStatement();
            }
            self.functions.deinit(self.allocator);
            self.functions = .empty;
        }
    }

    fn visitStatement(self: *FunctionHoister, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .function_definition => |*value| try self.visitBlock(&value.body, false),
            .if_statement => |*value| try self.visitBlock(&value.body, false),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body, false),
            .for_loop => |*value| {
                try self.visitBlock(&value.pre, false);
                try self.visitBlock(&value.post, false);
                try self.visitBlock(&value.body, false);
            },
            .block => |*value| try self.visitBlock(value, false),
            else => {},
        }
    }
};

fn emptyStatement() AST.Statement {
    return .{ .block = .{} };
}

test "function hoister moves nested definitions after outer code" {
    const allocator = std.testing.allocator;
    var nested: AST.Block = .{};
    try nested.statements.append(allocator, .{ .function_definition = .{} });
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    try root.statements.append(allocator, .{ .block = nested });
    try FunctionHoister.apply(allocator, &root);
    try std.testing.expectEqual(@as(usize, 1), root.statements.items.len);
    try std.testing.expect(root.statements.items[0] == .function_definition);
}
