// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Outlines complex Yul expression arguments into temporary declarations.

const std = @import("std");
const AST = @import("../ast.zig");
const NameDispenser = @import("name_dispenser.zig").NameDispenser;
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Utilities = @import("../utilities.zig");

pub const ExpressionSplitter = struct {
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    dispenser: *NameDispenser,
    // Scratch owns the slots; allocator owns their pending AST payloads.
    statements_to_prefix: std.ArrayList(AST.Statement) = .empty,

    pub const name = "ExpressionSplitter";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var splitter: ExpressionSplitter = .{
            .allocator = context.dispenser.allocator,
            .scratch_allocator = context.scratchAllocator(),
            .dialect = context.dialect,
            .dispenser = context.dispenser,
        };
        defer deinitStatements(splitter.allocator, splitter.scratch_allocator, &splitter.statements_to_prefix);
        try splitter.visitBlock(ast);
    }

    fn visitBlock(self: *ExpressionSplitter, block: *AST.Block) anyerror!void {
        // Ancestors may have pending prefixes (for example an if condition).
        // This block borrows the reusable suffix and transfers only that suffix.
        // On failure, run() destroys every still-pending node.
        const prefix_start = self.statements_to_prefix.items.len;

        var index: usize = 0;
        while (index < block.statements.items.len) {
            std.debug.assert(self.statements_to_prefix.items.len == prefix_start);
            try self.visitStatement(&block.statements.items[index]);
            const prefix_count = self.statements_to_prefix.items.len - prefix_start;
            if (prefix_count != 0) {
                try block.statements.insertSlice(
                    self.allocator,
                    index,
                    self.statements_to_prefix.items[prefix_start..],
                );
                self.statements_to_prefix.shrinkRetainingCapacity(prefix_start);
                index += prefix_count;
            }
            index += 1;
        }
    }

    fn visitStatement(self: *ExpressionSplitter, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| try self.visitExpression(value.value orelse return error.InvalidAst),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| {
                try self.outlineExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                try self.outlineExpression(value.expression orelse return error.InvalidAst);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                // A loop condition is reevaluated and cannot be outlined in
                // front of the loop without changing semantics.
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *ExpressionSplitter, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .function_call => |*call| try self.visitFunctionCall(call),
            .identifier, .literal => {},
        }
    }

    fn visitFunctionCall(self: *ExpressionSplitter, call: *AST.FunctionCall) anyerror!void {
        const builtin = try Utilities.resolveBuiltinFunction(&call.function_name, self.dialect);
        var index = call.arguments.items.len;
        while (index != 0) {
            index -= 1;
            if (builtin == null or builtin.?.literalArgument(index) == null)
                try self.outlineExpression(&call.arguments.items[index]);
        }
    }

    fn outlineExpression(self: *ExpressionSplitter, expression: *AST.Expression) anyerror!void {
        if (expression.* == .identifier) return;
        try self.visitExpression(expression);
        const temporary = try self.dispenser.newName(.{});
        const debug_data = switch (expression.*) {
            .function_call => |*value| value.debug_data,
            .identifier => unreachable,
            .literal => |*value| value.debug_data,
        };
        var variables = try AST.NameWithDebugDataList.initCapacity(self.allocator, 1);
        errdefer variables.deinit(self.allocator);
        variables.appendAssumeCapacity(.{ .debug_data = debug_data, .name = temporary });
        try self.statements_to_prefix.ensureUnusedCapacity(self.scratch_allocator, 1);
        const moved = expression.*;
        const moved_pointer = try self.allocator.create(AST.Expression);
        moved_pointer.* = moved;
        expression.* = .{ .identifier = .{ .debug_data = debug_data, .name = temporary } };
        self.statements_to_prefix.appendAssumeCapacity(.{ .variable_declaration = .{
            .debug_data = debug_data,
            .variables = variables,
            .value = moved_pointer,
        } });
        variables = .empty;
    }
};

fn deinitStatements(allocator: std.mem.Allocator, scratch_allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(scratch_allocator);
}
