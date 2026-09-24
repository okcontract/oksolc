// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Rejoins single-use temporary declarations into complex expressions.

const std = @import("std");
const AST = @import("../ast.zig");
const FunctionGrouper = @import("function_grouper.zig").FunctionGrouper;
const NameCollectorModule = @import("name_collector.zig");
const OptimizerUtilities = @import("optimizer_utilities.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;

pub const ExpressionJoiner = struct {
    allocator: std.mem.Allocator,
    references: NameCollectorModule.VariableReferenceMap,
    current_block: ?*AST.Block = null,
    latest_statement_index: usize = 0,

    pub const name = "ExpressionJoiner";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        const scratch_allocator = context.scratchAllocator();
        var joiner: ExpressionJoiner = .{
            .allocator = context.dispenser.allocator,
            .references = try NameCollectorModule.VariableReferencesCounter.countReferencesBlock(
                scratch_allocator,
                ast,
            ),
        };
        defer joiner.references.deinit(scratch_allocator);
        try joiner.visitBlock(ast);
        try FunctionGrouper.run(context, ast);
    }

    fn visitBlock(self: *ExpressionJoiner, block: *AST.Block) anyerror!void {
        self.resetLatestStatementPointer();
        for (block.statements.items, 0..) |*statement, index| {
            try self.visitStatement(statement);
            self.current_block = block;
            self.latest_statement_index = index;
        }
        OptimizerUtilities.removeEmptyBlocks(self.allocator, block);
        self.resetLatestStatementPointer();
    }

    fn visitStatement(self: *ExpressionJoiner, statement: *AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| try self.visitExpression(value.value orelse return error.InvalidAst),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| {
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                try self.visitExpression(value.expression orelse return error.InvalidAst);
                for (value.cases.items) |*case_value| try self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitExpression(value.condition orelse return error.InvalidAst);
                try self.visitBlock(&value.post);
                try self.visitBlock(&value.body);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *ExpressionJoiner, expression: *AST.Expression) anyerror!void {
        switch (expression.*) {
            .identifier => |identifier| if (self.isLatestStatementVarDeclJoinable(&identifier)) {
                const latest = self.latestStatement().?;
                const value = latest.variable_declaration.value.?;
                const moved = value.*;
                self.allocator.destroy(value);
                latest.variable_declaration.value = null;
                latest.deinit(self.allocator);
                latest.* = .{ .block = .{} };
                expression.* = moved;
                self.decrementLatestStatementPointer();
            },
            .function_call => |*call| try self.handleArguments(&call.arguments),
            .literal => {},
        }
    }

    fn handleArguments(
        self: *ExpressionJoiner,
        arguments: *std.ArrayList(AST.Expression),
    ) anyerror!void {
        var index = arguments.items.len;
        var reverse = arguments.items.len;
        while (reverse != 0) {
            reverse -= 1;
            index -= 1;
            const argument = arguments.items[reverse];
            if (argument != .identifier and argument != .literal) break;
        }
        while (index < arguments.items.len) : (index += 1)
            try self.visitExpression(&arguments.items[index]);
    }

    fn decrementLatestStatementPointer(self: *ExpressionJoiner) void {
        if (self.current_block == null) return;
        if (self.latest_statement_index > 0)
            self.latest_statement_index -= 1
        else
            self.resetLatestStatementPointer();
    }

    fn resetLatestStatementPointer(self: *ExpressionJoiner) void {
        self.current_block = null;
        self.latest_statement_index = std.math.maxInt(usize);
    }

    fn latestStatement(self: *ExpressionJoiner) ?*AST.Statement {
        const block = self.current_block orelse return null;
        if (self.latest_statement_index >= block.statements.items.len) return null;
        return &block.statements.items[self.latest_statement_index];
    }

    fn isLatestStatementVarDeclJoinable(
        self: *ExpressionJoiner,
        identifier: *const AST.Identifier,
    ) bool {
        const statement = self.latestStatement() orelse return false;
        if (statement.* != .variable_declaration) return false;
        const declaration = &statement.variable_declaration;
        if (declaration.variables.items.len != 1 or declaration.value == null) return false;
        const references = self.references.get(identifier.name) orelse return false;
        return declaration.variables.items[0].name.eql(identifier.name) and references.* == 1;
    }
};
