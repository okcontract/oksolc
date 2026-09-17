// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Finds single-expression functions that are safe to inline functionally.

const std = @import("std");
const AST = @import("../ast.zig");
const NameCollector = @import("name_collector.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const InlinableExpressionFunctionFinder = struct {
    allocator: std.mem.Allocator,
    found_disallowed_identifier: bool = false,
    disallowed_identifiers: NameCollector.NameSet = .{},
    inlinable_functions: NameCollector.FunctionDefinitionMap = .{},

    pub fn init(allocator: std.mem.Allocator) InlinableExpressionFunctionFinder {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *InlinableExpressionFunctionFinder) void {
        self.disallowed_identifiers.deinit(self.allocator);
        self.inlinable_functions.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn run(self: *InlinableExpressionFunctionFinder, block: *const AST.Block) anyerror!void {
        try self.visitBlock(block);
    }

    pub fn inlinableFunctions(self: *const InlinableExpressionFunctionFinder) *const NameCollector.FunctionDefinitionMap {
        return &self.inlinable_functions;
    }

    fn visitBlock(self: *InlinableExpressionFunctionFinder, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *InlinableExpressionFunctionFinder, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .expression_statement => |*value| try self.visitExpression(&value.expression),
            .assignment => |*value| try self.visitExpression(value.value orelse return error.InvalidAst),
            .variable_declaration => |*value| if (value.value) |expression| try self.visitExpression(expression),
            .function_definition => |*value| try self.visitFunction(value),
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
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .block => |*value| try self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitFunction(
        self: *InlinableExpressionFunctionFinder,
        function: *const AST.FunctionDefinition,
    ) anyerror!void {
        if (function.return_variables.items.len == 1 and function.body.statements.items.len == 1) {
            const return_variable = function.return_variables.items[0].name;
            const assignment = switch (function.body.statements.items[0]) {
                .assignment => |*value| value,
                else => null,
            };
            if (assignment) |value| if (value.variable_names.items.len == 1 and
                value.variable_names.items[0].name.eql(return_variable))
            {
                if (!self.disallowed_identifiers.isEmpty() or self.found_disallowed_identifier)
                    return error.InvalidFinderState;
                _ = try self.disallowed_identifiers.insert(self.allocator, return_variable);
                _ = try self.disallowed_identifiers.insert(self.allocator, function.name);
                try self.visitExpression(value.value orelse return error.InvalidAst);
                if (!self.found_disallowed_identifier)
                    _ = try self.inlinable_functions.insert(self.allocator, function.name, function);
                self.disallowed_identifiers.map.clearRetainingCapacity();
                self.found_disallowed_identifier = false;
            };
        }
        try self.visitBlock(&function.body);
    }

    fn visitExpression(
        self: *InlinableExpressionFunctionFinder,
        expression: *const AST.Expression,
    ) anyerror!void {
        switch (expression.*) {
            .literal => {},
            .identifier => |identifier| self.checkAllowed(identifier.name),
            .function_call => |*call| {
                if (call.function_name == .identifier)
                    self.checkAllowed(call.function_name.identifier.name);
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
            },
        }
    }

    fn checkAllowed(self: *InlinableExpressionFunctionFinder, candidate: YulName) void {
        if (self.disallowed_identifiers.contains(candidate)) self.found_disallowed_identifier = true;
    }
};
