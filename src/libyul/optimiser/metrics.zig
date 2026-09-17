// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! AST-size, expression-cost, and assignment-count metrics for the optimizer.

const std = @import("std");
const ordered = @import("cxx_compat");
const AST = @import("../ast.zig");
const Utilities = @import("../utilities.zig");
const OptimizerUtilities = @import("optimizer_utilities.zig");
const InstructionModule = @import("../../libevmasm/instruction.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const CodeWeights = struct {
    expression_statement_cost: usize = 0,
    assignment_cost: usize = 0,
    variable_declaration_cost: usize = 0,
    function_definition_cost: usize = 1,
    if_cost: usize = 2,
    switch_cost: usize = 1,
    case_cost: usize = 2,
    for_loop_cost: usize = 3,
    break_cost: usize = 2,
    continue_cost: usize = 2,
    leave_cost: usize = 2,
    block_cost: usize = 0,
    function_call_cost: usize = 1,
    identifier_cost: usize = 0,
    literal_cost: usize = 1,
    literal_zero_cost: usize = 0,

    pub fn costOfStatement(self: CodeWeights, statement: *const AST.Statement) usize {
        return switch (statement.*) {
            .expression_statement => self.expression_statement_cost,
            .assignment => self.assignment_cost,
            .variable_declaration => self.variable_declaration_cost,
            .function_definition => self.function_definition_cost,
            .if_statement => self.if_cost,
            .switch_statement => |value| self.switch_cost + self.case_cost * value.cases.items.len,
            .for_loop => self.for_loop_cost,
            .break_statement => self.break_cost,
            .continue_statement => self.continue_cost,
            .leave_statement => self.leave_cost,
            .block => self.block_cost,
        };
    }

    pub fn costOfExpression(self: CodeWeights, expression: *const AST.Expression) usize {
        return switch (expression.*) {
            .function_call => self.function_call_cost,
            .identifier => self.identifier_cost,
            .literal => |*literal| if (literal.kind != .String and
                !literal.value.unlimited() and literal.value.numeric_value.? == 0)
                self.literal_zero_cost
            else
                self.literal_cost,
        };
    }
};

pub const CodeSize = struct {
    ignore_functions: bool,
    weights: CodeWeights,
    size: usize = 0,

    pub fn codeSizeStatement(statement: *const AST.Statement, weights: CodeWeights) usize {
        var metric: CodeSize = .{ .ignore_functions = true, .weights = weights };
        metric.visitStatement(statement);
        return metric.size;
    }

    pub fn codeSizeExpression(expression: *const AST.Expression, weights: CodeWeights) usize {
        var metric: CodeSize = .{ .ignore_functions = true, .weights = weights };
        metric.visitExpression(expression);
        return metric.size;
    }

    pub fn codeSize(block: *const AST.Block, weights: CodeWeights) usize {
        var metric: CodeSize = .{ .ignore_functions = true, .weights = weights };
        metric.visitBlock(block);
        return metric.size;
    }

    pub fn codeSizeIncludingFunctions(block: *const AST.Block, weights: CodeWeights) usize {
        var metric: CodeSize = .{ .ignore_functions = false, .weights = weights };
        metric.visitBlock(block);
        return metric.size;
    }

    fn visitBlock(self: *CodeSize, block: *const AST.Block) void {
        for (block.statements.items) |*statement| self.visitStatement(statement);
    }

    fn visitStatement(self: *CodeSize, statement: *const AST.Statement) void {
        if (statement.* == .function_definition and self.ignore_functions) return;
        self.size += self.weights.costOfStatement(statement);
        switch (statement.*) {
            .expression_statement => |*value| self.visitExpression(&value.expression),
            .assignment => |*value| if (value.value) |expression| self.visitExpression(expression),
            .variable_declaration => |*value| if (value.value) |expression| self.visitExpression(expression),
            .function_definition => |*value| self.visitBlock(&value.body),
            .if_statement => |*value| {
                if (value.condition) |condition| self.visitExpression(condition);
                self.visitBlock(&value.body);
            },
            .switch_statement => |*value| {
                if (value.expression) |expression| self.visitExpression(expression);
                // Case labels are control metadata. Upstream ASTWalker visits the
                // case bodies, but does not count their literal labels as code.
                for (value.cases.items) |*case_value| self.visitBlock(&case_value.body);
            },
            .for_loop => |*value| {
                self.visitBlock(&value.pre);
                if (value.condition) |condition| self.visitExpression(condition);
                self.visitBlock(&value.body);
                self.visitBlock(&value.post);
            },
            .block => |*value| self.visitBlock(value),
            .break_statement, .continue_statement, .leave_statement => {},
        }
    }

    fn visitExpression(self: *CodeSize, expression: *const AST.Expression) void {
        self.size += self.weights.costOfExpression(expression);
        switch (expression.*) {
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    self.visitExpression(&call.arguments.items[index]);
                }
            },
            .identifier, .literal => {},
        }
    }
};

pub const CodeCost = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    cost: usize = 0,

    pub fn codeCost(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        expression: *const AST.Expression,
    ) anyerror!usize {
        var metric: CodeCost = .{ .allocator = allocator, .dialect = dialect };
        try metric.visitExpression(expression);
        return metric.cost;
    }

    fn visitExpression(self: *CodeCost, expression: *const AST.Expression) anyerror!void {
        self.cost += 1;
        switch (expression.*) {
            .function_call => |*call| {
                var index = call.arguments.items.len;
                while (index != 0) {
                    index -= 1;
                    try self.visitExpression(&call.arguments.items[index]);
                }
                if (OptimizerUtilities.toEVMInstruction(self.dialect, &call.function_name)) |instruction|
                    self.addInstructionCost(instruction)
                else
                    self.cost += 49;
            },
            .literal => |*literal| try self.visitLiteral(literal),
            .identifier => {},
        }
    }

    fn visitLiteral(self: *CodeCost, literal: *const AST.Literal) anyerror!void {
        switch (literal.kind) {
            .Boolean => {},
            .Number => {
                var value = try literal.value.value();
                while (value >= 0x100) : (value >>= 8) self.cost += 1;
                if (try literal.value.value() == 0) {
                    if (@import("../backends/evm/evm_dialect.zig").fromDialect(self.dialect)) |evm_dialect| {
                        if (evm_dialect.evmVersion().hasPush0()) self.cost -= 1;
                    }
                }
            },
            .String => {
                const formatted = try Utilities.formatLiteralAlloc(self.allocator, literal, true);
                defer self.allocator.free(formatted);
                self.cost += formatted.len;
            },
        }
    }

    fn addInstructionCost(self: *CodeCost, instruction: InstructionModule.Instruction) void {
        const tier = InstructionModule.instructionInfo(
            instruction,
            OptimizerUtilities.evmVersionFromDialect(self.dialect),
        ).gas_price_tier;
        if (@intFromEnum(tier) < @intFromEnum(InstructionModule.Tier.VeryLow))
            self.cost -= 1
        else if (@intFromEnum(tier) < @intFromEnum(InstructionModule.Tier.High))
            self.cost += 1
        else
            self.cost += 49;
    }
};

fn lessYulName(left: YulName, right: YulName) bool {
    return left.lessThan(right);
}

pub const AssignmentCounts = ordered.OrderedMap(YulName, usize, lessYulName);

pub const AssignmentCounter = struct {
    allocator: std.mem.Allocator,
    counters: AssignmentCounts = .{},

    pub fn init(allocator: std.mem.Allocator) AssignmentCounter {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *AssignmentCounter) void {
        self.counters.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn run(self: *AssignmentCounter, block: *const AST.Block) !void {
        try self.visitBlock(block);
    }

    pub fn assignmentCount(self: *const AssignmentCounter, name: YulName) usize {
        return if (self.counters.get(name)) |count| count.* else 0;
    }

    pub fn assignments(self: *const AssignmentCounter) *const AssignmentCounts {
        return &self.counters;
    }

    fn increment(self: *AssignmentCounter, name: YulName) !void {
        if (self.counters.getPtr(name)) |count|
            count.* += 1
        else
            _ = try self.counters.insert(self.allocator, name, 1);
    }

    fn visitBlock(self: *AssignmentCounter, block: *const AST.Block) anyerror!void {
        for (block.statements.items) |*statement| try self.visitStatement(statement);
    }

    fn visitStatement(self: *AssignmentCounter, statement: *const AST.Statement) anyerror!void {
        switch (statement.*) {
            .assignment => |*value| for (value.variable_names.items) |identifier|
                try self.increment(identifier.name),
            .function_definition => |*value| try self.visitBlock(&value.body),
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .for_loop => |*value| {
                try self.visitBlock(&value.pre);
                try self.visitBlock(&value.body);
                try self.visitBlock(&value.post);
            },
            .block => |*value| try self.visitBlock(value),
            else => {},
        }
    }
};

test "metrics count default AST weight and assignments" {
    const allocator = std.testing.allocator;
    const name = try YulName.init("x");
    var root: AST.Block = .{};
    defer root.deinit(allocator);
    var assignment: AST.Assignment = .{};
    try assignment.variable_names.append(allocator, .{ .name = name });
    assignment.value = try AST.createExpression(allocator, .{ .identifier = .{ .name = name } });
    try root.statements.append(allocator, .{ .assignment = assignment });
    try std.testing.expectEqual(@as(usize, 0), CodeSize.codeSize(&root, .{}));
    var counter = AssignmentCounter.init(allocator);
    defer counter.deinit();
    try counter.run(&root);
    try std.testing.expectEqual(@as(usize, 1), counter.assignmentCount(name));
}
