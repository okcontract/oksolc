// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Data-flow-independent simplification of Yul control-flow constructs.

const std = @import("std");
const AST = @import("../ast.zig");
const OptimiserStepContext = @import("optimiser_step.zig").OptimiserStepContext;
const Semantics = @import("semantics.zig");

pub const ControlFlowSimplifier = struct {
    allocator: std.mem.Allocator,
    dialect: AST.Dialect,
    num_break_statements: usize = 0,
    num_continue_statements: usize = 0,

    pub const name = "ControlFlowSimplifier";

    pub fn run(context: *OptimiserStepContext, ast: *AST.Block) anyerror!void {
        var pass: ControlFlowSimplifier = .{
            .allocator = context.dispenser.allocator,
            .dialect = context.dialect,
        };
        try pass.visitBlock(ast);
    }

    fn visitBlock(self: *ControlFlowSimplifier, block: *AST.Block) anyerror!void {
        try self.simplify(&block.statements);
    }

    fn visitStatement(self: *ControlFlowSimplifier, statement: *AST.Statement) anyerror!void {
        if (statement.* == .for_loop) {
            try self.visitForLoopStatement(statement);
            return;
        }
        switch (statement.*) {
            .function_definition => |*value| {
                try self.visitBlock(&value.body);
                if (value.body.statements.items.len != 0 and
                    value.body.statements.items[value.body.statements.items.len - 1] == .leave_statement)
                {
                    var removed = value.body.statements.pop().?;
                    removed.deinit(self.allocator);
                }
            },
            .if_statement => |*value| try self.visitBlock(&value.body),
            .switch_statement => |*value| for (value.cases.items) |*case_value|
                try self.visitBlock(&case_value.body),
            .block => |*value| try self.visitBlock(value),
            .break_statement => self.num_break_statements += 1,
            .continue_statement => self.num_continue_statements += 1,
            else => {},
        }
    }

    fn visitForLoopStatement(
        self: *ControlFlowSimplifier,
        statement: *AST.Statement,
    ) anyerror!void {
        const loop = &statement.for_loop;
        if (loop.pre.statements.items.len != 0) return error.ForLoopInitNotRewritten;
        const outer_break = self.num_break_statements;
        const outer_continue = self.num_continue_statements;
        self.num_break_statements = 0;
        self.num_continue_statements = 0;
        defer {
            self.num_break_statements = outer_break;
            self.num_continue_statements = outer_continue;
        }

        try self.visitBlock(&loop.pre);
        try self.visitBlock(&loop.post);
        try self.visitBlock(&loop.body);
        if (loop.body.statements.items.len == 0) return;

        const finder = Semantics.TerminationFinder.init(self.dialect, null);
        const last_index = loop.body.statements.items.len - 1;
        const control_flow = try finder.controlFlowKind(&loop.body.statements.items[last_index]);
        var terminating = false;
        if (control_flow == .break_flow) {
            terminating = true;
            if (self.num_break_statements == 0) return error.InvalidBreakAccounting;
            self.num_break_statements -= 1;
        } else if (control_flow == .terminate or control_flow == .leave) {
            terminating = true;
        }
        if (!terminating or self.num_continue_statements != 0 or self.num_break_statements != 0) return;

        if (control_flow == .break_flow) {
            var removed = loop.body.statements.pop().?;
            removed.deinit(self.allocator);
        }
        const condition = loop.condition orelse return error.InvalidAst;
        const moved_condition = condition;
        const moved_body = loop.body;
        loop.condition = null;
        loop.body = .{};
        const debug_data = loop.debug_data;
        loop.deinit(self.allocator);
        statement.* = .{ .if_statement = .{
            .debug_data = debug_data,
            .condition = moved_condition,
            .body = moved_body,
        } };
    }

    fn simplify(
        self: *ControlFlowSimplifier,
        statements: *std.ArrayList(AST.Statement),
    ) anyerror!void {
        var index: usize = 0;
        while (index < statements.items.len) {
            if (try self.replacementFor(&statements.items[index])) |*replacement| {
                var owned = replacement.*;
                defer deinitStatements(self.allocator, &owned);
                try self.simplify(&owned);
                try statements.ensureUnusedCapacity(self.allocator, owned.items.len);
                var removed = statements.orderedRemove(index);
                removed.deinit(self.allocator);
                statements.insertSliceAssumeCapacity(index, owned.items);
                const inserted = owned.items.len;
                owned.clearRetainingCapacity();
                index += inserted;
            } else {
                try self.visitStatement(&statements.items[index]);
                index += 1;
            }
        }
    }

    fn replacementFor(
        self: *ControlFlowSimplifier,
        statement: *AST.Statement,
    ) anyerror!?std.ArrayList(AST.Statement) {
        return switch (statement.*) {
            .if_statement => |*if_statement| if (if_statement.body.statements.items.len == 0 and
                self.dialect.discardFunctionHandle() != null)
                try self.reduceEmptyIf(if_statement)
            else
                null,
            .switch_statement => |*switch_statement| blk: {
                removeEmptyDefault(self.allocator, switch_statement);
                removeEmptyCasesWithoutDefault(self.allocator, switch_statement);
                if (switch_statement.cases.items.len == 0)
                    break :blk try self.reduceNoCaseSwitch(switch_statement);
                if (switch_statement.cases.items.len == 1)
                    break :blk try self.reduceSingleCaseSwitch(switch_statement);
                break :blk null;
            },
            else => null,
        };
    }

    fn reduceEmptyIf(
        self: *ControlFlowSimplifier,
        if_statement: *AST.If,
    ) anyerror!std.ArrayList(AST.Statement) {
        return self.singleDiscardStatement(&if_statement.condition);
    }

    fn reduceNoCaseSwitch(
        self: *ControlFlowSimplifier,
        switch_statement: *AST.Switch,
    ) anyerror!?std.ArrayList(AST.Statement) {
        if (self.dialect.discardFunctionHandle() == null) return null;
        return try self.singleDiscardStatement(&switch_statement.expression);
    }

    fn reduceSingleCaseSwitch(
        self: *ControlFlowSimplifier,
        switch_statement: *AST.Switch,
    ) anyerror!?std.ArrayList(AST.Statement) {
        const switch_case = &switch_statement.cases.items[0];
        const expression_debug = debugData(switch_statement.expression orelse return error.InvalidAst);
        if (switch_case.value) |case_literal| {
            const equality = self.dialect.equalityFunctionHandle() orelse return null;
            var result: std.ArrayList(AST.Statement) = .empty;
            errdefer deinitStatements(self.allocator, &result);
            try result.ensureTotalCapacity(self.allocator, 1);
            var arguments: std.ArrayList(AST.Expression) = .empty;
            errdefer deinitExpressions(self.allocator, &arguments);
            try arguments.ensureTotalCapacity(self.allocator, 2);
            const literal = case_literal.*;
            switch_case.value = null;
            self.allocator.destroy(case_literal);
            arguments.appendAssumeCapacity(.{ .literal = literal });
            const switch_expression = takeExpressionPointer(
                self.allocator,
                &switch_statement.expression,
            );
            arguments.appendAssumeCapacity(switch_expression);
            var body = switch_case.body;
            switch_case.body = .{};
            errdefer body.deinit(self.allocator);
            const condition = try AST.createExpression(self.allocator, .{ .function_call = .{
                .debug_data = expression_debug,
                .function_name = .{ .builtin = .{
                    .debug_data = expression_debug,
                    .handle = equality,
                } },
                .arguments = arguments,
            } });
            arguments = .empty;
            result.appendAssumeCapacity(.{ .if_statement = .{
                .debug_data = switch_statement.debug_data,
                .condition = condition,
                .body = body,
            } });
            body = .{};
            return result;
        }

        if (self.dialect.discardFunctionHandle() == null) return null;
        var result = try self.singleDiscardStatement(&switch_statement.expression);
        errdefer deinitStatements(self.allocator, &result);
        try result.ensureTotalCapacity(self.allocator, 2);
        var body = switch_case.body;
        switch_case.body = .{};
        result.appendAssumeCapacity(.{ .block = body });
        body = .{};
        return result;
    }

    fn singleDiscardStatement(
        self: *ControlFlowSimplifier,
        expression: *?*AST.Expression,
    ) anyerror!std.ArrayList(AST.Statement) {
        const debug_data = debugData(expression.* orelse return error.InvalidAst);
        const discard = self.dialect.discardFunctionHandle() orelse return error.MissingDiscardFunction;
        var result: std.ArrayList(AST.Statement) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitStatements(self.allocator, &result);
        try result.ensureTotalCapacity(self.allocator, 1);
        var arguments: std.ArrayList(AST.Expression) = .empty; // zlinter-disable-current-line require_errdefer_dealloc - adjacent project cleanup handles nested element ownership
        errdefer deinitExpressions(self.allocator, &arguments);
        try arguments.ensureTotalCapacity(self.allocator, 1);
        // Reserve both owners before removing the expression from its source.
        arguments.appendAssumeCapacity(takeExpressionPointer(self.allocator, expression));
        result.appendAssumeCapacity(.{ .expression_statement = .{
            .debug_data = debug_data,
            .expression = .{ .function_call = .{
                .debug_data = debug_data,
                .function_name = .{ .builtin = .{
                    .debug_data = debug_data,
                    .handle = discard,
                } },
                .arguments = arguments,
            } },
        } });
        return result;
    }
};

fn removeEmptyDefault(allocator: std.mem.Allocator, switch_statement: *AST.Switch) void {
    var index: usize = 0;
    while (index < switch_statement.cases.items.len) {
        const case_value = &switch_statement.cases.items[index];
        if (case_value.value == null and case_value.body.statements.items.len == 0) {
            var removed = switch_statement.cases.orderedRemove(index);
            removed.deinit(allocator);
        } else {
            index += 1;
        }
    }
}

fn removeEmptyCasesWithoutDefault(allocator: std.mem.Allocator, switch_statement: *AST.Switch) void {
    if (AST.hasDefaultCase(switch_statement)) return;
    var index: usize = 0;
    while (index < switch_statement.cases.items.len) {
        if (switch_statement.cases.items[index].body.statements.items.len == 0) {
            var removed = switch_statement.cases.orderedRemove(index);
            removed.deinit(allocator);
        } else {
            index += 1;
        }
    }
}

fn takeExpressionPointer(
    allocator: std.mem.Allocator,
    pointer: *?*AST.Expression,
) AST.Expression {
    const owned = pointer.*.?;
    const expression = owned.*;
    allocator.destroy(owned);
    pointer.* = null;
    return expression;
}

fn debugData(expression: *const AST.Expression) ?@import("../../liblangutil/debug_data.zig").DebugData {
    return switch (expression.*) {
        .function_call => |value| value.debug_data,
        .identifier => |value| value.debug_data,
        .literal => |value| value.debug_data,
    };
}

fn deinitExpressions(allocator: std.mem.Allocator, expressions: *std.ArrayList(AST.Expression)) void {
    for (expressions.items) |*expression| expression.deinit(allocator);
    expressions.deinit(allocator);
}

fn deinitStatements(allocator: std.mem.Allocator, statements: *std.ArrayList(AST.Statement)) void {
    for (statements.items) |*statement| statement.deinit(allocator);
    statements.deinit(allocator);
}

test "discard rewrites retain expression ownership on allocation failure" {
    const EVMDialect = @import("../backends/evm/evm_dialect.zig").EVMDialect;
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    var dialect = try EVMDialect.init(std.testing.allocator, EVMVersion.current(), false);
    defer dialect.deinit();
    for ([_][]const u8{
        "{ if add(1, 2) {} }",
        "{ switch add(1, 2) default {} }",
        "{ switch add(1, 2) default { pop(3) } }",
    }) |source|
        try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseDiscardRewrite, .{ dialect.dialect(), source });
}

fn exerciseDiscardRewrite(allocator: std.mem.Allocator, dialect: AST.Dialect, source: []const u8) !void {
    const Parser = @import("../asm_parser.zig").Parser;
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var ast = (try Parser.parseSource(allocator, source, "discard.yul", &reporter, dialect, .{})) orelse
        return error.TestUnexpectedResult;
    defer ast.deinit();
    var pass = ControlFlowSimplifier{ .allocator = allocator, .dialect = dialect };
    try pass.visitBlock(&ast.root_block);
    try std.testing.expect(ast.root().statements.items[0] == .expression_statement);
}
