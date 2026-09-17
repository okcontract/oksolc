// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Source-location-independent syntactic and alpha-equivalence comparison.

const std = @import("std");
const AST = @import("../ast.zig");
const Utilities = @import("../utilities.zig");
const YulName = @import("../yul_name.zig").YulName;

pub const SyntacticallyEqual = struct {
    allocator: std.mem.Allocator,
    ids_used: u32 = 0,
    identifiers_lhs: std.AutoHashMapUnmanaged(YulName, u32) = .empty,
    identifiers_rhs: std.AutoHashMapUnmanaged(YulName, u32) = .empty,

    const stack_case_capacity = 16;

    pub fn init(allocator: std.mem.Allocator) SyntacticallyEqual {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *SyntacticallyEqual) void {
        self.identifiers_lhs.deinit(self.allocator);
        self.identifiers_rhs.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn resetRetainingCapacity(self: *SyntacticallyEqual) void {
        self.ids_used = 0;
        self.identifiers_lhs.clearRetainingCapacity();
        self.identifiers_rhs.clearRetainingCapacity();
    }

    pub fn expression(self: *SyntacticallyEqual, lhs: *const AST.Expression, rhs: *const AST.Expression) anyerror!bool {
        self.resetRetainingCapacity();
        return self.expressionImpl(lhs, rhs);
    }

    fn expressionImpl(self: *SyntacticallyEqual, lhs: *const AST.Expression, rhs: *const AST.Expression) anyerror!bool {
        if (std.meta.activeTag(lhs.*) != std.meta.activeTag(rhs.*)) return false;
        return switch (lhs.*) {
            .function_call => |*left| self.functionCall(left, &rhs.function_call),
            .identifier => |*left| self.identifier(left, &rhs.identifier),
            .literal => |*left| literal(left, &rhs.literal),
        };
    }

    pub fn statement(self: *SyntacticallyEqual, lhs: *const AST.Statement, rhs: *const AST.Statement) anyerror!bool {
        self.resetRetainingCapacity();
        return self.statementImpl(lhs, rhs);
    }

    fn statementImpl(self: *SyntacticallyEqual, lhs: *const AST.Statement, rhs: *const AST.Statement) anyerror!bool {
        if (std.meta.activeTag(lhs.*) != std.meta.activeTag(rhs.*)) return false;
        return switch (lhs.*) {
            .expression_statement => |*left| self.expressionImpl(&left.expression, &rhs.expression_statement.expression),
            .assignment => |*left| self.assignment(left, &rhs.assignment),
            .variable_declaration => |*left| self.variableDeclaration(left, &rhs.variable_declaration),
            .function_definition => |*left| self.functionDefinition(left, &rhs.function_definition),
            .if_statement => |*left| self.ifStatement(left, &rhs.if_statement),
            .switch_statement => |*left| self.switchStatement(left, &rhs.switch_statement),
            .for_loop => |*left| self.forLoop(left, &rhs.for_loop),
            .break_statement, .continue_statement, .leave_statement => true,
            .block => |*left| self.blockImpl(left, &rhs.block),
        };
    }

    pub fn block(self: *SyntacticallyEqual, lhs: *const AST.Block, rhs: *const AST.Block) anyerror!bool {
        self.resetRetainingCapacity();
        return self.blockImpl(lhs, rhs);
    }

    fn blockImpl(self: *SyntacticallyEqual, lhs: *const AST.Block, rhs: *const AST.Block) anyerror!bool {
        if (lhs.statements.items.len != rhs.statements.items.len) return false;
        for (lhs.statements.items, rhs.statements.items) |*left, *right|
            if (!try self.statementImpl(left, right)) return false;
        return true;
    }

    fn functionCall(self: *SyntacticallyEqual, lhs: *const AST.FunctionCall, rhs: *const AST.FunctionCall) anyerror!bool {
        if (!try self.functionName(&lhs.function_name, &rhs.function_name)) return false;
        if (lhs.arguments.items.len != rhs.arguments.items.len) return false;
        for (lhs.arguments.items, rhs.arguments.items) |*left, *right|
            if (!try self.expressionImpl(left, right)) return false;
        return true;
    }

    fn functionName(self: *SyntacticallyEqual, lhs: *const AST.FunctionName, rhs: *const AST.FunctionName) anyerror!bool {
        if (std.meta.activeTag(lhs.*) != std.meta.activeTag(rhs.*)) return false;
        return switch (lhs.*) {
            .builtin => |left| left.handle.id == rhs.builtin.handle.id,
            .identifier => |*left| self.identifier(left, &rhs.identifier),
        };
    }

    fn identifier(self: *SyntacticallyEqual, lhs: *const AST.Identifier, rhs: *const AST.Identifier) bool {
        const lhs_id = self.identifiers_lhs.get(lhs.name);
        const rhs_id = self.identifiers_rhs.get(rhs.name);
        if (lhs_id == null and rhs_id == null) return lhs.name.eql(rhs.name);
        return lhs_id != null and rhs_id != null and lhs_id.? == rhs_id.?;
    }

    fn literal(lhs: *const AST.Literal, rhs: *const AST.Literal) bool {
        return lhs.value.eql(&rhs.value);
    }

    fn assignment(self: *SyntacticallyEqual, lhs: *const AST.Assignment, rhs: *const AST.Assignment) anyerror!bool {
        if (lhs.variable_names.items.len != rhs.variable_names.items.len) return false;
        for (lhs.variable_names.items, rhs.variable_names.items) |*left, *right|
            if (!self.identifier(left, right)) return false;
        return self.optionalExpression(lhs.value, rhs.value);
    }

    fn variableDeclaration(
        self: *SyntacticallyEqual,
        lhs: *const AST.VariableDeclaration,
        rhs: *const AST.VariableDeclaration,
    ) anyerror!bool {
        if (!try self.optionalExpression(lhs.value, rhs.value)) return false;
        if (lhs.variables.items.len != rhs.variables.items.len) return false;
        for (lhs.variables.items, rhs.variables.items) |*left, *right|
            try self.visitDeclaration(left, right);
        return true;
    }

    fn functionDefinition(
        self: *SyntacticallyEqual,
        lhs: *const AST.FunctionDefinition,
        rhs: *const AST.FunctionDefinition,
    ) anyerror!bool {
        if (lhs.parameters.items.len != rhs.parameters.items.len or
            lhs.return_variables.items.len != rhs.return_variables.items.len)
            return false;
        for (lhs.parameters.items, rhs.parameters.items) |*left, *right|
            try self.visitDeclaration(left, right);
        for (lhs.return_variables.items, rhs.return_variables.items) |*left, *right|
            try self.visitDeclaration(left, right);
        return self.blockImpl(&lhs.body, &rhs.body);
    }

    fn ifStatement(self: *SyntacticallyEqual, lhs: *const AST.If, rhs: *const AST.If) anyerror!bool {
        return try self.optionalExpression(lhs.condition, rhs.condition) and try self.blockImpl(&lhs.body, &rhs.body);
    }

    fn switchStatement(self: *SyntacticallyEqual, lhs: *const AST.Switch, rhs: *const AST.Switch) anyerror!bool {
        if (!try self.optionalExpression(lhs.expression, rhs.expression)) return false;
        if (lhs.cases.items.len != rhs.cases.items.len) return false;
        const case_count = lhs.cases.items.len;
        var lhs_stack: [stack_case_capacity]*const AST.Case = undefined;
        var rhs_stack: [stack_case_capacity]*const AST.Case = undefined;
        var heap_cases: ?[]*const AST.Case = null;
        defer if (heap_cases) |cases| self.allocator.free(cases);

        const lhs_cases, const rhs_cases = if (case_count <= stack_case_capacity)
            .{ lhs_stack[0..case_count], rhs_stack[0..case_count] }
        else heap: {
            const cases = try self.allocator.alloc(
                *const AST.Case,
                try std.math.mul(usize, case_count, 2),
            );
            heap_cases = cases;
            break :heap .{ cases[0..case_count], cases[case_count..] };
        };
        for (lhs.cases.items, lhs_cases) |*case_value, *target| target.* = case_value;
        for (rhs.cases.items, rhs_cases) |*case_value, *target| target.* = case_value;
        std.sort.heap(*const AST.Case, lhs_cases, {}, caseLessThan);
        std.sort.heap(*const AST.Case, rhs_cases, {}, caseLessThan);
        for (lhs_cases, rhs_cases) |left, right|
            if (!try self.switchCase(left, right)) return false;
        return true;
    }

    fn switchCase(self: *SyntacticallyEqual, lhs: *const AST.Case, rhs: *const AST.Case) anyerror!bool {
        if (!optionalLiteralEqual(lhs.value, rhs.value)) return false;
        return self.blockImpl(&lhs.body, &rhs.body);
    }

    fn forLoop(self: *SyntacticallyEqual, lhs: *const AST.ForLoop, rhs: *const AST.ForLoop) anyerror!bool {
        return try self.blockImpl(&lhs.pre, &rhs.pre) and
            try self.optionalExpression(lhs.condition, rhs.condition) and
            try self.blockImpl(&lhs.body, &rhs.body) and
            try self.blockImpl(&lhs.post, &rhs.post);
    }

    fn optionalExpression(
        self: *SyntacticallyEqual,
        lhs: ?*const AST.Expression,
        rhs: ?*const AST.Expression,
    ) anyerror!bool {
        if (lhs == null or rhs == null) return lhs == null and rhs == null;
        return self.expressionImpl(lhs.?, rhs.?);
    }

    fn visitDeclaration(
        self: *SyntacticallyEqual,
        lhs: *const AST.NameWithDebugData,
        rhs: *const AST.NameWithDebugData,
    ) !void {
        const id = self.ids_used;
        self.ids_used += 1;
        try self.identifiers_lhs.put(self.allocator, lhs.name, id);
        try self.identifiers_rhs.put(self.allocator, rhs.name, id);
    }
};

pub const SyntacticallyEqualExpression = struct {
    pub fn eql(
        _: std.mem.Allocator,
        lhs: *const AST.Expression,
        rhs: *const AST.Expression,
    ) bool {
        return eqlNoAlloc(lhs, rhs);
    }

    /// Expressions contain no declarations, so alpha-renaming state is never
    /// populated while comparing them. Keep this infallible form for hash-map
    /// contexts and optimizer hot paths.
    pub fn eqlNoAlloc(lhs: *const AST.Expression, rhs: *const AST.Expression) bool {
        if (std.meta.activeTag(lhs.*) != std.meta.activeTag(rhs.*)) return false;
        return switch (lhs.*) {
            .function_call => |*left| functionCall(left, &rhs.function_call),
            .identifier => |*left| left.name.eql(rhs.identifier.name),
            .literal => |*left| left.value.eql(&rhs.literal.value),
        };
    }

    fn functionCall(lhs: *const AST.FunctionCall, rhs: *const AST.FunctionCall) bool {
        if (!functionName(&lhs.function_name, &rhs.function_name)) return false;
        if (lhs.arguments.items.len != rhs.arguments.items.len) return false;
        for (lhs.arguments.items, rhs.arguments.items) |*left, *right|
            if (!eqlNoAlloc(left, right)) return false;
        return true;
    }

    fn functionName(lhs: *const AST.FunctionName, rhs: *const AST.FunctionName) bool {
        if (std.meta.activeTag(lhs.*) != std.meta.activeTag(rhs.*)) return false;
        return switch (lhs.*) {
            .builtin => |left| left.handle.id == rhs.builtin.handle.id,
            .identifier => |left| left.name.eql(rhs.identifier.name),
        };
    }
};

fn optionalLiteralEqual(lhs: ?*const AST.Literal, rhs: ?*const AST.Literal) bool {
    if (lhs == null or rhs == null) return lhs == null and rhs == null;
    return lhs.?.value.eql(&rhs.?.value);
}

fn caseLessThan(_: void, lhs: *const AST.Case, rhs: *const AST.Case) bool {
    return Utilities.switchCaseLessThan(lhs, rhs);
}

test "syntactic equality treats consistently renamed declarations as equal" {
    const allocator = std.testing.allocator;
    const x = try YulName.init("x");
    const renamed = try YulName.init("renamed");
    var left: AST.Block = .{};
    defer left.deinit(allocator);
    var left_decl: AST.VariableDeclaration = .{};
    try left_decl.variables.append(allocator, .{ .name = x });
    try left.statements.append(allocator, .{ .variable_declaration = left_decl });
    try left.statements.append(allocator, .{ .expression_statement = .{
        .expression = .{ .identifier = .{ .name = x } },
    } });
    var right: AST.Block = .{};
    defer right.deinit(allocator);
    var right_decl: AST.VariableDeclaration = .{};
    try right_decl.variables.append(allocator, .{ .name = renamed });
    try right.statements.append(allocator, .{ .variable_declaration = right_decl });
    try right.statements.append(allocator, .{ .expression_statement = .{
        .expression = .{ .identifier = .{ .name = renamed } },
    } });
    var comparator = SyntacticallyEqual.init(allocator);
    defer comparator.deinit();
    try std.testing.expect(try comparator.block(&left, &right));

    const old_name: AST.Expression = .{ .identifier = .{ .name = x } };
    const old_renamed_name: AST.Expression = .{ .identifier = .{ .name = renamed } };
    try std.testing.expect(!try comparator.expression(&old_name, &old_renamed_name));
}

test "syntactic equality reorders small switch cases without allocating" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const Parser = @import("../asm_parser.zig").Parser;
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    var left = (try Parser.parseSource(
        allocator,
        "{ switch 0 case 1 { pop(1) } case 2 { pop(2) } default { pop(0) } }",
        "left.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer left.deinit();
    var right = (try Parser.parseSource(
        allocator,
        "{ switch 0 case 2 { pop(2) } case 1 { pop(1) } default { pop(0) } }",
        "right.yul",
        &reporter,
        .{},
        .{},
    )).?;
    defer right.deinit();

    var comparator = SyntacticallyEqual.init(std.testing.failing_allocator);
    defer comparator.deinit();
    try std.testing.expect(try comparator.block(left.root(), right.root()));
}
