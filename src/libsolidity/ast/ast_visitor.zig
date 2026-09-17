// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Open visitor interface translated from `ASTVisitor.h`.
//!
//! The syntax hierarchy itself is closed, but compiler passes are open. A
//! context plus function-pointer table preserves node-specific overrides
//! without allocating visitor objects or relying on hidden virtual dispatch.

const std = @import("std");
const AST = @import("ast.zig");

pub const VisitFn = *const fn (?*anyopaque, *const AST.Node) bool;
pub const EndVisitFn = *const fn (?*anyopaque, *const AST.Node) void;
pub const MutableVisitFn = *const fn (?*anyopaque, *AST.Node) bool;
pub const MutableEndVisitFn = *const fn (?*anyopaque, *AST.Node) void;

const kind_count = std.meta.fields(AST.Kind).len;

pub const ASTConstVisitor = struct {
    context: ?*anyopaque = null,
    visit_node: ?VisitFn = null,
    end_visit_node: ?EndVisitFn = null,
    visits: [kind_count]?VisitFn = [_]?VisitFn{null} ** kind_count,
    end_visits: [kind_count]?EndVisitFn = [_]?EndVisitFn{null} ** kind_count,

    pub fn setVisit(self: *ASTConstVisitor, kind: AST.Kind, function: VisitFn) void {
        self.visits[@intFromEnum(kind)] = function;
    }

    pub fn setEndVisit(self: *ASTConstVisitor, kind: AST.Kind, function: EndVisitFn) void {
        self.end_visits[@intFromEnum(kind)] = function;
    }

    pub fn visit(self: *ASTConstVisitor, node: *const AST.Node) bool {
        if (self.visits[@intFromEnum(node.nodeKind())]) |function|
            return function(self.context, node);
        if (self.visit_node) |function| return function(self.context, node);
        return true;
    }

    pub fn endVisit(self: *ASTConstVisitor, node: *const AST.Node) void {
        if (self.end_visits[@intFromEnum(node.nodeKind())]) |function| {
            function(self.context, node);
            return;
        }
        if (self.end_visit_node) |function| function(self.context, node);
    }
};

pub const ASTVisitor = struct {
    context: ?*anyopaque = null,
    visit_node: ?MutableVisitFn = null,
    end_visit_node: ?MutableEndVisitFn = null,
    visits: [kind_count]?MutableVisitFn = [_]?MutableVisitFn{null} ** kind_count,
    end_visits: [kind_count]?MutableEndVisitFn = [_]?MutableEndVisitFn{null} ** kind_count,

    pub fn setVisit(self: *ASTVisitor, kind: AST.Kind, function: MutableVisitFn) void {
        self.visits[@intFromEnum(kind)] = function;
    }

    pub fn setEndVisit(self: *ASTVisitor, kind: AST.Kind, function: MutableEndVisitFn) void {
        self.end_visits[@intFromEnum(kind)] = function;
    }

    pub fn visit(self: *ASTVisitor, node: *AST.Node) bool {
        if (self.visits[@intFromEnum(node.nodeKind())]) |function|
            return function(self.context, node);
        if (self.visit_node) |function| return function(self.context, node);
        return true;
    }

    pub fn endVisit(self: *ASTVisitor, node: *AST.Node) void {
        if (self.end_visits[@intFromEnum(node.nodeKind())]) |function| {
            function(self.context, node);
            return;
        }
        if (self.end_visit_node) |function| function(self.context, node);
    }
};

pub const SimpleASTVisitor = struct {
    pub fn init(
        context: ?*anyopaque,
        on_visit: ?VisitFn,
        on_end_visit: ?EndVisitFn,
    ) ASTConstVisitor {
        return .{
            .context = context,
            .visit_node = on_visit,
            .end_visit_node = on_end_visit,
        };
    }
};

test "node-specific visitor callbacks override generic callbacks" {
    const State = struct {
        generic_count: usize = 0,
        literal_count: usize = 0,

        fn generic(context: ?*anyopaque, _: *const AST.Node) bool {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            self.generic_count += 1;
            return true;
        }

        fn literal(context: ?*anyopaque, _: *const AST.Node) bool {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            self.literal_count += 1;
            return true;
        }
    };

    var tree = try AST.Tree.init(std.testing.allocator, "1", "A.sol");
    defer tree.deinit();
    const literal = try tree.createNode(.{}, .{ .literal = .{ .token = .Number, .value = "1" } });
    var state: State = .{};
    var visitor = SimpleASTVisitor.init(&state, State.generic, null);
    visitor.setVisit(.literal, State.literal);
    try std.testing.expect(visitor.visit(literal));
    try std.testing.expectEqual(@as(usize, 0), state.generic_count);
    try std.testing.expectEqual(@as(usize, 1), state.literal_count);
}
