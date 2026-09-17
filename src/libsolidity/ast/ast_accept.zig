// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Mechanical recursive dispatch translated from `AST_accept.h`.

const std = @import("std");
const AST = @import("ast.zig");
const ASTImplementation = @import("ast.zig");
const Visitors = @import("ast_visitor.zig");

pub fn accept(
    allocator: std.mem.Allocator,
    node: *const AST.Node,
    visitor: *Visitors.ASTConstVisitor,
) std.mem.Allocator.Error!void {
    if (visitor.visit(node)) {
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(allocator);
        try ASTImplementation.appendChildren(allocator, &children, node);
        for (children.items) |child| try accept(allocator, child, visitor);
    }
    visitor.endVisit(node);
}

pub fn acceptMutable(
    allocator: std.mem.Allocator,
    node: *AST.Node,
    visitor: *Visitors.ASTVisitor,
) std.mem.Allocator.Error!void {
    if (visitor.visit(node)) {
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(allocator);
        try ASTImplementation.appendChildren(allocator, &children, node);
        for (children.items) |child| try acceptMutable(allocator, @constCast(child), visitor);
    }
    visitor.endVisit(node);
}

test "accept preserves document order, pruning, and balanced end visits" {
    const State = struct {
        visits: std.ArrayList(AST.Kind) = .empty,
        ends: std.ArrayList(AST.Kind) = .empty,

        fn deinit(self: *@This()) void {
            self.visits.deinit(std.testing.allocator);
            self.ends.deinit(std.testing.allocator);
        }

        fn visit(context: ?*anyopaque, node: *const AST.Node) bool {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            self.visits.append(std.testing.allocator, node.nodeKind()) catch unreachable;
            return node.nodeKind() != .binary_operation;
        }

        fn end(context: ?*anyopaque, node: *const AST.Node) void {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            self.ends.append(std.testing.allocator, node.nodeKind()) catch unreachable;
        }
    };

    var tree = try AST.Tree.init(std.testing.allocator, "1 + 2;", "A.sol");
    defer tree.deinit();
    const one = try tree.createNode(.{}, .{ .literal = .{ .token = .Number, .value = "1" } });
    const two = try tree.createNode(.{}, .{ .literal = .{ .token = .Number, .value = "2" } });
    const add = try tree.createNode(.{}, .{ .binary_operation = .{
        .left = one,
        .operator = .Add,
        .right = two,
    } });
    const statement = try tree.createNode(.{}, .{ .expression_statement = .{ .expression = add } });
    const statements = try tree.ownSlice(*AST.Node, &.{statement});
    const block = try tree.createNode(.{}, .{ .block = .{ .statements = statements } });

    var state: State = .{};
    defer state.deinit();
    var visitor = Visitors.SimpleASTVisitor.init(&state, State.visit, State.end);
    try accept(std.testing.allocator, block, &visitor);
    try std.testing.expectEqualSlices(AST.Kind, &.{ .block, .expression_statement, .binary_operation }, state.visits.items);
    try std.testing.expectEqualSlices(AST.Kind, &.{ .binary_operation, .expression_statement, .block }, state.ends.items);
}
