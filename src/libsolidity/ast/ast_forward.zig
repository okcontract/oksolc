// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Ownership and comparison primitives corresponding to `ASTForward.h`.
//!
//! Solidity AST nodes live in a compilation arena in the Zig port. An
//! `ASTPointer(T)` is therefore a borrowed stable pointer rather than a
//! reference-counted allocation per node.

const std = @import("std");

pub const ASTString = []u8;
pub const ASTStringView = []const u8;

pub fn ASTPointer(comptime T: type) type {
    return *T;
}

pub fn ASTCompareByID(comptime T: type) type {
    return struct {
        fn nodeId(node: *const T) i64 {
            if (@hasField(T, "id")) return @intCast(node.id);
            if (@hasDecl(T, "id")) return @intCast(node.id());
            @compileError(@typeName(T) ++ " has neither an id field nor an id() method");
        }

        pub fn lessNodes(left: *const T, right: *const T) bool {
            return nodeId(left) < nodeId(right);
        }

        pub fn nodeBeforeId(left: *const T, right: i64) bool {
            return nodeId(left) < right;
        }

        pub fn idBeforeNode(left: i64, right: *const T) bool {
            return left < nodeId(right);
        }
    };
}

test "AST ID comparison supports node and transparent integer lookups" {
    const Node = struct {
        value: i64,
        fn id(self: *const @This()) i64 {
            return self.value;
        }
    };
    const Compare = ASTCompareByID(Node);
    const one: Node = .{ .value = 1 };
    const two: Node = .{ .value = 2 };
    try std.testing.expect(Compare.lessNodes(&one, &two));
    try std.testing.expect(Compare.nodeBeforeId(&one, 2));
    try std.testing.expect(Compare.idBeforeNode(1, &two));
}

test "AST ID comparison accepts the translated node field representation" {
    const Node = struct { id: i64 };
    const Compare = ASTCompareByID(Node);
    const one: Node = .{ .id = 1 };
    const two: Node = .{ .id = 2 };
    try std.testing.expect(Compare.lessNodes(&one, &two));
    try std.testing.expect(Compare.nodeBeforeId(&one, 2));
    try std.testing.expect(Compare.idBeforeNode(1, &two));
}
