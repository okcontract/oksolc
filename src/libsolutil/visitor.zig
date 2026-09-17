// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Tagged-union dispatch replaces the C++ overload-set visitor. This module
//! keeps a single named boundary so translated call sites remain uniform.

pub fn visit(value: anytype, visitor: anytype) @TypeOf(visitor.visit(value)) {
    return visitor.visit(value);
}

pub fn fallback(comptime Result: type) Result {
    return switch (@typeInfo(Result)) {
        .void => {},
        else => .{},
    };
}

test "generic visitor forwards tagged values" {
    const V = union(enum) { number: u32, none };
    const Handler = struct {
        fn visit(_: @This(), value: V) u32 {
            return switch (value) {
                .number => |number| number,
                .none => 0,
            };
        }
    };
    const std = @import("std");
    try std.testing.expectEqual(@as(u32, 7), visit(V{ .number = 7 }, Handler{}));
}
