// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Value/arena-oriented translation of `DebugData.h`.

const std = @import("std");
const SourceLocation = @import("source_location.zig").SourceLocation;

pub const DebugData = struct {
    native_location: SourceLocation = .{},
    origin_location: SourceLocation = .{},
    ast_id: ?i64 = null,

    pub fn create(
        allocator: std.mem.Allocator,
        native_location: SourceLocation,
        origin_location: SourceLocation,
        ast_id: ?i64,
    ) !*const DebugData {
        const value = try allocator.create(DebugData);
        value.* = .{
            .native_location = native_location,
            .origin_location = origin_location,
            .ast_id = ast_id,
        };
        return value;
    }

    pub fn destroy(pointer: *const DebugData, allocator: std.mem.Allocator) void {
        allocator.destroy(@constCast(pointer));
    }
};

/// Stable immutable empty value, matching the cached shared pointer upstream.
pub const empty: DebugData = .{};

test "debug data retains both locations and AST identity" {
    const value = try DebugData.create(
        std.testing.allocator,
        .{ .start = 1, .end = 2, .source_name = "native.yul" },
        .{ .start = 3, .end = 5, .source_name = "origin.sol" },
        17,
    );
    defer DebugData.destroy(value, std.testing.allocator);
    try std.testing.expectEqual(@as(?i64, 17), value.ast_id);
    try std.testing.expectEqualStrings("origin.sol", value.origin_location.source_name.?);
}
