// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `libsolutil/LEB128.h`.

const std = @import("std");
const cxx_compat = @import("cxx_compat");

/// Caller owns the returned bytes and must free them with `allocator`.
pub fn lebEncode(allocator: std.mem.Allocator, value: u64) std.mem.Allocator.Error![]u8 {
    var encoded: cxx_compat.Vector(u8) = .{};
    errdefer encoded.deinit(allocator);

    var remaining = value;
    while (remaining > 0x7f) {
        try encoded.append(allocator, @intCast(0x80 | (remaining & 0x7f)));
        remaining >>= 7;
    }
    try encoded.append(allocator, @intCast(remaining));
    return encoded.toOwnedSlice(allocator);
}

/// Caller owns the returned bytes and must free them with `allocator`.
pub fn lebEncodeSigned(allocator: std.mem.Allocator, value: i64) std.mem.Allocator.Error![]u8 {
    var encoded: cxx_compat.Vector(u8) = .{};
    errdefer encoded.deinit(allocator);

    var remaining = value;
    var more = true;
    while (more) {
        var byte: u8 = @intCast(remaining & 0x7f);
        remaining >>= 7;
        more = !((remaining == 0 and (byte & 0x40) == 0) or
            (remaining == -1 and (byte & 0x40) != 0));
        if (more) byte |= 0x80;
        try encoded.append(allocator, byte);
    }
    return encoded.toOwnedSlice(allocator);
}

test "unsigned examples match the upstream suite" {
    const Case = struct {
        value: u64,
        expected: []const u8,
    };
    const cases = [_]Case{
        .{ .value = 0, .expected = &.{0x00} },
        .{ .value = 1, .expected = &.{0x01} },
        .{ .value = 624485, .expected = &.{ 0xe5, 0x8e, 0x26 } },
    };

    for (cases) |case| {
        const actual = try lebEncode(std.testing.allocator, case.value);
        defer std.testing.allocator.free(actual);
        try std.testing.expectEqualSlices(u8, case.expected, actual);
    }
}

test "signed examples match the upstream suite" {
    const Case = struct {
        value: i64,
        expected: []const u8,
    };
    const cases = [_]Case{
        .{ .value = 0, .expected = &.{0x00} },
        .{ .value = 1, .expected = &.{0x01} },
        .{ .value = -1, .expected = &.{0x7f} },
        .{ .value = -2, .expected = &.{0x7e} },
        .{ .value = 624485, .expected = &.{ 0xe5, 0x8e, 0x26 } },
        .{ .value = -123456, .expected = &.{ 0xc0, 0xbb, 0x78 } },
        .{
            .value = 123456123456,
            .expected = &.{ 0xc0, 0xe4, 0xbb, 0xf4, 0xcb, 0x03 },
        },
        .{
            .value = -123456123456,
            .expected = &.{ 0xc0, 0x9b, 0xc4, 0x8b, 0xb4, 0x7c },
        },
    };

    for (cases) |case| {
        const actual = try lebEncodeSigned(std.testing.allocator, case.value);
        defer std.testing.allocator.free(actual);
        try std.testing.expectEqualSlices(u8, case.expected, actual);
    }
}

fn exerciseAllocationFailure(allocator: std.mem.Allocator) !void {
    const encoded = try lebEncodeSigned(allocator, std.math.minInt(i64));
    defer allocator.free(encoded);
}

test "allocation failure does not leak partial output" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        exerciseAllocationFailure,
        .{},
    );
}
