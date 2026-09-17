// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `libsolutil/UTF8.cpp`.

const std = @import("std");

fn isWellFormed(byte1: u8, byte2: u8) bool {
    if (byte1 == 0xc0 or byte1 == 0xc1)
        return false
    else if (byte1 >= 0xc2 and byte1 <= 0xdf)
        return true
    else if (byte1 == 0xe0)
        return byte2 >= 0xa0
    else if (byte1 >= 0xe1 and byte1 <= 0xec)
        return true
    else if (byte1 == 0xed)
        return byte2 <= 0x9f
    else if (byte1 == 0xee or byte1 == 0xef)
        return true
    else if (byte1 == 0xf0)
        return byte2 >= 0x90
    else if (byte1 >= 0xf1 and byte1 <= 0xf3)
        return true
    else if (byte1 == 0xf4)
        return byte2 <= 0x8f;
    return false;
}

/// Preserves the upstream output-parameter contract: `invalid_position` is
/// written only for invalid input. The reported position intentionally retains
/// the upstream validator's historical scan-forward behavior.
pub fn validateUTF8(input: []const u8, invalid_position: *usize) bool {
    var valid = true;
    var index: usize = 0;

    while (index < input.len) : (index += 1) {
        if (input[index] < 0x80) continue;

        var count: usize = 0;
        if (input[index] >= 0xc0 and input[index] <= 0xdf)
            count = 1
        else if (input[index] >= 0xe0 and input[index] <= 0xef)
            count = 2
        else if (input[index] >= 0xf0 and input[index] <= 0xf7)
            count = 3;

        if (count == 0) {
            valid = false;
            break;
        }
        if (count >= input.len - index) {
            valid = false;
            break;
        }

        var continuation_index: usize = 0;
        while (continuation_index < count) : (continuation_index += 1) {
            index += 1;
            if ((input[index] & 0xc0) != 0x80) {
                valid = false;
                break;
            }
            if (continuation_index == 0 and !isWellFormed(input[index - 1], input[index])) {
                valid = false;
                break;
            }
        }
    }

    if (valid) return true;
    invalid_position.* = index;
    return false;
}

pub fn isValidUTF8(input: []const u8) bool {
    var invalid_position: usize = undefined;
    return validateUTF8(input, &invalid_position);
}

fn expectValid(bytes: []const u8) !void {
    var untouched: usize = 0xfeedface;
    try std.testing.expect(validateUTF8(bytes, &untouched));
    try std.testing.expectEqual(@as(usize, 0xfeedface), untouched);
}

fn expectInvalid(bytes: []const u8, expected_position: usize) !void {
    var actual_position: usize = undefined;
    try std.testing.expect(!validateUTF8(bytes, &actual_position));
    try std.testing.expectEqual(expected_position, actual_position);
}

test "valid byte sequences match the upstream suite" {
    const cases = [_][]const u8{
        &.{0x00},
        &.{0x20},
        &.{0x7f},
        &.{ 0xc2, 0x81 },
        &.{ 0xdf, 0x81 },
        &.{ 0xe0, 0xa0, 0x81 },
        &.{ 0xe1, 0x80, 0x81 },
        &.{ 0xec, 0x80, 0x81 },
        &.{ 0xed, 0x80, 0x81 },
        &.{ 0xee, 0x80, 0x81 },
        &.{ 0xef, 0x80, 0x81 },
        &.{ 0xf0, 0x90, 0x80, 0x81 },
        &.{ 0xf3, 0x80, 0x80, 0x81 },
        &.{ 0xf2, 0x80, 0x80, 0x81 },
        &.{ 0xf4, 0x8e, 0x80, 0x81 },
    };
    for (cases) |case| try expectValid(case);
}

test "invalid positions match the upstream suite" {
    const Case = struct {
        bytes: []const u8,
        position: usize,
    };
    const cases = [_]Case{
        .{ .bytes = &.{0x80}, .position = 0 },
        .{ .bytes = &.{0xa0}, .position = 0 },
        .{ .bytes = &.{0xc0}, .position = 0 },
        .{ .bytes = &.{0xc1}, .position = 0 },
        .{ .bytes = &.{0xc2}, .position = 0 },
        .{ .bytes = &.{ 0xe0, 0x80, 0x81 }, .position = 2 },
        .{ .bytes = &.{ 0xe1, 0x80 }, .position = 0 },
        .{ .bytes = &.{ 0xec, 0x80 }, .position = 0 },
        .{ .bytes = &.{ 0xf0, 0x8f, 0x80, 0x01 }, .position = 2 },
        .{ .bytes = &.{ 0xf1, 0x80, 0x80 }, .position = 0 },
        .{ .bytes = &.{ 0xf4, 0x90, 0x80, 0x81 }, .position = 2 },
        .{ .bytes = &.{0xf8}, .position = 0 },
        .{ .bytes = &.{0xf9}, .position = 0 },
    };
    for (cases) |case| try expectInvalid(case.bytes, case.position);
}
