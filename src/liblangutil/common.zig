// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `liblangutil/Common.h`.

const std = @import("std");

pub inline fn isDecimalDigit(c: u8) bool {
    return c >= '0' and c <= '9';
}

pub inline fn isHexDigit(c: u8) bool {
    return isDecimalDigit(c) or
        (c >= 'a' and c <= 'f') or
        (c >= 'A' and c <= 'F');
}

pub inline fn isWhiteSpace(c: u8) bool {
    return c == ' ' or c == '\n' or c == '\t' or c == '\r';
}

pub inline fn isIdentifierStart(c: u8) bool {
    return c == '_' or c == '$' or
        (c >= 'a' and c <= 'z') or
        (c >= 'A' and c <= 'Z');
}

pub inline fn isIdentifierPart(c: u8) bool {
    return isIdentifierStart(c) or isDecimalDigit(c);
}

pub inline fn hexValue(c: u8) i8 {
    if (c >= '0' and c <= '9') return @intCast(c - '0');
    if (c >= 'a' and c <= 'f') return @intCast(c - 'a' + 10);
    if (c >= 'A' and c <= 'F') return @intCast(c - 'A' + 10);
    return -1;
}

test "character classes preserve ASCII-only scanner behavior" {
    for (0..256) |raw| {
        const c: u8 = @intCast(raw);
        try std.testing.expectEqual(c >= '0' and c <= '9', isDecimalDigit(c));
        try std.testing.expectEqual(
            (c >= '0' and c <= '9') or
                (c >= 'a' and c <= 'f') or
                (c >= 'A' and c <= 'F'),
            isHexDigit(c),
        );
        try std.testing.expectEqual(
            c == ' ' or c == '\n' or c == '\t' or c == '\r',
            isWhiteSpace(c),
        );
    }
    try std.testing.expectEqual(@as(i8, 0), hexValue('0'));
    try std.testing.expectEqual(@as(i8, 10), hexValue('a'));
    try std.testing.expectEqual(@as(i8, 15), hexValue('F'));
    try std.testing.expectEqual(@as(i8, -1), hexValue('g'));
}
