// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `libsolutil/ErrorCodes.h`.

const std = @import("std");

pub const PanicCode = enum(c_int) {
    generic = 0x00,
    assert = 0x01,
    under_overflow = 0x11,
    division_by_zero = 0x12,
    enum_conversion_error = 0x21,
    storage_encoding_error = 0x22,
    empty_array_pop = 0x31,
    array_out_of_bounds = 0x32,
    resource_error = 0x41,
    invalid_internal_function = 0x51,
};

test "panic codes retain their externally observed ABI values" {
    const expected = [_]c_int{ 0x00, 0x01, 0x11, 0x12, 0x21, 0x22, 0x31, 0x32, 0x41, 0x51 };
    const actual = [_]PanicCode{
        .generic,
        .assert,
        .under_overflow,
        .division_by_zero,
        .enum_conversion_error,
        .storage_encoding_error,
        .empty_array_pop,
        .array_out_of_bounds,
        .resource_error,
        .invalid_internal_function,
    };
    for (actual, expected) |code, value| {
        try std.testing.expectEqual(value, @intFromEnum(code));
    }
    try std.testing.expectEqual(@sizeOf(c_int), @sizeOf(PanicCode));
    const tag_type = @typeInfo(PanicCode).@"enum".tag_type;
    try std.testing.expectEqual(
        std.builtin.Signedness.signed,
        @typeInfo(tag_type).int.signedness,
    );
}
