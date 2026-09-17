// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! ABI function-selector helpers from `FunctionSelector.h`.

const std = @import("std");
const fixed_hash = @import("fixed_hash.zig");
const keccak = @import("keccak256.zig");

pub const H32 = fixed_hash.FixedHash(4);

pub fn selectorFromSignatureH32(signature: []const u8) H32 {
    const digest = keccak.keccak256(signature);
    return H32.fromHash(32, &digest, .align_left);
}

pub fn selectorFromSignatureU32(signature: []const u8) u32 {
    const selector = selectorFromSignatureH32(signature);
    return selector.toInteger();
}

pub fn selectorFromSignatureU256(signature: []const u8) u256 {
    return @as(u256, selectorFromSignatureU32(signature)) << 224;
}

test "test() selector matches the upstream ABI vectors" {
    const selector = selectorFromSignatureH32("test()");
    try std.testing.expectEqualStrings("f8a8fd6d", &(selector.hex()));
    try std.testing.expectEqual(@as(u32, 0xf8a8fd6d), selectorFromSignatureU32("test()"));
    try std.testing.expectEqual(
        @as(u256, 0xf8a8fd6d) << 224,
        selectorFromSignatureU256("test()"),
    );
}
