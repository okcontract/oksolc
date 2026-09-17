// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Keccak-256 implementation corresponding to `Keccak256.cpp`.

const std = @import("std");
const fixed_hash = @import("fixed_hash.zig");

pub const H256 = fixed_hash.H256;

pub fn keccak256(input: []const u8) H256 {
    var output = H256.init();
    std.crypto.hash.sha3.Keccak256.hash(input, output.mutableArray(), .{});
    return output;
}

test "Keccak-256 matches the upstream empty, zero, and string vectors" {
    const Case = struct { input: []const u8, expected: []const u8 };
    const cases = [_]Case{
        .{ .input = "", .expected = "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" },
        .{ .input = &.{0}, .expected = "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a" },
        .{ .input = &.{ 0, 0 }, .expected = "54a8c0ab653c15bfb48b47fd011ba2b9617af01cb45cab344acd57c924d56798" },
        .{ .input = "test", .expected = "9c22ff5f21f0b81b113e63f7db6da94fedef11b2119b4088b89664fb9a3cb658" },
        .{ .input = "longer test string", .expected = "47bed17bfbbc08d6b5a0f603eff1b3e932c37c10b865847a7bc73d55b260f32a" },
    };
    for (cases) |case| {
        const actual = keccak256(case.input);
        try std.testing.expectEqualStrings(case.expected, &(actual.hex()));
    }
}
