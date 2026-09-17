// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Compatibility surface for the bundled `picosha2.h`, backed by Zig's
//! standard-library SHA-256 implementation.

const std = @import("std");

pub const digest_size: usize = 32;

pub const Hash256 = struct {
    state: std.crypto.hash.sha2.Sha256 = std.crypto.hash.sha2.Sha256.init(.{}),

    pub fn init() Hash256 {
        return .{};
    }

    pub fn process(self: *Hash256, input: []const u8) void {
        self.state.update(input);
    }

    pub fn finish(self: *Hash256) [digest_size]u8 {
        var output: [digest_size]u8 = undefined;
        self.state.final(&output);
        return output;
    }
};

pub fn hash256(input: []const u8) [digest_size]u8 {
    var output: [digest_size]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(input, &output, .{});
    return output;
}

pub fn hash256Hex(input: []const u8) [digest_size * 2]u8 {
    const digest = hash256(input);
    return std.fmt.bytesToHex(digest, .lower);
}

test "SHA-256 compatibility vectors" {
    try std.testing.expectEqualStrings(
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        &hash256Hex(""),
    );
    try std.testing.expectEqualStrings(
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        &hash256Hex("abc"),
    );
}
