// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Canonical hashing primitives for persistent incremental-compiler keys.
//!
//! The byte format is independent of Zig's native layout:
//! integers are fixed-width big-endian values and every field is framed with
//! an explicit tag and length.

const std = @import("std");
const FixedHash = @import("../libsolutil/fixed_hash.zig");

pub const H256 = FixedHash.H256;

const format_magic = "zsolc.incremental.key\x00";

pub const KeyHasher = struct {
    state: std.crypto.hash.sha3.Keccak256,

    pub fn init(domain: []const u8, schema_version: u32) KeyHasher {
        var result: KeyHasher = .{
            .state = std.crypto.hash.sha3.Keccak256.init(.{}),
        };
        result.state.update(format_magic);
        result.updateInt(u32, schema_version);
        result.updateLength(domain.len);
        result.state.update(domain);
        return result;
    }

    pub fn addBytes(self: *KeyHasher, tag: u8, value: []const u8) void {
        self.state.update(&.{tag});
        self.updateLength(value.len);
        self.state.update(value);
    }

    pub fn addDigest(self: *KeyHasher, tag: u8, value: *const H256) void {
        self.addBytes(tag, value.bytes());
    }

    pub fn addBool(self: *KeyHasher, tag: u8, value: bool) void {
        self.addBytes(tag, &.{@intFromBool(value)});
    }

    pub fn addU8(self: *KeyHasher, tag: u8, value: u8) void {
        self.addBytes(tag, &.{value});
    }

    pub fn addU32(self: *KeyHasher, tag: u8, value: u32) void {
        var encoded: [@sizeOf(u32)]u8 = undefined;
        std.mem.writeInt(u32, &encoded, value, .big);
        self.addBytes(tag, &encoded);
    }

    pub fn addU64(self: *KeyHasher, tag: u8, value: u64) void {
        var encoded: [@sizeOf(u64)]u8 = undefined;
        std.mem.writeInt(u64, &encoded, value, .big);
        self.addBytes(tag, &encoded);
    }

    pub fn finish(self: *KeyHasher) H256 {
        var output = H256.init();
        self.state.final(output.mutableArray());
        self.* = undefined;
        return output;
    }

    fn updateLength(self: *KeyHasher, length: usize) void {
        self.updateInt(u64, @intCast(length));
    }

    fn updateInt(self: *KeyHasher, comptime T: type, value: T) void {
        var encoded: [@sizeOf(T)]u8 = undefined;
        std.mem.writeInt(T, &encoded, value, .big);
        self.state.update(&encoded);
    }
};

test "key hasher frames domains, versions, fields, and lengths" {
    var first = KeyHasher.init("test-a", 1);
    first.addBytes(1, "ab");
    first.addBytes(2, "c");
    const first_digest = first.finish();

    var same = KeyHasher.init("test-a", 1);
    same.addBytes(1, "ab");
    same.addBytes(2, "c");
    const same_digest = same.finish();
    try std.testing.expect(first_digest.eql(&same_digest));

    var differently_framed = KeyHasher.init("test-a", 1);
    differently_framed.addBytes(1, "a");
    differently_framed.addBytes(2, "bc");
    const differently_framed_digest = differently_framed.finish();
    try std.testing.expect(!first_digest.eql(&differently_framed_digest));

    var other_domain = KeyHasher.init("test-b", 1);
    other_domain.addBytes(1, "ab");
    other_domain.addBytes(2, "c");
    const other_domain_digest = other_domain.finish();
    try std.testing.expect(!first_digest.eql(&other_domain_digest));

    var other_version = KeyHasher.init("test-a", 2);
    other_version.addBytes(1, "ab");
    other_version.addBytes(2, "c");
    const other_version_digest = other_version.finish();
    try std.testing.expect(!first_digest.eql(&other_version_digest));
}
