// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Authenticated inspection receipts, independent of compiler artifact caches.
//! A receipt binds the executable/context, exact request/output and read set.
const std = @import("std");
const Store = @import("store.zig");
const Hmac = std.crypto.auth.hmac.sha2.HmacSha256;
pub const Key = @import("solidity").incremental.CacheAuthenticationKey;

pub fn seal(key: Key, context: []const u8, request: []const u8, output: []const u8, manifest: []const u8) [64]u8 {
    var mac = Hmac.init(&key);
    mac.update("oksolc.browser.resume.v1\x00");
    // Fixed-size hashes frame all fields unambiguously. Recompute from actual
    // stored bodies; SQLite's unauthenticated digest columns are insufficient.
    for ([_][]const u8{ context, request, output, manifest }) |field| {
        const hash = Store.digest(field);
        mac.update(&hash);
    }
    var tag: [Hmac.mac_length]u8 = undefined;
    mac.final(&tag);
    return std.fmt.bytesToHex(tag, .lower);
}

pub fn authentic(key: Key, candidate: Store.Resume) bool {
    const expected = seal(key, candidate.receipt.context, candidate.request, candidate.output, candidate.receipt.manifest);
    const actual: *const [64]u8 = if (candidate.receipt.seal.len == 64) candidate.receipt.seal[0..64] else return false;
    return std.crypto.timing_safe.eql([64]u8, expected, actual.*);
}

test "resume receipt authenticates actual bodies, context, manifest and key" {
    const key: Key = [_]u8{0x37} ** 32;
    const tag = seal(key, "context", "request", "output", "manifest");
    var candidate: Store.Resume = .{ .id = 1, .request = "request", .output = "output", .receipt = .{ .context = "context", .manifest = "manifest", .seal = &tag } };
    try std.testing.expect(authentic(key, candidate));
    try std.testing.expect(!authentic([_]u8{0x38} ** 32, candidate));
    inline for (.{ "request", "output" }) |field| {
        var altered = candidate;
        @field(altered, field) = "changed";
        try std.testing.expect(!authentic(key, altered));
    }
    inline for (.{ "context", "manifest", "seal" }) |field| {
        var altered = candidate;
        @field(altered.receipt, field) = "changed";
        try std.testing.expect(!authentic(key, altered));
    }
    candidate.id = 2; // SQL identity is not part of semantic input/output.
    try std.testing.expect(authentic(key, candidate));
}
