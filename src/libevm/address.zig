// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Allocation-free CREATE/CREATE2 address calculation, shared by concrete and
//! abstract execution. These functions calculate candidate addresses only:
//! gas, balance, nonce-limit, collision, and code validation belong to the
//! caller's execution semantics. A result establishes neither successful
//! deployment nor permission to resolve a later call to that account.

const std = @import("std");
const Keccak = @import("../libsolutil/keccak256.zig");

/// The nonce is the creator's value before the CREATE attempt increments it.
/// Osaka bounds account nonces to u64. Even maxInt(u64) has an address formula,
/// although CREATE must fail at that nonce under EIP-2681.
pub fn create(creator: u160, nonce: u64) u160 {
    // RLP([address, nonce]): one list byte, 21 address bytes, and at most
    // nine nonce bytes. Every possible payload fits the short-list form.
    var preimage: [31]u8 = undefined;
    preimage[1] = 0x94;
    std.mem.writeInt(u160, preimage[2..22], creator, .big);
    const len: usize = if (nonce <= 0x7f) len: {
        preimage[22] = if (nonce == 0) 0x80 else @intCast(nonce);
        break :len 23;
    } else len: {
        var bytes: [8]u8 = undefined;
        std.mem.writeInt(u64, &bytes, nonce, .big);
        const count: usize = (64 - @as(usize, @clz(nonce)) + 7) / 8;
        preimage[22] = 0x80 + @as(u8, @intCast(count));
        @memcpy(preimage[23..][0..count], bytes[8 - count ..]);
        break :len 23 + count;
    };
    preimage[0] = 0xc0 + @as(u8, @intCast(len - 1));
    return hashAddress(preimage[0..len]);
}

/// EIP-1014 hashes the exact initcode, including encoded constructor arguments.
/// A source digest, runtime template, or deployed bytecode hash is not a valid
/// substitute. Accepting an existing digest avoids rehashing shared initcode.
pub fn create2(creator: u160, salt: u256, init_code_hash: Keccak.H256) u160 {
    var preimage: [85]u8 = undefined;
    preimage[0] = 0xff;
    std.mem.writeInt(u160, preimage[1..21], creator, .big);
    std.mem.writeInt(u256, preimage[21..53], salt, .big);
    @memcpy(preimage[53..85], &init_code_hash.storage);
    return hashAddress(&preimage);
}

fn hashAddress(preimage: []const u8) u160 {
    const digest = Keccak.keccak256(preimage);
    return std.mem.readInt(u160, digest.storage[12..32], .big);
}
