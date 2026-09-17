// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Legacy and binary-Merkle-tree Swarm hashing from `SwarmHash.cpp`.

const std = @import("std");
const fixed_hash = @import("fixed_hash.zig");
const keccak = @import("keccak256.zig");

pub const H256 = fixed_hash.H256;

fn littleEndianSize(size: usize) [8]u8 {
    var encoded: [8]u8 = undefined;
    std.mem.writeInt(u64, &encoded, @intCast(size), .little);
    return encoded;
}

fn hashWithSize(data: []const u8, logical_size: usize) H256 {
    const encoded_size = littleEndianSize(logical_size);
    var hasher = std.crypto.hash.sha3.Keccak256.init(.{});
    hasher.update(&encoded_size);
    hasher.update(data);
    var output = H256.init();
    hasher.final(output.mutableArray());
    return output;
}

fn legacyIntermediate(
    allocator: std.mem.Allocator,
    input: []const u8,
) std.mem.Allocator.Error!H256 {
    if (input.len <= 0x1000) return hashWithSize(input, input.len);

    var maximum_represented_size: usize = 0x1000;
    while (maximum_represented_size <= (input.len - 1) / (0x1000 / 32)) {
        maximum_represented_size *= 0x1000 / 32;
    }
    var inner_nodes: std.ArrayList(u8) = .empty;
    defer inner_nodes.deinit(allocator);
    var offset: usize = 0;
    while (offset < input.len) : (offset += maximum_represented_size) {
        const end = @min(offset + maximum_represented_size, input.len);
        const child = try legacyIntermediate(allocator, input[offset..end]);
        try inner_nodes.appendSlice(allocator, child.bytes());
    }
    return hashWithSize(inner_nodes.items, input.len);
}

pub fn bzzr0Hash(allocator: std.mem.Allocator, input: []const u8) std.mem.Allocator.Error!H256 {
    return legacyIntermediate(allocator, input);
}

fn bmtHash(data: []const u8) H256 {
    if (data.len <= 64) return keccak.keccak256(data);
    const middle = data.len / 2;
    const left = bmtHash(data[0..middle]);
    const right = bmtHash(data[middle..]);
    var children: [64]u8 = undefined;
    @memcpy(children[0..32], left.bytes());
    @memcpy(children[32..], right.bytes());
    return keccak.keccak256(&children);
}

fn chunkHash(data: []const u8, force_higher_level: bool) H256 {
    var data_to_hash = [_]u8{0} ** 0x1000;
    if (data.len < 0x1000 or (data.len == 0x1000 and !force_higher_level)) {
        @memcpy(data_to_hash[0..data.len], data);
    } else {
        var maximum_represented_size: usize = 0x1000;
        while (maximum_represented_size <= (data.len - 1) / (0x1000 / 32)) {
            maximum_represented_size *= 0x1000 / 32;
        }
        const force_higher = maximum_represented_size > 0x1000;
        var output_offset: usize = 0;
        var input_offset: usize = 0;
        while (input_offset < data.len) : (input_offset += maximum_represented_size) {
            const end = @min(input_offset + maximum_represented_size, data.len);
            const child = chunkHash(data[input_offset..end], force_higher);
            @memcpy(data_to_hash[output_offset..][0..32], child.bytes());
            output_offset += 32;
        }
        std.debug.assert(output_offset <= data_to_hash.len);
    }

    const root = bmtHash(&data_to_hash);
    return hashWithSize(root.bytes(), data.len);
}

pub fn bzzr1Hash(input: []const u8) H256 {
    if (input.len == 0) return H256.init();
    return chunkHash(input, false);
}

test "Swarm hashes match legacy and BMT boundary vectors" {
    const LegacyCase = struct { length: usize, expected: []const u8 };
    const legacy_cases = [_]LegacyCase{
        .{ .length = 0, .expected = "011b4d03dd8c01f1049143cf9c4c817e4b167f1d1b83e5c6f0f10d89ba1e7bce" },
        .{ .length = 0x1000 - 1, .expected = "32f0faabc4265ac238cd945087133ce3d7e9bb2e536053a812b5373c54043adb" },
        .{ .length = 0x1000, .expected = "411dd45de7246e94589ff5888362c41e85bd3e582a92d0fda8f0e90b76439bec" },
        .{ .length = 0x1000 + 1, .expected = "69754a0098432bbc2e84fe1205276870748a61a065ab6ef44d6a2e7b13ce044d" },
    };
    for (legacy_cases) |case| {
        const input = try std.testing.allocator.alloc(u8, case.length);
        defer std.testing.allocator.free(input);
        @memset(input, 0);
        const actual = try bzzr0Hash(std.testing.allocator, input);
        try std.testing.expectEqualStrings(case.expected, &actual.hex());
    }

    const BmtCase = struct { length: usize, expected: []const u8 };
    const bmt_cases = [_]BmtCase{
        .{ .length = 1, .expected = "fe60ba40b87599ddfb9e8947c1c872a4a1a5b56f7d1b80f0a646005b38db52a5" },
        .{ .length = 64, .expected = "24090f674316c306ea2a98bdd08f042d6f776d0ae1c23b27fca52750a9c7d4e5" },
        .{ .length = 65, .expected = "6ab1eaa91095215e30cacf47131d06ce5e9fc01611e406409705e190ee4440c6" },
        .{ .length = 4096, .expected = "09ae927d0f3aaa37324df178928d3826820f3dd3388ce4aaebfc3af410bde23a" },
        .{ .length = 4097, .expected = "c082943c4cb8a97c67947f290f5421cf4c61d021eb303c8df77de6fe208df516" },
    };
    for (bmt_cases) |case| {
        const input = try std.testing.allocator.alloc(u8, case.length);
        defer std.testing.allocator.free(input);
        @memset(input, 0);
        const actual = bzzr1Hash(input);
        try std.testing.expectEqualStrings(case.expected, &actual.hex());
    }
}
