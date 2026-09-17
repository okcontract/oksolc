// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! UnixFS/DAG-PB IPFS hashing compatible with `ipfs add` and `IpfsHash.cpp`.

const std = @import("std");
const sha256 = @import("picosha2.zig");

pub const multihash_size: usize = 34;
pub const Multihash = [multihash_size]u8;

const Chunk = struct {
    hash: Multihash = [_]u8{0} ** multihash_size,
    size: usize = 0,
    block_size: usize = 0,
};

fn appendVarint(output: *std.ArrayList(u8), allocator: std.mem.Allocator, input: usize) !void {
    var value = input;
    while (value > 0x7f) : (value >>= 7) {
        try output.append(allocator, @intCast(0x80 | (value & 0x7f)));
    }
    try output.append(allocator, @intCast(value));
}

fn encodeHash(input: []const u8) Multihash {
    var result: Multihash = undefined;
    result[0] = 0x12;
    result[1] = 0x20;
    const digest = sha256.hash256(input);
    @memcpy(result[2..], &digest);
    return result;
}

fn combineLinks(
    allocator: std.mem.Allocator,
    links: []const Chunk,
) !Chunk {
    var link_data: std.ArrayList(u8) = .empty;
    defer link_data.deinit(allocator);
    var lengths: std.ArrayList(u8) = .empty;
    defer lengths.deinit(allocator);
    var chunk: Chunk = .{};

    for (links) |link| {
        chunk.size = try std.math.add(usize, chunk.size, link.size);
        chunk.block_size = try std.math.add(usize, chunk.block_size, link.block_size);

        var encoded_link: std.ArrayList(u8) = .empty;
        defer encoded_link.deinit(allocator);
        try encoded_link.append(allocator, 0x0a);
        try appendVarint(&encoded_link, allocator, link.hash.len);
        try encoded_link.appendSlice(allocator, &link.hash);
        try encoded_link.appendSlice(allocator, &.{ 0x12, 0x00, 0x18 });
        try appendVarint(&encoded_link, allocator, link.block_size);

        try link_data.append(allocator, 0x12);
        try appendVarint(&link_data, allocator, encoded_link.items.len);
        try link_data.appendSlice(allocator, encoded_link.items);

        try lengths.append(allocator, 0x20);
        try appendVarint(&lengths, allocator, link.size);
    }

    var unixfs: std.ArrayList(u8) = .empty;
    defer unixfs.deinit(allocator);
    try unixfs.appendSlice(allocator, &.{ 0x08, 0x02, 0x18 });
    try appendVarint(&unixfs, allocator, chunk.size);
    try unixfs.appendSlice(allocator, lengths.items);

    var block: std.ArrayList(u8) = .empty;
    defer block.deinit(allocator);
    try block.appendSlice(allocator, link_data.items);
    try block.append(allocator, 0x0a);
    try appendVarint(&block, allocator, unixfs.items.len);
    try block.appendSlice(allocator, unixfs.items);

    chunk.block_size = try std.math.add(usize, chunk.block_size, block.items.len);
    chunk.hash = encodeHash(block.items);
    return chunk;
}

fn buildNextLevel(
    allocator: std.mem.Allocator,
    current: []const Chunk,
) !std.ArrayList(Chunk) {
    const max_children: usize = 174;
    var next: std.ArrayList(Chunk) = .empty;
    errdefer next.deinit(allocator);
    var start: usize = 0;
    while (start < current.len) : (start += max_children) {
        const end = @min(start + max_children, current.len);
        try next.append(allocator, try combineLinks(allocator, current[start..end]));
    }
    return next;
}

pub fn ipfsHash(allocator: std.mem.Allocator, input: []const u8) !Multihash {
    const maximum_chunk_size: usize = 256 * 1024;
    const chunk_count = @max(@as(usize, 1), (input.len + maximum_chunk_size - 1) / maximum_chunk_size);
    var chunks: std.ArrayList(Chunk) = .empty;
    defer chunks.deinit(allocator);
    try chunks.ensureTotalCapacity(allocator, chunk_count);

    for (0..chunk_count) |chunk_index| {
        const start = chunk_index * maximum_chunk_size;
        const end = @min(start + maximum_chunk_size, input.len);
        const bytes = input[start..end];

        var unixfs: std.ArrayList(u8) = .empty;
        defer unixfs.deinit(allocator);
        try unixfs.appendSlice(allocator, &.{ 0x08, 0x02 });
        if (bytes.len != 0) {
            try unixfs.append(allocator, 0x12);
            try appendVarint(&unixfs, allocator, bytes.len);
            try unixfs.appendSlice(allocator, bytes);
        }
        try unixfs.append(allocator, 0x18);
        try appendVarint(&unixfs, allocator, bytes.len);

        var block: std.ArrayList(u8) = .empty;
        defer block.deinit(allocator);
        try block.append(allocator, 0x0a);
        try appendVarint(&block, allocator, unixfs.items.len);
        try block.appendSlice(allocator, unixfs.items);
        chunks.appendAssumeCapacity(.{
            .hash = encodeHash(block.items),
            .size = bytes.len,
            .block_size = block.items.len,
        });
    }

    while (chunks.items.len != 1) {
        const next = try buildNextLevel(allocator, chunks.items);
        chunks.deinit(allocator);
        chunks = next;
    }
    return chunks.items[0].hash;
}

pub fn base58EncodeAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
) std.mem.Allocator.Error![]u8 {
    const alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    if (input.len == 0) return allocator.alloc(u8, 0);

    const working = try allocator.dupe(u8, input);
    defer allocator.free(working);
    var first_nonzero: usize = 0;
    while (first_nonzero < working.len and working[first_nonzero] == 0) first_nonzero += 1;
    var reversed: std.ArrayList(u8) = .empty;
    errdefer reversed.deinit(allocator);
    while (first_nonzero < working.len) {
        var remainder: u16 = 0;
        for (working[first_nonzero..]) |*byte| {
            const accumulator = remainder * 256 + byte.*;
            byte.* = @intCast(accumulator / 58);
            remainder = accumulator % 58;
        }
        try reversed.append(allocator, alphabet[remainder]);
        while (first_nonzero < working.len and working[first_nonzero] == 0) first_nonzero += 1;
    }
    for (input) |byte| {
        if (byte != 0) break;
        try reversed.append(allocator, alphabet[0]);
    }
    std.mem.reverse(u8, reversed.items);
    return reversed.toOwnedSlice(allocator);
}

pub fn ipfsHashBase58Alloc(
    allocator: std.mem.Allocator,
    input: []const u8,
) ![]u8 {
    const digest = try ipfsHash(allocator, input);
    return base58EncodeAlloc(allocator, &digest);
}

test "IPFS UnixFS hashes match upstream small and chunked vectors" {
    const Case = struct { length: usize, literal: ?[]const u8 = null, expected: []const u8 };
    const cases = [_]Case{
        .{ .length = 0, .literal = "", .expected = "QmbFMke1KXqnYyBBWxB74N4c5SBnJMVAiMNRcGu6x1AwQH" },
        .{ .length = 1, .literal = "x", .expected = "QmULKig5Fxrs2sC4qt9nNduucXfb92AFYQ6Hi3YRqDmrYC" },
        .{ .length = 9, .literal = "Solidity\n", .expected = "QmSsm9M7PQRBnyiz1smizk8hZw3URfk8fSeHzeTo3oZidS" },
        .{ .length = 200, .expected = "QmSXR1N23uWzsANi8wpxMPw5dmmhqBVUAb4hUrHVLpNaMr" },
        .{ .length = 100000, .expected = "QmYgKa25YqEGpQmmZtPPFMNK3kpqqneHk6nMSEUYryEX1C" },
        .{ .length = 256 * 1024 + 1, .expected = "QmbVuw4C4vcmVKqxoWtgDVobvcHrSn51qsmQmyxjk4sB2Q" },
    };
    for (cases) |case| {
        const zeros = if (case.literal == null)
            try std.testing.allocator.alloc(u8, case.length)
        else
            null;
        defer if (zeros) |storage| std.testing.allocator.free(storage);
        if (zeros) |storage| @memset(storage, 0);
        const input = case.literal orelse zeros.?;
        const actual = try ipfsHashBase58Alloc(std.testing.allocator, input);
        defer std.testing.allocator.free(actual);
        try std.testing.expectEqualStrings(case.expected, actual);
    }
}
