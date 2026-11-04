// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Map = @FieldType(evm.expression_classes.ExpressionClasses, "expressions");
const Key = @FieldType(Map.KV, "key");
const Context = @typeInfo(@TypeOf(Map.getOrPutContext)).@"fn".param_types[3].?;
const lengths = [_]usize{ 0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 65 };

const Case = struct {
    length: usize,
    alias_equal: bool,
    copied_equal: bool,
    different_length: bool,
    changed_bytes_rejected: usize,
    scalar_changes_rejected: [4]bool,
};
const Capture = struct {
    schema: []const u8 = "oksolc.expression-map-equality.v1",
    arch: []const u8 = @tagName(builtin.cpu.arch),
    backend: []const u8 = @tagName(builtin.zig_backend),
    endian: []const u8 = @tagName(builtin.cpu.arch.endian()),
    scan_bytes: ?usize = if (std.simd.suggestVectorLength(u8)) |n| n else null,
    usize_bytes: usize = @sizeOf(usize),
    unique_u32: bool = std.meta.hasUniqueRepresentation(u32),
    fuzz: bool = builtin.fuzz,
    cases: [lengths.len]Case,
    collision: struct { same_start: bool, same_fingerprint: bool, first: ?u32, second: ?u32, absent: ?u32, size: u32 },
};

fn key(arguments: []const u32) Key {
    return .{ .item_type = .Push, .instruction = 171, .data = 0xffffffffffffffff, .arguments = arguments, .sequence_number = 305419896 };
}

pub fn observe(allocator: std.mem.Allocator) !Capture {
    const ctx: Context = .{};
    var output: Capture = undefined;
    var cases: [lengths.len]Case = undefined;
    // Mutable distinct buffers force the runtime specialization. Every byte
    // position is changed independently, including overlapping tail lanes.
    var left: [66]u32 = undefined;
    var right: [66]u32 = undefined;
    for (&left, &right, 0..) |*a, *b, i| {
        a.* = @as(u32, @intCast(i)) *% 0x9e3779b9;
        b.* = a.*;
    }
    std.mem.doNotOptimizeAway(&left);
    std.mem.doNotOptimizeAway(&right);
    for (lengths, &cases) |len, *result| {
        const a = key(left[0..len]);
        const b = key(right[0..len]);
        result.* = .{ .length = len, .alias_equal = ctx.eql(a, a), .copied_equal = ctx.eql(a, b), .different_length = ctx.eql(a, key(right[0 .. len + 1])), .changed_bytes_rejected = 0, .scalar_changes_rejected = undefined };
        for (0..len) |i| {
            for (0..4) |lane| {
                const mask = @as(u32, 1) << @as(u5, @intCast(lane * 8));
                right[i] ^= mask;
                if (!ctx.eql(a, b)) result.changed_bytes_rejected += 1;
                right[i] ^= mask;
            }
        }
        var altered = b;
        altered.item_type = .Operation;
        result.scalar_changes_rejected[0] = !ctx.eql(a, altered);
        altered = b;
        altered.instruction ^= 1;
        result.scalar_changes_rejected[1] = !ctx.eql(a, altered);
        altered = b;
        altered.data ^= @as(u256, 1) << 255;
        result.scalar_changes_rejected[2] = !ctx.eql(a, altered);
        altered = b;
        altered.sequence_number ^= 1;
        result.scalar_changes_rejected[3] = !ctx.eql(a, altered);
    }
    var map: Map = .empty;
    defer map.deinit(allocator);
    const first = key(left[0..17]);
    const hash = ctx.hash(first);
    var colliding: [2]Key = undefined;
    var found: usize = 0;
    for (1..262144) |n| {
        var candidate = first;
        candidate.data += n;
        const candidate_hash = ctx.hash(candidate);
        if (candidate_hash & 7 != hash & 7 or candidate_hash >> 57 != hash >> 57) continue;
        colliding[found] = candidate;
        found += 1;
        if (found == colliding.len) break;
    }
    if (found != colliding.len) return error.CollisionFixtureExhausted;
    try map.put(allocator, first, 37);
    try map.put(allocator, colliding[0], 53);
    if (map.capacity() != 8) return error.UnexpectedCapacity;
    var copied_query = first;
    copied_query.arguments = right[0..17];
    output = .{ .cases = cases, .collision = .{
        .same_start = ctx.hash(colliding[0]) & 7 == hash & 7 and ctx.hash(colliding[1]) & 7 == hash & 7,
        .same_fingerprint = ctx.hash(colliding[0]) >> 57 == hash >> 57 and ctx.hash(colliding[1]) >> 57 == hash >> 57,
        .first = map.get(copied_query),
        .second = map.get(colliding[0]),
        .absent = map.get(colliding[1]),
        .size = map.size,
    } };
    return output;
}
