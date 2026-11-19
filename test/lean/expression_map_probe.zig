// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Map = @FieldType(evm.expression_classes.ExpressionClasses, "expressions");
const Key = @FieldType(Map.KV, "key");
const Context = @typeInfo(@TypeOf(Map.getOrPutContext)).@"fn".param_types[3].?;

const Trace = struct {
    comparisons: *usize,
    hash_calls: ?*usize = null,
    pub fn hash(self: Trace, query: Key) u64 {
        if (self.hash_calls) |calls| calls.* += 1;
        return (Context{}).hash(query);
    }
    pub fn eql(self: Trace, left: Key, right: Key) bool {
        self.comparisons.* += 1;
        return (Context{}).eql(left, right);
    }
};
const Snapshot = struct { metadata: [8]u8, size: u32, available: u32 };
const Capture = struct {
    schema: []const u8 = "oksolc.expression-map-probe.v1",
    arch: []const u8 = @tagName(builtin.cpu.arch),
    backend: []const u8 = @tagName(builtin.zig_backend),
    hashes: [4]u64,
    wrapped: Snapshot,
    tombstone: Snapshot,
    reused: Snapshot,
    exhausted: Snapshot,
    recycled: Snapshot,
    hit: ?u32,
    missed: ?u32,
    hit_comparisons: usize,
    miss_comparisons: usize,
    reuse_index: usize,
    recycle_index: usize,
    found_existing: bool,
};

fn key(data: u256) Key {
    return .{ .item_type = .Push, .instruction = 171, .data = data, .arguments = &.{}, .sequence_number = 0 };
}
fn snapshot(map: Map) Snapshot {
    var result: Snapshot = .{ .metadata = undefined, .size = map.size, .available = map.available };
    for (&result.metadata, 0..) |*byte, i| byte.* = @bitCast(map.metadata.?[i]);
    return result;
}
fn insert(map: *Map, incoming: Key, id: u32) struct { index: usize, existing: bool } {
    const before = snapshot(map.*);
    const entry = map.getOrPutAssumeCapacity(incoming);
    const after = snapshot(map.*);
    var index: usize = 8;
    for (before.metadata, after.metadata, 0..) |old, new, i| {
        if (old != new) index = i;
    }
    entry.value_ptr.* = id;
    return .{ .index = index, .existing = entry.found_existing };
}

pub fn observe(allocator: std.mem.Allocator) !Capture {
    const ctx: Context = .{};
    var colliding: [4]Key = undefined;
    var hashes: [4]u64 = undefined;
    var found: usize = 0;
    for (0..262144) |n| {
        const candidate = key(n);
        const hash = ctx.hash(candidate);
        if (hash & 7 != 7 or (found != 0 and hash >> 57 != hashes[0] >> 57)) continue;
        colliding[found] = candidate;
        hashes[found] = hash;
        found += 1;
        if (found == colliding.len) break;
    }
    if (found != colliding.len) return error.CollisionFixtureExhausted;
    var map: Map = .empty;
    defer map.deinit(allocator);
    try map.ensureTotalCapacity(allocator, 2);
    if (map.capacity() != 8) return error.UnexpectedCapacity;
    const a = insert(&map, colliding[0], 37);
    const b = insert(&map, colliding[1], 53);
    if (a.index != 7 or b.index != 0 or a.existing or b.existing) return error.WrongWrap;
    const wrapped = snapshot(map);
    if (!map.remove(colliding[0])) return error.MissingRemoval;
    const tombstone = snapshot(map);
    var comparisons: usize = 0;
    const hit = map.getAdapted(colliding[1], Trace{ .comparisons = &comparisons });
    const hit_comparisons = comparisons;
    const reused_entry = insert(&map, colliding[2], 71);
    const reused = snapshot(map);

    // Public insert/remove operations create a full cycle with no free byte.
    // No uninitialized key or value is read and no metadata is forged.
    var full: Map = .empty;
    defer full.deinit(allocator);
    try full.ensureTotalCapacity(allocator, 2);
    for (0..8) |start| {
        var selected: ?Key = null;
        for (0..262144) |n| {
            const candidate = key(n);
            if (ctx.hash(candidate) & 7 == start) {
                selected = candidate;
                break;
            }
        }
        const candidate = selected orelse return error.StartFixtureExhausted;
        _ = insert(&full, candidate, 11);
        if (!full.remove(candidate)) return error.MissingRemoval;
    }
    _ = insert(&full, colliding[0], 37);
    const exhausted = snapshot(full);
    comparisons = 0;
    const missed = full.getAdapted(colliding[3], Trace{ .comparisons = &comparisons });
    const miss_comparisons = comparisons;
    const recycled_entry = insert(&full, colliding[3], 89);
    return .{
        .hashes = hashes,
        .wrapped = wrapped,
        .tombstone = tombstone,
        .reused = reused,
        .exhausted = exhausted,
        .recycled = snapshot(full),
        .hit = hit,
        .missed = missed,
        .hit_comparisons = hit_comparisons,
        .miss_comparisons = miss_comparisons,
        .reuse_index = reused_entry.index,
        .recycle_index = recycled_entry.index,
        .found_existing = reused_entry.existing or recycled_entry.existing,
    };
}

const CallerCase = struct {
    name: []const u8,
    capacity: u32,
    size: u32,
    available: u32,
    metadata_present: bool,
    hash_calls: usize,
    comparisons: usize,
    result: ?u32,
    unchanged: bool,
};

fn observeCall(map: *Map, name: []const u8, query: Key) CallerCase {
    const before = map.*;
    const before_capacity = map.capacity();
    var comparisons: usize = 0;
    var hashes: usize = 0;
    const result = map.getAdapted(query, Trace{ .comparisons = &comparisons, .hash_calls = &hashes });
    return .{
        .name = name,
        .capacity = map.capacity(),
        .size = map.size,
        .available = map.available,
        .metadata_present = map.metadata != null,
        .hash_calls = hashes,
        .comparisons = comparisons,
        .result = result,
        .unchanged = before.metadata == map.metadata and before_capacity == map.capacity() and
            before.size == map.size and before.available == map.available,
    };
}

pub fn observeCaller(allocator: std.mem.Allocator) !struct {
    schema: []const u8 = "oksolc.expression-map-caller.v1",
    hashes: [2]u64,
    cases: [4]CallerCase,
} {
    var map: Map = .empty;
    defer map.deinit(allocator);
    var cases: [4]CallerCase = undefined;
    cases[0] = observeCall(&map, "empty-unallocated", key(0));
    try map.ensureTotalCapacity(allocator, 2);
    cases[1] = observeCall(&map, "empty-allocated", key(0));
    _ = insert(&map, key(0), 37);
    cases[2] = observeCall(&map, "hit", key(0));
    cases[3] = observeCall(&map, "miss", key(1));
    return .{ .hashes = .{ (Context{}).hash(key(0)), (Context{}).hash(key(1)) }, .cases = cases };
}
