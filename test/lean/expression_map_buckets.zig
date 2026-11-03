// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const evm = @import("compiler").libevmasm;
const capture = @import("representative_array_layout.zig");
const Map = @FieldType(evm.expression_classes.ExpressionClasses, "expressions");
const Key = @FieldType(Map.KV, "key");
const Value = @FieldType(Map.KV, "value");
const Metadata = @typeInfo(@typeInfo(@FieldType(Map, "metadata")).optional.child).pointer.child;

const Region = struct { base: usize = 0, bytes: usize = 0, alignment: usize = 0 };

// Unlike the representative-remap fixture, these callbacks forward resize and
// remap unchanged. Only the requested OOM is injected; unexpected calls remain
// visible in the counters and make the acceptance check fail.
const Trace = struct {
    inner: std.mem.Allocator,
    reject: bool = false,
    attempts: usize = 0,
    allocations: usize = 0,
    frees: usize = 0,
    resizes: usize = 0,
    remaps: usize = 0,
    requested: Region = .{},
    released: Region = .{},

    fn allocator(self: *Trace) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{ .alloc = alloc, .resize = resize, .remap = remap, .free = free } };
    }
    fn alloc(ctx: *anyopaque, bytes: usize, alignment: std.mem.Alignment, ra: usize) ?[*]u8 {
        const self: *Trace = @ptrCast(@alignCast(ctx));
        self.attempts += 1;
        const pointer = if (self.reject) null else self.inner.rawAlloc(bytes, alignment, ra);
        self.requested = .{ .base = if (pointer) |p| @intFromPtr(p) else 0, .bytes = bytes, .alignment = alignment.toByteUnits() };
        if (pointer != null) self.allocations += 1;
        return pointer;
    }
    fn resize(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, bytes: usize, ra: usize) bool {
        const self: *Trace = @ptrCast(@alignCast(ctx));
        self.resizes += 1;
        return self.inner.rawResize(memory, alignment, bytes, ra);
    }
    fn remap(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, bytes: usize, ra: usize) ?[*]u8 {
        const self: *Trace = @ptrCast(@alignCast(ctx));
        self.remaps += 1;
        return self.inner.rawRemap(memory, alignment, bytes, ra);
    }
    fn free(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ra: usize) void {
        const self: *Trace = @ptrCast(@alignCast(ctx));
        self.frees += 1;
        self.released = .{ .base = @intFromPtr(memory.ptr), .bytes = memory.len, .alignment = alignment.toByteUnits() };
        self.inner.rawFree(memory, alignment, ra);
    }
};

const Case = struct {
    requested_count: u32,
    oom_error: ?[]const u8 = null,
    oom_request: Region = .{},
    oom_capacity: u32 = 0,
    oom_metadata: usize = 0,
    reserve_error: ?[]const u8 = null,
    insert_error: ?[]const u8 = null,
    allocation: Region = .{},
    capacity: u32 = 0,
    metadata: usize = 0,
    metadata_cleared: bool = false,
    available: u32 = 0,
    empty_lookup: bool = false,
    index: ?usize = null,
    key_pointer: usize = 0,
    value_pointer: usize = 0,
    value: ?u32 = null,
    attempts: usize = 0,
    allocations: usize = 0,
    frees: usize = 0,
    resizes: usize = 0,
    remaps: usize = 0,
    released: Region = .{},
};

const CapacityRequest = struct {
    schema: []const u8 = "oksolc.expression-map-capacity.v1",
    requested_count: u32,
    outcome: ?[]const u8,
    request: Region,
    capacity: u32,
    available: u32,
    count: u32,
    metadata_null: bool,
    unlocked: bool,
    attempts: usize,
    allocations: usize,
    frees: usize,
    resizes: usize,
    remaps: usize,
};

// Exercise the real capacityForSize caller without attempting huge allocations.
// The rejecting allocator still records the exact native request and effects.
fn capacityRequest(backing: std.mem.Allocator, count: u32) CapacityRequest {
    var trace: Trace = .{ .inner = backing, .reject = true };
    var map: Map = .empty;
    const outcome = if (map.ensureTotalCapacity(trace.allocator(), count)) |_| null else |err| @errorName(err);
    const capacity = map.capacity();
    const available = map.available;
    const size = map.count();
    const metadata_null = map.metadata == null;
    const unlocked = !std.debug.runtime_safety or @backingInt(map.pointer_stability.state) == 0;
    map.deinit(trace.allocator());
    return .{ .requested_count = count, .outcome = outcome, .request = trace.requested, .capacity = capacity, .available = available, .count = size, .metadata_null = metadata_null, .unlocked = unlocked, .attempts = trace.attempts, .allocations = trace.allocations, .frees = trace.frees, .resizes = trace.resizes, .remaps = trace.remaps };
}

const KeyAssignment = struct {
    schema: []const u8 = "oksolc.expression-map-key-assignment.v1",
    item_type: u32,
    instruction: u8,
    data_words: [4]u64,
    arguments: [3]u32,
    argument_count: usize,
    argument_pointer_retained: bool,
    sequence_number: u32,
    value_retained: bool,
    neighbor_retained: bool,
    capacity: u32,
    count: u32,
    attempts: usize,
    allocations: usize,
    frees: usize,
};

const EntryAssignment = struct {
    schema: []const u8 = "oksolc.expression-map-entry-assignment.v1",
    key: KeyAssignment,
    id: u32,
};

fn keyObservation(stored: Key, arguments: []const u32, id: u32, neighbor_retained: bool, map: *const Map, trace: *const Trace) KeyAssignment {
    return .{
        .item_type = @intCast(@backingInt(stored.item_type)),
        .instruction = stored.instruction,
        .data_words = .{ @truncate(stored.data), @truncate(stored.data >> 64), @truncate(stored.data >> 128), @truncate(stored.data >> 192) },
        .arguments = stored.arguments[0..3].*,
        .argument_count = stored.arguments.len,
        .argument_pointer_retained = stored.arguments.ptr == arguments[0..].ptr,
        .sequence_number = stored.sequence_number,
        .value_retained = id == 37,
        .neighbor_retained = neighbor_retained,
        .capacity = map.capacity(),
        .count = map.count(),
        .attempts = trace.attempts,
        .allocations = trace.allocations,
        .frees = 0,
    };
}

// Observe assignment through actual bucket pointers. This
// deliberately does not claim that changing a key in place preserves hashing;
// no lookup follows the assignment. The publication/probing proof must supply
// that separate relation. Every field and the borrowed slice identity is read.
fn assignment(backing: std.mem.Allocator, id: ?u32) !EntryAssignment {
    var trace: Trace = .{ .inner = backing };
    var map: Map = .empty;
    var live = true;
    defer if (live) map.deinit(trace.allocator());
    const old: Key = .{ .item_type = .Operation, .instruction = 0, .data = 0, .arguments = &.{}, .sequence_number = 0 };
    const neighbor: Key = .{ .item_type = .Operation, .instruction = 1, .data = 1, .arguments = &.{}, .sequence_number = 1 };
    try map.put(trace.allocator(), old, 37);
    try map.put(trace.allocator(), neighbor, 53);
    const entry = map.getEntry(old).?;
    const other = map.getEntry(neighbor).?;
    const arguments = [_]u32{ 5, 17, 0xffffffff };
    const key: Key = .{ .item_type = .Push, .instruction = 171, .data = (@as(u256, 11) << 192) | (@as(u256, 7) << 128) | (@as(u256, 5) << 64) | 3, .arguments = &arguments, .sequence_number = 305419896 };
    entry.key_ptr.* = key;
    if (id) |incoming| entry.value_ptr.* = incoming;
    const stored = entry.key_ptr.*;
    const observed_id = entry.value_ptr.*;
    var result = keyObservation(stored, &arguments, observed_id, std.meta.eql(other.key_ptr.*, neighbor) and other.value_ptr.* == 53, &map, &trace);
    map.deinit(trace.allocator());
    live = false;
    result.frees = trace.frees;
    return .{ .key = result, .id = observed_id };
}

const NewSlotAssignment = struct {
    schema: []const u8 = "oksolc.expression-map-new-slot.v1",
    key: KeyAssignment,
    id: u32,
    lookup_id: ?u32,
    index: usize,
    fingerprint: u8,
    metadata_before: u8,
    metadata_after: u8,
    available_before: u32,
    available_after: u32,
    count_before: u32,
    found_existing: bool,
    pointers_retained: bool,
};

const TablePublication = struct {
    schema: []const u8 = "oksolc.expression-map-table.v1",
    first: KeyAssignment,
    first_id: u32,
    second_id: u32,
    second_arguments: [3]u32,
    second_key_retained: bool,
    second_pointer_retained: bool,
    lookup_first: ?u32,
    lookup_second: ?u32,
    both_new: bool,
    distinct_slots: bool,
    used_slots: usize,
    available: u32,
};

// Two keys differ only in an argument word. Distinct backing arrays keep their
// native lifetimes separate; lookup must compare contents and preserve the old
// entry. This regression exercises native probing without claiming its proof.
fn tablePublication(backing: std.mem.Allocator) !TablePublication {
    var trace: Trace = .{ .inner = backing };
    var map: Map = .empty;
    var live = true;
    defer if (live) map.deinit(trace.allocator());
    const first_arguments = [_]u32{ 5, 17, 0xffffffff };
    const second_arguments = [_]u32{ 5, 17, 0xfffffffe };
    const first_key: Key = .{ .item_type = .Push, .instruction = 171, .data = (@as(u256, 11) << 192) | (@as(u256, 7) << 128) | (@as(u256, 5) << 64) | 3, .arguments = &first_arguments, .sequence_number = 305419896 };
    var second_key = first_key;
    second_key.arguments = &second_arguments;
    const first = try map.getOrPut(trace.allocator(), first_key);
    first.key_ptr.* = first_key;
    first.value_ptr.* = 0xfedcba98;
    const second = try map.getOrPut(trace.allocator(), second_key);
    second.key_ptr.* = second_key;
    second.value_ptr.* = 53;
    var used: usize = 0;
    for (map.metadata.?[0..map.capacity()]) |metadata| {
        if (metadata.isUsed()) used += 1;
    }
    const retained = map.getEntry(first_key).?;
    var result: TablePublication = .{
        .first = keyObservation(retained.key_ptr.*, &first_arguments, retained.value_ptr.*, std.meta.eql(second.key_ptr.*, second_key), &map, &trace),
        .first_id = retained.value_ptr.*,
        .second_id = second.value_ptr.*,
        .second_arguments = second.key_ptr.arguments[0..3].*,
        .second_key_retained = std.meta.eql(second.key_ptr.*, second_key),
        .second_pointer_retained = second.key_ptr.arguments.ptr == second_arguments[0..].ptr,
        .lookup_first = map.get(first_key),
        .lookup_second = map.get(second_key),
        .both_new = !first.found_existing and !second.found_existing,
        .distinct_slots = retained.key_ptr != second.key_ptr and retained.value_ptr != second.value_ptr,
        .used_slots = used,
        .available = map.available,
    };
    map.deinit(trace.allocator());
    live = false;
    result.first.frees = trace.frees;
    return result;
}

// Execute the real new-slot route and its following publication stores. All
// other metadata remains free; lookup now uses the same key that was inserted.
fn newSlotAssignment(backing: std.mem.Allocator) !NewSlotAssignment {
    var trace: Trace = .{ .inner = backing };
    var map: Map = .empty;
    var live = true;
    defer if (live) map.deinit(trace.allocator());
    try map.ensureTotalCapacity(trace.allocator(), 1);
    const arguments = [_]u32{ 5, 17, 0xffffffff };
    const key: Key = .{ .item_type = .Push, .instruction = 171, .data = (@as(u256, 11) << 192) | (@as(u256, 7) << 128) | (@as(u256, 5) << 64) | 3, .arguments = &arguments, .sequence_number = 305419896 };
    const Context = @typeInfo(@TypeOf(Map.getOrPutContext)).@"fn".param_types[3].?;
    const hash = (Context{}).hash(key);
    const index: usize = @intCast(hash & (map.capacity() - 1));
    const fingerprint = Metadata.takeFingerprint(hash);
    const metadata_before: u8 = @bitCast(map.metadata.?[index]);
    const available_before = map.available;
    const count_before = map.count();
    const entry = try map.getOrPut(trace.allocator(), key);
    entry.key_ptr.* = key;
    entry.value_ptr.* = 0xfedcba98;
    var neighbors_free = true;
    for (map.metadata.?[0..map.capacity()], 0..) |metadata, other| {
        if (other != index and @as(u8, @bitCast(metadata)) != 0) neighbors_free = false;
    }
    const queried = map.getEntry(key).?;
    var result: NewSlotAssignment = .{
        .key = keyObservation(entry.key_ptr.*, &arguments, entry.value_ptr.*, neighbors_free, &map, &trace),
        .id = entry.value_ptr.*,
        .lookup_id = map.get(key),
        .index = index,
        .fingerprint = fingerprint,
        .metadata_before = metadata_before,
        .metadata_after = @bitCast(map.metadata.?[index]),
        .available_before = available_before,
        .available_after = map.available,
        .count_before = count_before,
        .found_existing = entry.found_existing,
        .pointers_retained = queried.key_ptr == entry.key_ptr and queried.value_ptr == entry.value_ptr,
    };
    map.deinit(trace.allocator());
    live = false;
    result.key.frees = trace.frees;
    return result;
}

// Check every old backing byte and every u7 fingerprint against the actual
// packed fields and native fill implementation; no uninitialized byte is read.
fn checkMetadataFill() !void {
    for (0..256) |old| {
        for (0..128) |fingerprint| {
            var metadata: Metadata = @bitCast(@as(u8, @intCast(old)));
            metadata.used = 1;
            if (@as(u8, @bitCast(metadata)) != 128 + old % 128) return error.UsedFieldMismatch;
            metadata = @bitCast(@as(u8, @intCast(old)));
            metadata.fill(@intCast(fingerprint));
            if (@as(u8, @bitCast(metadata)) != 128 + fingerprint or !metadata.isUsed() or metadata.isFree())
                return error.MetadataFillMismatch;
        }
    }
}

fn observe(backing: std.mem.Allocator, requested_count: u32) Case {
    var trace: Trace = .{ .inner = backing, .reject = true };
    var result: Case = .{ .requested_count = requested_count };
    {
        var map: Map = .empty;
        defer map.deinit(trace.allocator());
        result.oom_error = if (map.ensureTotalCapacity(trace.allocator(), requested_count)) |_| null else |err| @errorName(err);
        result.oom_request = trace.requested;
        result.oom_capacity = map.capacity();
        result.oom_metadata = if (map.metadata) |p| @intFromPtr(p) else 0;

        trace.reject = false;
        result.reserve_error = if (map.ensureTotalCapacity(trace.allocator(), requested_count)) |_| null else |err| @errorName(err);
        result.allocation = trace.requested;
        result.capacity = map.capacity();
        result.metadata = if (map.metadata) |p| @intFromPtr(p) else 0;
        if (result.reserve_error == null) {
            result.available = map.available;
            result.metadata_cleared = true;
            for (map.metadata.?[0..map.capacity()]) |entry| {
                if (!entry.isFree() or entry.isUsed() or @as(u8, @bitCast(entry)) != 0)
                    result.metadata_cleared = false;
            }
            const key: Key = .{ .item_type = .Operation, .instruction = @backingInt(evm.instruction.Instruction.PC), .data = 0, .arguments = &.{}, .sequence_number = 0 };
            result.empty_lookup = map.get(key) == null;
            result.insert_error = if (map.put(trace.allocator(), key, 37)) |_| null else |err| @errorName(err);
            if (map.getEntry(key)) |entry| {
                result.key_pointer = @intFromPtr(entry.key_ptr);
                result.value_pointer = @intFromPtr(entry.value_ptr);
                result.value = entry.value_ptr.*;
            }
            if (map.metadata) |metadata| {
                for (0..map.capacity()) |index| {
                    if (metadata[index].isUsed()) {
                        result.index = index;
                        break;
                    }
                }
            }
        }
    }
    result.attempts = trace.attempts;
    result.allocations = trace.allocations;
    result.frees = trace.frees;
    result.resizes = trace.resizes;
    result.remaps = trace.remaps;
    result.released = trace.released;
    return result;
}

// Check the complete packed interpretation and the exact byte memset view.
// Sentinels on both sides make a shifted or overlong clear observable.
fn checkPackedMetadata() !void {
    for (0..256) |bits| {
        const entry: Metadata = @bitCast(@as(u8, @intCast(bits)));
        if (entry.fingerprint != bits % 128 or entry.used != bits / 128 or
            entry.isUsed() != (bits >= 128) or entry.isFree() != (bits == 0) or entry.isTombstone() != (bits == 1))
            return error.UnexpectedPackedMetadata;
    }
    var slots: [10]Metadata = @splat(@bitCast(@as(u8, 0xa5)));
    @memset(@as([*]u8, @ptrCast(&slots[1]))[0 .. @sizeOf(Metadata) * 8], 0);
    if (@as(u8, @bitCast(slots[0])) != 0xa5 or @as(u8, @bitCast(slots[9])) != 0xa5)
        return error.MetadataClearCrossedBoundary;
    for (slots[1..9]) |entry| {
        if (!entry.isFree() or entry.isUsed()) return error.MetadataClearFailed;
    }
}

// Exercise the actual specialization's lock, including its erased ReleaseFast
// layout. This checks the scoped lock adapter, not intermediate grow states.
fn checkLocalLock() !void {
    var map: Map = .{};
    if (@sizeOf(@FieldType(Map, "pointer_stability")) != (if (std.debug.runtime_safety) @as(usize, 8) else 0))
        return error.UnexpectedLockLayout;
    if (std.debug.runtime_safety and @backingInt(map.pointer_stability.state) != 0) return error.LockNotInitialized;
    map.pointer_stability.lock();
    if (std.debug.runtime_safety and @backingInt(map.pointer_stability.state) != std.math.maxInt(usize))
        return error.LockNotExclusive;
    if (map.metadata != null or map.size != 0 or map.available != 0) return error.LockChangedMapFields;
    map.pointer_stability.unlock();
    if (std.debug.runtime_safety and @backingInt(map.pointer_stability.state) != 0) return error.LockNotReleased;
}

pub fn main(init: std.process.Init) !void {
    var args = try init.minimal.args.iterateAllocator(init.gpa);
    defer args.deinit();
    _ = args.next();
    if (args.next()) |count| {
        if (args.next() != null) return error.UnexpectedArguments;
        if (std.mem.eql(u8, count, "wyhash-hash")) {
            const result = @import("wyhash_hash.zig").observe();
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "wyhash-final")) {
            const result = @import("wyhash_local.zig").observeFinal();
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "wyhash-local")) {
            const result = @import("wyhash_local.zig").observe();
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "hash-input")) {
            var arena = std.heap.ArenaAllocator.init(init.gpa);
            defer arena.deinit();
            const result = try @import("expression_hash_input.zig").observe(arena.allocator());
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "caller")) {
            const result = try @import("expression_map_probe.zig").observeCaller(init.gpa);
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "probe")) {
            const result = try @import("expression_map_probe.zig").observe(init.gpa);
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "equality")) {
            const result = try @import("expression_map_equality.zig").observe(init.gpa);
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "table")) {
            const result = try tablePublication(init.gpa);
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        if (std.mem.eql(u8, count, "insert")) {
            try checkMetadataFill();
            const result = try newSlotAssignment(init.gpa);
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        const key_only = std.mem.eql(u8, count, "key");
        if (key_only or std.mem.eql(u8, count, "entry")) {
            const result = try assignment(init.gpa, if (key_only) null else 0xfedcba98);
            var buffer: [1024]u8 = undefined;
            var output = std.Io.File.stdout().writer(init.io, &buffer);
            if (key_only) try std.json.Stringify.value(result.key, .{}, &output.interface) else try std.json.Stringify.value(result, .{}, &output.interface);
            try output.interface.writeByte('\n');
            try output.interface.flush();
            return;
        }
        const result = capacityRequest(init.gpa, try std.fmt.parseInt(u32, count, 10));
        var buffer: [1024]u8 = undefined;
        var output = std.Io.File.stdout().writer(init.io, &buffer);
        try std.json.Stringify.value(result, .{}, &output.interface);
        try output.interface.writeByte('\n');
        try output.interface.flush();
        return;
    }
    try checkPackedMetadata();
    try checkLocalLock();
    // Observe the compiler's actual map instantiation without copying private
    // stdlib declarations or reading uninitialized header/key/value padding.
    const counts = [_]u32{ 1, 7, 25, 100 };
    var cases: [counts.len]Case = undefined;
    for (counts, 0..) |count, index| cases[index] = observe(init.gpa, count);
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(.{
        .schema = "oksolc.expression-map-buckets.v1",
        .target = capture.target(Key, "oksolc.expression-key-layout.v1"),
        .fields = capture.fieldsOf(Key),
        .metadata = .{
            .name = @typeName(Metadata),
            .bytes = @sizeOf(Metadata),
            .alignment = @alignOf(Metadata),
            .bits = @bitSizeOf(Metadata),
            .backing = @typeName(@typeInfo(Metadata).@"struct".backing_integer.?),
            .fingerprint_offset = @bitOffsetOf(Metadata, "fingerprint"),
            .used_offset = @bitOffsetOf(Metadata, "used"),
        },
        .value = .{ .name = @typeName(Value), .bytes = @sizeOf(Value), .alignment = @alignOf(Value) },
        .cases = cases,
    }, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
