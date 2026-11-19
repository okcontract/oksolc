// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Classes = evm.expression_classes.ExpressionClasses;

const Trace = struct {
    alloc: usize = 3,
    resize: usize = 7,
    remap: usize = 11,
    free: usize = 13,

    fn get(context: *anyopaque) *Trace {
        return @ptrCast(@alignCast(context));
    }
    fn allocate(context: *anyopaque, _: usize, _: std.mem.Alignment, _: usize) ?[*]u8 {
        get(context).alloc += 1;
        return null;
    }
    fn resizeMemory(context: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) bool {
        get(context).resize += 1;
        return false;
    }
    fn remapMemory(context: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize, _: usize) ?[*]u8 {
        get(context).remap += 1;
        return null;
    }
    fn freeMemory(context: *anyopaque, _: []u8, _: std.mem.Alignment, _: usize) void {
        get(context).free += 1;
    }
    const vtable: std.mem.Allocator.VTable = .{
        .alloc = allocate,
        .resize = resizeMemory,
        .remap = remapMemory,
        .free = freeMemory,
    };
};

const Fields = struct {
    allocator_pointer: usize,
    allocator_vtable: usize,
    representative_length: usize,
    representative_capacity: usize,
    map_metadata_null: bool,
    map_size: u32,
    map_available: u32,
    map_lock_empty: bool,
    representative_lock_empty: bool,
};
const Query = struct { id: u32, opcode: u8, invalid_representative: bool, constant_missing: bool, operation_missing: bool, cache_missing: bool };
const Observation = struct { input: Fields, actual: Fields, before: Trace, after: Trace, size: usize, cache_capacity: u32, key_iterator_empty: bool, queries: [1024]Query };

fn observe(trace: *Trace) Observation {
    const allocator: std.mem.Allocator = .{ .ptr = trace, .vtable = &Trace.vtable };
    const initial = trace.*;
    const classes = Classes.init(allocator);
    const Map = @TypeOf(classes.expressions);
    const empty: Map = .empty;
    comptime {
        std.debug.assert(@typeInfo(Classes).@"struct".field_names.len == 3);
        std.debug.assert(@typeInfo(@TypeOf(classes.representatives)).@"struct".field_names.len == 3);
        std.debug.assert(@typeInfo(Map).@"struct".field_names.len == 4);
    }
    var queries: [1024]Query = undefined;
    var count: usize = 0;
    for ([_]u32{ 0, 1, 0xFFFFFFFE, 0xFFFFFFFF }) |id| {
        for (0..256) |opcode| {
            const result = classes.representative(id);
            const invalid = if (result) |_| false else |err| err == error.InvalidExpressionId;
            queries[count] = .{
                .id = id,
                .opcode = @intCast(opcode),
                .invalid_representative = invalid,
                .constant_missing = classes.knownConstant(id) == null,
                .operation_missing = classes.operationArguments(id, @fromBackingInt(@intCast(opcode))) == null,
                .cache_missing = classes.expressions.get(.{
                    .item_type = if (id & 1 == 0) .Operation else .Push,
                    .instruction = @intCast(opcode),
                    .data = id,
                    .arguments = &.{ id, @intCast(opcode) },
                    .sequence_number = id,
                }) == null,
            };
            count += 1;
        }
    }
    std.debug.assert(count == queries.len);
    var keys = classes.expressions.keyIterator();
    const cache_capacity = classes.expressions.capacity();
    const key_iterator_empty = keys.next() == null;
    return .{
        .input = .{ .allocator_pointer = @intFromPtr(allocator.ptr), .allocator_vtable = @intFromPtr(allocator.vtable), .representative_length = 0, .representative_capacity = 0, .map_metadata_null = true, .map_size = 0, .map_available = 0, .map_lock_empty = true, .representative_lock_empty = true },
        .actual = .{ .allocator_pointer = @intFromPtr(classes.allocator.ptr), .allocator_vtable = @intFromPtr(classes.allocator.vtable), .representative_length = classes.representatives.items.len, .representative_capacity = classes.representatives.capacity, .map_metadata_null = classes.expressions.metadata == null, .map_size = classes.expressions.size, .map_available = classes.expressions.available, .map_lock_empty = std.meta.eql(classes.expressions.pointer_stability, empty.pointer_stability), .representative_lock_empty = std.meta.eql(classes.representatives.pointer_stability, empty.pointer_stability) },
        .before = initial,
        .after = trace.*,
        .size = classes.size(),
        .cache_capacity = cache_capacity,
        .key_iterator_empty = key_iterator_empty,
        .queries = queries,
    };
}

pub fn main(init: std.process.Init) !void {
    var traces: [2]Trace = .{ .{}, .{ .alloc = 17, .resize = 19, .remap = 23, .free = 29 } };
    const cases = [_]Observation{ observe(&traces[0]), observe(&traces[1]) };
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(.{ .schema = "oksolc.graph-init-observations.v4", .zigVersion = builtin.zig_version_string, .mode = switch (builtin.mode) {
        .debug => "Debug",
        .safe => "ReleaseSafe",
        .fast => "ReleaseFast",
        .small => "ReleaseSmall",
    }, .backend = @tagName(builtin.zig_backend), .cases = cases }, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
