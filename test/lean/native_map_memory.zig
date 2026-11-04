// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Classes = evm.expression_classes.ExpressionClasses;
const Item = evm.assembly_item.AssemblyItem;

const Allocations = struct {
    allocations: usize,
    deallocations: usize,
    allocated_bytes: usize,
    freed_bytes: usize,
    resizes: usize,
    induced_failure: bool,

    fn observe(allocator: *const std.testing.FailingAllocator) Allocations {
        return .{
            .allocations = allocator.allocations,
            .deallocations = allocator.deallocations,
            .allocated_bytes = allocator.allocated_bytes,
            .freed_bytes = allocator.freed_bytes,
            .resizes = allocator.resize_index,
            .induced_failure = allocator.has_induced_failure,
        };
    }
};

const Snapshot = struct {
    owner_address: usize,
    map_size_address: usize,
    map_size: u32,
    map_capacity: u32,
    map_available: u32,
    map_metadata: usize,
    map_unlocked: bool,
    representative_count: usize,
    representative_capacity: usize,
    representative_storage: usize,
    representative_item: usize,
    cached_id: ?u32,
    allocator: Allocations,

    fn observe(classes: *const Classes, allocator: *const std.testing.FailingAllocator) Snapshot {
        const Map = @TypeOf(classes.expressions);
        const empty: Map = .empty;
        return .{
            .owner_address = @intFromPtr(classes),
            .map_size_address = @intFromPtr(&classes.expressions.size),
            .map_size = classes.expressions.size,
            .map_capacity = classes.expressions.capacity(),
            .map_available = classes.expressions.available,
            .map_metadata = if (classes.expressions.metadata) |pointer| @intFromPtr(pointer) else 0,
            .map_unlocked = std.meta.eql(classes.expressions.pointer_stability, empty.pointer_stability),
            .representative_count = classes.representatives.items.len,
            .representative_capacity = classes.representatives.capacity,
            .representative_storage = @intFromPtr(classes.representatives.items.ptr),
            .representative_item = @intFromPtr(classes.representatives.items[0].item),
            .cached_id = classes.expressions.get(.{
                .item_type = .Operation,
                .instruction = @backingInt(evm.instruction.Instruction.PC),
                .data = 0,
                .arguments = &.{},
                .sequence_number = 0,
            }),
            .allocator = Allocations.observe(allocator),
        };
    }
};

const Case = struct { name: []const u8, before: Snapshot, after: Snapshot, failure: ?[]const u8 };
const Observation = struct { id: u32, opcode: u8, argument_count: usize, cases: [3]Case, teardown: Allocations };

fn attempt(name: []const u8, classes: *Classes, allocator: *std.testing.FailingAllocator, id: u32, item: *const Item) Case {
    const before = Snapshot.observe(classes, allocator);
    const failure = if (classes.forceEqual(id, item, &.{}, true)) |_| null else |err| @errorName(err);
    return .{ .name = name, .before = before, .after = Snapshot.observe(classes, allocator), .failure = failure };
}

/// PC creates a real representative without populating the deterministic map.
/// forceEqual then reaches the compiler's own publishOwned with an empty key.
/// Observe before asserting: the Python gate retains all fields and failures.
fn observe(backing: std.mem.Allocator) !Observation {
    var allocator = std.testing.FailingAllocator.init(backing, .{ .resize_fail_index = 0 });
    var result: Observation = undefined;
    {
        var classes = Classes.init(allocator.allocator());
        defer classes.deinit();
        const item = Item.initInstruction(.PC, .{});
        const id = try classes.findDefault(&item, &.{});

        allocator.fail_index = allocator.alloc_index;
        const failure = attempt("first-bucket-oom", &classes, &allocator, id, &item);
        allocator.fail_index = std.math.maxInt(usize);
        const created = attempt("first-bucket-success", &classes, &allocator, id, &item);
        allocator.fail_index = allocator.alloc_index;
        allocator.has_induced_failure = false;
        const hit = attempt("cached-force", &classes, &allocator, id, &item);

        result = .{ .id = id, .opcode = @backingInt(evm.instruction.Instruction.PC), .argument_count = 0, .cases = .{ failure, created, hit }, .teardown = undefined };
    }
    result.teardown = Allocations.observe(&allocator);
    return result;
}

pub fn main(init: std.process.Init) !void {
    const observation = try observe(init.gpa);
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(.{
        .schema = "oksolc.native-map-memory-boundary.v1",
        .zigVersion = builtin.zig_version_string,
        .mode = switch (builtin.mode) {
            .debug => "Debug",
            .safe => "ReleaseSafe",
            .fast => "ReleaseFast",
            .small => "ReleaseSmall",
        },
        .backend = @tagName(builtin.zig_backend),
        .arch = @tagName(builtin.cpu.arch),
        .os = @tagName(builtin.os.tag),
        .pointer_bits = @bitSizeOf(usize),
        .owner_size = @sizeOf(Classes),
        .observation = observation,
    }, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
