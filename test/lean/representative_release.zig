// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Expression = evm.expression_classes.Expression;

// Observe allocation and rawFree through the same allocator. The backing
// contains borrowed pointers; only its storage is freed.
const FreeProbe = struct {
    inner: std.mem.Allocator,
    allocations: usize = 0,
    allocation_base: usize = 0,
    requested_bytes: usize = 0,
    requested_alignment: usize = 0,
    order: usize = 0,
    calls: usize = 0,
    base: usize = 0,
    bytes: usize = 0,
    alignment: usize = 0,
    remap_calls: usize = 0,
    remap_base: usize = 0,
    remap_bytes: usize = 0,
    remap_new_bytes: usize = 0,
    remap_alignment: usize = 0,

    fn allocator(self: *FreeProbe) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{ .alloc = alloc, .resize = resize, .remap = remap, .free = free } };
    }
    fn alloc(context: *anyopaque, len: usize, alignment: std.mem.Alignment, ra: usize) ?[*]u8 {
        const self: *FreeProbe = @ptrCast(@alignCast(context));
        self.allocations += 1;
        self.requested_bytes = len;
        self.requested_alignment = alignment.toByteUnits();
        self.order = self.order * 10 + 1;
        const memory = self.inner.rawAlloc(len, alignment, ra);
        self.allocation_base = if (memory) |pointer| @intFromPtr(pointer) else 0;
        return memory;
    }
    fn resize(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, len: usize, ra: usize) bool {
        const self: *FreeProbe = @ptrCast(@alignCast(context));
        return self.inner.rawResize(memory, alignment, len, ra);
    }
    fn remap(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, len: usize, _: usize) ?[*]u8 {
        const self: *FreeProbe = @ptrCast(@alignCast(context));
        self.remap_calls += 1;
        self.remap_base = @intFromPtr(memory.ptr);
        self.remap_bytes = memory.len;
        self.remap_new_bytes = len;
        self.remap_alignment = alignment.toByteUnits();
        self.order = self.order * 10 + 3;
        // Select the actual source fallback in this finite native fixture.
        // This does not establish a general production remap contract.
        return null;
    }
    fn free(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ra: usize) void {
        const self: *FreeProbe = @ptrCast(@alignCast(context));
        self.calls += 1;
        self.order = self.order * 10 + 2;
        self.base = @intFromPtr(memory.ptr);
        self.bytes = memory.len;
        self.alignment = alignment.toByteUnits();
        self.inner.rawFree(memory, alignment, ra);
    }
};

pub fn main(init: std.process.Init) !void {
    var failing = std.testing.FailingAllocator.init(init.gpa, .{ .fail_index = 0 });
    var rejected: FreeProbe = .{ .inner = failing.allocator() };
    const oom = if (rejected.allocator().alloc(Expression, 5)) |unexpected| blk: {
        rejected.allocator().free(unexpected);
        break :blk false;
    } else |err| err == error.OutOfMemory;
    var probe: FreeProbe = .{ .inner = init.gpa };
    const allocator = probe.allocator();
    var item = evm.assembly_item.AssemblyItem.initInstruction(.LT, .{});
    var parent = [_]u32{ 777, 99, 1, 5 };
    const storage = try allocator.alloc(Expression, 5);
    var array: std.ArrayList(Expression) = .fromOwnedSlice(storage);
    array.items.len = 2;
    defer array.deinit(allocator);
    array.items[0] = .{ .item = &item, .arguments = parent[1..3], .id = 0, .sequence_number = 23 };
    array.items[1] = .{ .item = &item, .arguments = parent[1..3], .id = 1, .sequence_number = 29 };
    var growth_failing = std.testing.FailingAllocator.init(init.gpa, .{ .fail_index = 1 });
    var growth_rejected: FreeProbe = .{ .inner = growth_failing.allocator() };
    const growth_allocator = growth_rejected.allocator();
    const retained = try growth_allocator.alloc(Expression, 5);
    var failed_array: std.ArrayList(Expression) = .fromOwnedSlice(retained);
    failed_array.items.len = 2;
    defer failed_array.deinit(growth_allocator);
    const retained_base = @intFromPtr(retained.ptr);
    @memcpy(failed_array.items, array.items);
    const growth_oom = if (failed_array.ensureTotalCapacityPrecise(growth_allocator, 7)) |_| false else |err| err == error.OutOfMemory;
    const item_base = @intFromPtr(array.items[1].item);
    const arguments_base = @intFromPtr(array.items[1].arguments.ptr);
    const arguments_length = array.items[1].arguments.len;
    const allocated = array.allocatedSlice();
    const base = @intFromPtr(allocated.ptr);
    const length = array.items.len;
    const capacity = array.capacity;
    const allocation = .{ .calls = probe.allocations, .base = probe.allocation_base, .bytes = probe.requested_bytes, .alignment = probe.requested_alignment };
    try array.ensureTotalCapacityPrecise(allocator, 7);
    const copied = array.allocatedSlice();
    const copy_allocation = .{ .calls = probe.allocations - allocation.calls, .base = probe.allocation_base, .bytes = probe.requested_bytes, .alignment = probe.requested_alignment };
    // Read the new descriptors and independent pointees, never the old storage.
    const calls_after_nonempty = probe.calls;
    const empty: std.ArrayList(Expression) = .empty;
    allocator.free(empty.allocatedSlice());
    // Empty growth must not inspect or release the interior sentinel view.
    var sentinel_storage: [2]Expression = undefined;
    var empty_probe: FreeProbe = .{ .inner = init.gpa };
    const empty_allocator = empty_probe.allocator();
    var empty_array: std.ArrayList(Expression) = .empty;
    empty_array.items = sentinel_storage[1..1];
    const empty_source = @intFromPtr(empty_array.items.ptr);
    try empty_array.ensureTotalCapacityPrecise(empty_allocator, 5);
    defer empty_array.deinit(empty_allocator);
    const profile = .{
        .schema = "oksolc.representative-release-native.v6",
        .target = .{ .arch = @tagName(builtin.cpu.arch), .os = @tagName(builtin.os.tag), .mode = switch (builtin.mode) {
            .debug => "Debug",
            .safe => "ReleaseSafe",
            .fast => "ReleaseFast",
            .small => "ReleaseSmall",
        }, .pointer_bytes = @sizeOf(usize) },
        .descriptor = .{ .bytes = @sizeOf(Expression), .alignment = @alignOf(Expression) },
        .backing = .{ .base = base, .length = length, .capacity = capacity },
        .allocation = allocation,
        .copy_allocation = copy_allocation,
        .remap = .{ .calls = probe.remap_calls, .base = probe.remap_base, .bytes = probe.remap_bytes, .new_bytes = probe.remap_new_bytes, .alignment = probe.remap_alignment },
        .header = .{ .base = @intFromPtr(array.items.ptr), .length = array.items.len, .capacity = array.capacity },
        .copy = .{ .base = @intFromPtr(copied.ptr), .capacity = copied.len, .rows = .{
            .{ .item_base = @intFromPtr(copied[0].item), .arguments_base = @intFromPtr(copied[0].arguments.ptr), .arguments_length = copied[0].arguments.len, .id = copied[0].id, .sequence = copied[0].sequence_number },
            .{ .item_base = @intFromPtr(copied[1].item), .arguments_base = @intFromPtr(copied[1].arguments.ptr), .arguments_length = copied[1].arguments.len, .id = copied[1].id, .sequence = copied[1].sequence_number },
        } },
        .release = .{ .calls = calls_after_nonempty, .base = probe.base, .bytes = probe.bytes, .alignment = probe.alignment },
        .order = probe.order,
        .oom = .{ .failed = oom, .calls = rejected.allocations, .base = rejected.allocation_base, .bytes = rejected.requested_bytes, .alignment = rejected.requested_alignment, .frees = rejected.calls, .order = rejected.order },
        .growth_oom = .{
            .failed = growth_oom,
            .calls = growth_rejected.allocations,
            .base = growth_rejected.allocation_base,
            .bytes = growth_rejected.requested_bytes,
            .alignment = growth_rejected.requested_alignment,
            .frees = growth_rejected.calls,
            .order = growth_rejected.order,
            .remap = .{ .calls = growth_rejected.remap_calls, .base = growth_rejected.remap_base, .bytes = growth_rejected.remap_bytes, .new_bytes = growth_rejected.remap_new_bytes, .alignment = growth_rejected.remap_alignment },
            .old_base = retained_base,
            .header = .{ .base = @intFromPtr(failed_array.items.ptr), .length = failed_array.items.len, .capacity = failed_array.capacity },
            .rows = .{
                .{ .item_base = @intFromPtr(failed_array.items[0].item), .arguments_base = @intFromPtr(failed_array.items[0].arguments.ptr), .arguments_length = failed_array.items[0].arguments.len, .id = failed_array.items[0].id, .sequence = failed_array.items[0].sequence_number },
                .{ .item_base = @intFromPtr(failed_array.items[1].item), .arguments_base = @intFromPtr(failed_array.items[1].arguments.ptr), .arguments_length = failed_array.items[1].arguments.len, .id = failed_array.items[1].id, .sequence = failed_array.items[1].sequence_number },
            },
        },
        .empty_calls = probe.calls - calls_after_nonempty,
        .empty_growth = .{
            .sentinel_base = @intFromPtr(&sentinel_storage),
            .source = empty_source,
            .calls = empty_probe.allocations,
            .base = empty_probe.allocation_base,
            .bytes = empty_probe.requested_bytes,
            .alignment = empty_probe.requested_alignment,
            .remaps = empty_probe.remap_calls,
            .frees = empty_probe.calls,
            .order = empty_probe.order,
            .header = .{ .base = @intFromPtr(empty_array.items.ptr), .length = empty_array.items.len, .capacity = empty_array.capacity },
        },
        .item = .{ .base_before = item_base, .base_after = @intFromPtr(&item), .instruction_after = @tagName(try item.instruction()) },
        .parent = .{ .base = @intFromPtr(&parent), .arguments_base = arguments_base, .arguments_length = arguments_length, .after = parent },
    };
    var buffer: [2048]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(profile, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
