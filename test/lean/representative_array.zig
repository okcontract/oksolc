// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Classes = evm.expression_classes.ExpressionClasses;
const Expression = evm.expression_classes.Expression;

const Header = struct { pointer: usize, length: usize, capacity: usize };
fn header(array: std.ArrayList(Expression)) Header {
    return .{ .pointer = @intFromPtr(array.items.ptr), .length = array.items.len, .capacity = array.capacity };
}

// Count attempts before forwarding, including failed remaps. The inner
// FailingAllocator supplies ordinary OOM and successful allocation totals.
const Calls = struct {
    inner: std.mem.Allocator,
    allocations: usize = 0,
    resizes: usize = 0,
    remaps: usize = 0,
    frees: usize = 0,
    requested_bytes: usize = 0,
    requested_alignment: usize = 0,

    fn allocator(self: *Calls) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{ .alloc = alloc, .resize = resize, .remap = remap, .free = free } };
    }

    fn alloc(context: *anyopaque, len: usize, alignment: std.mem.Alignment, return_address: usize) ?[*]u8 {
        const self: *Calls = @ptrCast(@alignCast(context));
        self.allocations += 1;
        self.requested_bytes = len;
        self.requested_alignment = alignment.toByteUnits();
        return self.inner.rawAlloc(len, alignment, return_address);
    }

    fn resize(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, len: usize, return_address: usize) bool {
        const self: *Calls = @ptrCast(@alignCast(context));
        self.resizes += 1;
        return self.inner.rawResize(memory, alignment, len, return_address);
    }

    fn remap(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, len: usize, return_address: usize) ?[*]u8 {
        const self: *Calls = @ptrCast(@alignCast(context));
        self.remaps += 1;
        return self.inner.rawRemap(memory, alignment, len, return_address);
    }

    fn free(context: *anyopaque, memory: []u8, alignment: std.mem.Alignment, return_address: usize) void {
        const self: *Calls = @ptrCast(@alignCast(context));
        self.frees += 1;
        self.inner.rawFree(memory, alignment, return_address);
    }
};

const Observation = struct {
    pointer: usize,
    readonly: bool,
    item_pointer: usize,
    arguments_pointer: usize,
    arguments_length: usize,
    arguments: []const u32,
    id: u32,
    sequence_number: u32,
};

fn observe(expression: *const Expression) Observation {
    return .{
        .pointer = @intFromPtr(expression),
        .readonly = @typeInfo(@TypeOf(expression)).pointer.attrs.@"const",
        .item_pointer = @intFromPtr(expression.item),
        .arguments_pointer = @intFromPtr(expression.arguments.ptr),
        .arguments_length = expression.arguments.len,
        .arguments = expression.arguments,
        .id = expression.id,
        .sequence_number = expression.sequence_number,
    };
}

fn invalid(classes: *const Classes, id: u32) !bool {
    _ = classes.representative(id) catch |err| switch (err) {
        error.InvalidExpressionId => return true,
        else => return err,
    };
    return false;
}

pub fn main(init: std.process.Init) !void {
    var tracking = std.testing.FailingAllocator.init(init.gpa, .{ .fail_index = 0 });
    var calls: Calls = .{ .inner = tracking.allocator() };
    var first: std.ArrayList(Expression) = .empty;
    defer first.deinit(calls.allocator());
    const first_before = header(first);
    try first.ensureTotalCapacityPrecise(calls.allocator(), 0);
    const first_noop = header(first);
    const noop_skipped_allocator = calls.allocations == 0 and calls.resizes == 0 and calls.remaps == 0 and calls.frees == 0;
    const first_oom = if (first.ensureTotalCapacityPrecise(calls.allocator(), 3)) |_| false else |err| err == error.OutOfMemory;
    const first_failed = header(first);
    const oom_induced = tracking.has_induced_failure and tracking.allocations == 0 and calls.allocations == 1 and
        calls.requested_bytes == 96 and calls.requested_alignment == 8 and calls.resizes == 0 and calls.remaps == 0 and calls.frees == 0;
    tracking.fail_index = std.math.maxInt(usize);
    try first.ensureTotalCapacityPrecise(calls.allocator(), 3);
    const first_after = header(first);
    // A full capacity check must skip the allocator even when it would fail.
    tracking.fail_index = tracking.alloc_index;
    try first.ensureTotalCapacityPrecise(calls.allocator(), 3);
    const first_unchanged = header(first);

    const maximum = std.math.maxInt(usize);
    const minima = [_]usize{ 0, 1, 2, 3, 8, maximum / 2, maximum - 1, maximum };
    var capacity_samples: [minima.len]struct { minimum: usize, capacity: usize } = undefined;
    for (minima, 0..) |minimum, index| {
        capacity_samples[index] = .{ .minimum = minimum, .capacity = std.ArrayList(Expression).growCapacity(minimum) };
    }
    var capacity_tracking = std.testing.FailingAllocator.init(init.gpa, .{ .fail_index = 0 });
    var capacity_calls: Calls = .{ .inner = capacity_tracking.allocator() };
    var capacity_array: std.ArrayList(Expression) = .empty;
    defer capacity_array.deinit(capacity_calls.allocator());
    const capacity_before = header(capacity_array);
    try capacity_array.ensureTotalCapacity(capacity_calls.allocator(), 0);
    const capacity_noop = header(capacity_array);
    const capacity_noop_skipped = capacity_calls.allocations == 0 and capacity_calls.resizes == 0 and
        capacity_calls.remaps == 0 and capacity_calls.frees == 0;
    const capacity_oom = if (capacity_array.ensureTotalCapacity(capacity_calls.allocator(), 1)) |_| false else |err| err == error.OutOfMemory;
    const capacity_failed = header(capacity_array);
    const capacity_oom_induced = capacity_tracking.has_induced_failure and capacity_tracking.allocations == 0 and
        capacity_calls.allocations == 1 and capacity_calls.requested_bytes == 160 and capacity_calls.requested_alignment == 8 and
        capacity_calls.resizes == 0 and capacity_calls.remaps == 0 and capacity_calls.frees == 0;
    capacity_tracking.fail_index = maximum;
    try capacity_array.ensureTotalCapacity(capacity_calls.allocator(), 1);
    const capacity_after = header(capacity_array);
    capacity_tracking.fail_index = capacity_tracking.alloc_index;
    try capacity_array.ensureTotalCapacity(capacity_calls.allocator(), 1);
    try capacity_array.ensureTotalCapacity(capacity_calls.allocator(), 5);
    const capacity_unchanged = header(capacity_array);
    var overflow_array: std.ArrayList(Expression) = .empty;
    defer overflow_array.deinit(capacity_calls.allocator());
    const overflow_before = header(overflow_array);
    const overflow_oom = if (overflow_array.ensureTotalCapacity(capacity_calls.allocator(), maximum)) |_| false else |err| err == error.OutOfMemory;
    const overflow_after = header(overflow_array);

    var fresh = Classes.init(init.gpa);
    defer fresh.deinit();
    const owned_before = header(fresh.representatives);
    const fresh_constant = try fresh.makeConstant(7, .{});
    const owned_first_header = header(fresh.representatives);
    const owned_first = observe(try fresh.representative(fresh_constant));
    const fresh_operation = try fresh.makeOperation(.CALLDATALOAD, &.{fresh_constant}, .{});
    const owned_rows = [_]Observation{
        observe(try fresh.representative(fresh_constant)),
        observe(try fresh.representative(fresh_operation)),
    };

    var classes = Classes.init(init.gpa);
    defer classes.deinit();
    const empty_rejected = try invalid(&classes, 0);
    // Spare capacity is deliberately present when the reader is exercised.
    // No representative pointer survives any constructor or growth call.
    try classes.representatives.ensureTotalCapacity(init.gpa, 8);
    const zero = try classes.makeConstant(0, .{});
    const one = try classes.makeConstant(1, .{});
    const input = try classes.makeOperation(.CALLDATALOAD, &.{zero}, .{});
    const second_input = try classes.makeOperation(.CALLDATALOAD, &.{one}, .{});
    const comparison_item = evm.assembly_item.AssemblyItem.initInstruction(.LT, .{});
    const before_append_length = classes.representatives.items.len;
    const before_append_capacity = classes.representatives.capacity;
    const before_append_pointer = @intFromPtr(classes.representatives.items.ptr);
    var parent_arguments = [_]evm.expression_classes.Id{ 777, second_input, input, 5 };
    const parent_before = parent_arguments;
    const comparison = try classes.find(&comparison_item, parent_arguments[1..3], true, 23);
    const append_size_increased = classes.representatives.items.len == before_append_length + 1;
    const append_capacity_unchanged = classes.representatives.capacity == before_append_capacity;
    const append_backing_unchanged = @intFromPtr(classes.representatives.items.ptr) == before_append_pointer;
    const before_hit = classes.size();
    const comparison_hit = try classes.find(&comparison_item, &.{ second_input, input }, true, 23);
    const cache_hit_size_unchanged = classes.size() == before_hit;
    // This descriptor borrows the existing item and parent argument buffer.
    // Only the new list's backing is released; it does not own these payloads.
    const append_value: Expression = .{
        .item = classes.representatives.items[comparison].item,
        .arguments = parent_arguments[1..3],
        .id = 0,
        .sequence_number = 29,
    };
    var append_tracking = std.testing.FailingAllocator.init(init.gpa, .{ .fail_index = 0 });
    var append_calls: Calls = .{ .inner = append_tracking.allocator() };
    var growing_append: std.ArrayList(Expression) = .empty;
    defer growing_append.deinit(append_calls.allocator());
    const growing_before = header(growing_append);
    const growing_oom = if (growing_append.append(append_calls.allocator(), append_value)) |_| false else |err| err == error.OutOfMemory;
    const growing_failed = header(growing_append);
    const growing_oom_induced = append_tracking.has_induced_failure and append_tracking.allocations == 0 and
        append_calls.allocations == 1 and append_calls.requested_bytes == 160 and append_calls.requested_alignment == 8 and
        append_calls.resizes == 0 and append_calls.remaps == 0 and append_calls.frees == 0;
    append_tracking.fail_index = maximum;
    try growing_append.append(append_calls.allocator(), append_value);
    const growing_after = header(growing_append);
    const before_copy = [_]Observation{
        observe(try classes.representative(zero)),
        observe(try classes.representative(one)),
        observe(try classes.representative(input)),
        observe(try classes.representative(second_input)),
        observe(try classes.representative(comparison)),
    };
    const before_copy_header = .{
        .pointer = @intFromPtr(classes.representatives.items.ptr),
        .length = classes.representatives.items.len,
        .capacity = classes.representatives.capacity,
    };
    // Observe the host.copy boundary used by ArrayList's allocation fallback.
    // Only the initialized prefix is read. These shallow copies borrow the
    // original item/argument allocations and must not deinit their payloads.
    const copied = try init.gpa.alloc(Expression, classes.representatives.items.len + 2);
    var grown = std.ArrayList(Expression).fromOwnedSlice(copied);
    grown.items.len = classes.representatives.items.len;
    defer grown.deinit(init.gpa);
    @memcpy(copied[0..classes.representatives.items.len], classes.representatives.items);
    var copy_observations: [5]Observation = undefined;
    var observations: [5]Observation = undefined;
    for (&copy_observations, &observations, 0..) |*target, *source, index| {
        target.* = observe(&copied[index]);
        source.* = observe(&classes.representatives.items[index]);
    }
    const publication_before = .{
        .pointer = @intFromPtr(grown.items.ptr),
        .length = grown.items.len,
        .capacity = grown.capacity,
    };
    // Exercise the pinned native growth body. The proof in this gate covers
    // its reached publication suffix; it does not establish remap retention.
    try grown.ensureTotalCapacityPrecise(init.gpa, publication_before.capacity + 3);
    var published_observations: [5]Observation = undefined;
    for (&published_observations, 0..) |*observation, index| {
        observation.* = observe(&grown.items[index]);
    }
    const profile = .{
        .schema = "oksolc.representative-array-observations.v11",
        .zigVersion = builtin.zig_version_string,
        .mode = switch (builtin.mode) {
            .debug => "Debug",
            .safe => "ReleaseSafe",
            .fast => "ReleaseFast",
            .small => "ReleaseSmall",
        },
        .backend = @tagName(builtin.zig_backend),
        .owner_pointer = @intFromPtr(&classes),
        .owner_bytes = @sizeOf(Classes),
        .owner_alignment = @alignOf(Classes),
        .allocator_pointer = @intFromPtr(&classes.allocator),
        .expressions_pointer = @intFromPtr(&classes.expressions),
        .header_pointer = @intFromPtr(&classes.representatives),
        .header_bytes = @sizeOf(@TypeOf(classes.representatives)),
        .header_alignment = @alignOf(@TypeOf(classes.representatives)),
        .items_pointer = @intFromPtr(classes.representatives.items.ptr),
        .length = classes.representatives.items.len,
        .capacity = classes.representatives.capacity,
        .element_bytes = @sizeOf(Expression),
        .element_alignment = @alignOf(Expression),
        .empty_rejected = empty_rejected,
        .length_rejected = try invalid(&classes, @intCast(classes.representatives.items.len)),
        .capacity_rejected = try invalid(&classes, @intCast(classes.representatives.capacity)),
        .maximum_rejected = try invalid(&classes, std.math.maxInt(u32)),
        .cache_hit = comparison_hit == comparison,
        .cache_hit_size_unchanged = cache_hit_size_unchanged,
        .before_append_length = before_append_length,
        .before_append_capacity = before_append_capacity,
        .before_append_pointer = before_append_pointer,
        .append_size_increased = append_size_increased,
        .append_capacity_unchanged = append_capacity_unchanged,
        .append_backing_unchanged = append_backing_unchanged,
        .append_id_matches_previous_length = comparison == before_append_length,
        .parent_pointer = @intFromPtr(&parent_arguments),
        .parent_before = parent_before,
        .parent_after = parent_arguments,
        .parent_offset = 1,
        .parent_length = 2,
        .representatives = observations,
        .owned_append = .{
            .owner_pointer = @intFromPtr(&fresh),
            .before = owned_before,
            .first_header = owned_first_header,
            .first = owned_first,
            .after = header(fresh.representatives),
            .rows = owned_rows,
            .length_rejected = try invalid(&fresh, @intCast(fresh.representatives.items.len)),
            .capacity_rejected = try invalid(&fresh, @intCast(fresh.representatives.capacity)),
        },
        .first_growth = .{
            .before = first_before,
            .noop = first_noop,
            .noop_skipped_allocator = noop_skipped_allocator,
            .oom_reported = first_oom,
            .oom_induced = oom_induced,
            .failed = first_failed,
            .after = first_after,
            .unchanged = first_unchanged,
            .allocated_bytes = tracking.allocated_bytes,
            .allocations = tracking.allocations,
            .allocation_calls = calls.allocations,
            .requested_bytes = calls.requested_bytes,
            .requested_alignment = calls.requested_alignment,
            .resize_calls = calls.resizes,
            .remap_calls = calls.remaps,
            .free_calls = calls.frees,
        },
        .capacity_selection = .{
            .arch = @tagName(builtin.cpu.arch),
            .cache_line = @as(usize, std.atomic.cache_line),
            .samples = capacity_samples,
            .first_growth = .{
                .before = capacity_before,
                .noop = capacity_noop,
                .noop_skipped_allocator = capacity_noop_skipped,
                .oom_reported = capacity_oom,
                .oom_induced = capacity_oom_induced,
                .failed = capacity_failed,
                .after = capacity_after,
                .unchanged = capacity_unchanged,
                .allocated_bytes = capacity_tracking.allocated_bytes,
                .allocations = capacity_tracking.allocations,
                .allocation_calls = capacity_calls.allocations,
                .requested_bytes = capacity_calls.requested_bytes,
                .requested_alignment = capacity_calls.requested_alignment,
                .resize_calls = capacity_calls.resizes,
                .remap_calls = capacity_calls.remaps,
                .free_calls = capacity_calls.frees,
            },
            .overflow_oom = overflow_oom,
            .overflow_before = overflow_before,
            .overflow_after = overflow_after,
        },
        .growing_append = .{
            .before = growing_before,
            .failed = growing_failed,
            .after = growing_after,
            .oom_reported = growing_oom,
            .oom_induced = growing_oom_induced,
            .allocated_bytes = append_tracking.allocated_bytes,
            .allocations = append_tracking.allocations,
            .allocation_calls = append_calls.allocations,
            .requested_bytes = append_calls.requested_bytes,
            .requested_alignment = append_calls.requested_alignment,
            .resize_calls = append_calls.resizes,
            .remap_calls = append_calls.remaps,
            .free_calls = append_calls.frees,
            .record = observe(&growing_append.items[0]),
            .parent_after = parent_arguments,
        },
        .copy = .{
            .source_before = before_copy,
            .header_before = before_copy_header,
            .target_pointer = publication_before.pointer,
            .target_capacity = publication_before.capacity,
            .copied = copy_observations,
        },
        .publication = .{
            .before = publication_before,
            .after = .{ .pointer = @intFromPtr(grown.items.ptr), .length = grown.items.len, .capacity = grown.capacity },
            .representatives = published_observations,
        },
    };
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(profile, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
