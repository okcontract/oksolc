// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Unreferenced JUMPDEST removal translated from `JumpdestRemover.cpp`.

const std = @import("std");
const AssemblyItem = @import("assembly_item.zig").AssemblyItem;
const SubAssemblyID = @import("sub_assembly_id.zig").SubAssemblyID;

pub const TagSet = struct {
    values: std.ArrayList(usize) = .empty,

    pub fn deinit(self: *TagSet, allocator: std.mem.Allocator) void {
        self.values.deinit(allocator);
        self.* = undefined;
    }

    pub fn contains(self: *const TagSet, value: usize) bool {
        return search(self.values.items, value).found;
    }

    pub fn insert(self: *TagSet, allocator: std.mem.Allocator, value: usize) !bool {
        const result = search(self.values.items, value);
        if (result.found) return false;
        try self.values.insert(allocator, result.index, value);
        return true;
    }
};

pub fn referencedTagsAlloc(
    allocator: std.mem.Allocator,
    items: []const AssemblyItem,
    sub_id: SubAssemblyID,
) std.mem.Allocator.Error!TagSet {
    var result: TagSet = .{};
    errdefer result.deinit(allocator);
    for (items) |*item| {
        if (item.item_type != .PushTag) continue;
        const split = item.splitForeignPushTag() catch unreachable; // zlinter-disable-current-line no_swallow_error - assembly item kind was checked immediately before this invariant conversion
        if (split[0].eql(sub_id)) _ = try result.insert(allocator, split[1]);
    }
    return result;
}

pub fn optimise(
    allocator: std.mem.Allocator,
    items: *std.ArrayList(AssemblyItem),
    tags_referenced_from_outside: []const usize,
) std.mem.Allocator.Error!bool {
    var references = try referencedTagsAlloc(allocator, items.items, .{});
    defer references.deinit(allocator);
    for (tags_referenced_from_outside) |tag_id| _ = try references.insert(allocator, tag_id);

    const initial_size = items.items.len;
    var output_index: usize = 0;
    for (items.items, 0..) |*item, input_index| {
        var remove = false;
        if (item.item_type == .Tag) {
            const split = item.splitForeignPushTag() catch unreachable; // zlinter-disable-current-line no_swallow_error - assembly item kind was checked immediately before this invariant conversion
            std.debug.assert(split[0].empty());
            remove = !references.contains(split[1]);
        }
        if (remove) {
            item.deinit(allocator);
        } else {
            if (output_index != input_index) {
                // Assignment transfers ownership into the compacted prefix;
                // the stale tail copy is discarded by shrinking below.
                items.items[output_index] = item.*;
            }
            output_index += 1;
        }
    }
    items.shrinkRetainingCapacity(output_index);
    return output_index != initial_size;
}

const SearchResult = struct { index: usize, found: bool };

fn search(values: []const usize, value: usize) SearchResult {
    var lower: usize = 0;
    var upper = values.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (values[middle] < value) lower = middle + 1 else upper = middle;
    }
    return .{
        .index = lower,
        .found = lower < values.len and values[lower] == value,
    };
}

test "jumpdest removal retains local and externally referenced tags only" {
    var items: std.ArrayList(AssemblyItem) = .empty;
    defer {
        for (items.items) |*item| item.deinit(std.testing.allocator);
        items.deinit(std.testing.allocator);
    }
    const tag_one = AssemblyItem.initType(.Tag, 1, .{});
    const tag_two = AssemblyItem.initType(.Tag, 2, .{});
    const tag_three = AssemblyItem.initType(.Tag, 3, .{});
    try items.appendSlice(std.testing.allocator, &.{
        tag_one,
        AssemblyItem.initType(.PushTag, 1, .{}),
        tag_two,
        tag_three,
    });
    try std.testing.expect(try optimise(std.testing.allocator, &items, &.{3}));
    try std.testing.expectEqual(@as(usize, 3), items.items.len);
    try std.testing.expectEqual(@as(u256, 1), items.items[0].data_value);
    try std.testing.expectEqual(@as(u256, 3), items.items[2].data_value);
}

test "foreign tag references are selected by subassembly id" {
    var foreign = AssemblyItem.initType(.PushTag, 7, .{});
    try foreign.setPushTagSubIdAndTag(SubAssemblyID.init(4), 7);
    const items = [_]AssemblyItem{
        AssemblyItem.initType(.PushTag, 3, .{}),
        foreign,
    };
    var tags = try referencedTagsAlloc(std.testing.allocator, &items, SubAssemblyID.init(4));
    defer tags.deinit(std.testing.allocator);
    try std.testing.expect(tags.contains(7));
    try std.testing.expect(!tags.contains(3));
}
