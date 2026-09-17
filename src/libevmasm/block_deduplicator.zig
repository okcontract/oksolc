// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Basic-block suffix deduplication translated from `BlockDeduplicator.cpp`.

const std = @import("std");
const AssemblyItemModule = @import("assembly_item.zig");
const SemanticInformation = @import("semantic_information.zig");
const SubAssemblyID = @import("sub_assembly_id.zig").SubAssemblyID;

const AssemblyItem = AssemblyItemModule.AssemblyItem;

pub const TagReplacement = struct {
    from: u256,
    to: u256,
};

pub const BlockDeduplicator = struct {
    replaced_tags: std.ArrayList(TagReplacement) = .empty,

    pub fn deinit(self: *BlockDeduplicator, allocator: std.mem.Allocator) void {
        self.replaced_tags.deinit(allocator);
        self.* = undefined;
    }

    pub fn replacements(self: *const BlockDeduplicator) []const TagReplacement {
        return self.replaced_tags.items;
    }

    pub fn deduplicate(
        self: *BlockDeduplicator,
        allocator: std.mem.Allocator,
        items: *std.ArrayList(AssemblyItem),
    ) std.mem.Allocator.Error!bool {
        const push_self = AssemblyItem.initType(.PushTag, std.math.maxInt(u256) - 3, .{});
        const self_tag = push_self.tag() catch unreachable; // zlinter-disable-current-line no_swallow_error - assembly item kind was checked immediately before this invariant conversion
        for (items.items) |*item| {
            if (item.eql(&self_tag) or item.eql(&push_self)) return false;
        }

        var iterations: usize = 0;
        while (true) : (iterations += 1) {
            var blocks_seen: std.ArrayList(usize) = .empty;
            defer blocks_seen.deinit(allocator);
            for (items.items, 0..) |*item, index| {
                if (item.item_type != .Tag) continue;
                const position = lowerBoundBlock(items.items, blocks_seen.items, index, &push_self);
                if (position == blocks_seen.items.len or
                    blockLess(items.items, index, blocks_seen.items[position], &push_self) or
                    blockLess(items.items, blocks_seen.items[position], index, &push_self))
                {
                    try blocks_seen.insert(allocator, position, index);
                } else {
                    try self.putReplacement(allocator, item.data_value, items.items[blocks_seen.items[position]].data_value);
                }
            }
            if (!applyTagReplacement(items.items, self.replaced_tags.items, .{})) break;
        }
        return iterations > 0;
    }

    fn putReplacement(
        self: *BlockDeduplicator,
        allocator: std.mem.Allocator,
        from: u256,
        to: u256,
    ) std.mem.Allocator.Error!void {
        const index = lowerBoundReplacement(self.replaced_tags.items, from);
        if (index < self.replaced_tags.items.len and self.replaced_tags.items[index].from == from) {
            self.replaced_tags.items[index].to = to;
        } else {
            try self.replaced_tags.insert(allocator, index, .{ .from = from, .to = to });
        }
    }
};

pub fn applyTagReplacement(
    items: []AssemblyItem,
    replacements: []const TagReplacement,
    sub_id_filter: SubAssemblyID,
) bool {
    var changed = false;
    for (items) |*item| {
        if (item.item_type != .PushTag) continue;
        const split = item.splitForeignPushTag() catch unreachable; // zlinter-disable-current-line no_swallow_error - assembly item kind was checked immediately before this invariant conversion
        if (!split[0].eql(sub_id_filter)) continue;

        var replacement = findReplacement(replacements, split[1]);
        var final: ?u256 = null;
        while (replacement) |entry| {
            final = entry.to;
            replacement = findReplacement(replacements, entry.to);
        }
        if (final) |tag_id| {
            changed = true;
            item.setPushTagSubIdAndTag(split[0], @as(usize, @truncate(tag_id))) catch unreachable; // zlinter-disable-current-line no_swallow_error - assembly item kind was checked immediately before this invariant conversion
        }
    }
    return changed;
}

const BlockCursor = struct {
    index: usize,
    end: usize,
    replace_item: *const AssemblyItem,
    replace_with: *const AssemblyItem,

    fn current(self: *const BlockCursor, items: []const AssemblyItem) *const AssemblyItem {
        const item = &items[self.index];
        return if (item.eql(self.replace_item)) self.replace_with else item;
    }

    fn advance(self: *BlockCursor, items: []const AssemblyItem) void {
        if (self.index == self.end) return;
        const item = &items[self.index];
        if (SemanticInformation.altersControlFlow(item) and !item.eqlInstruction(.JUMPI)) {
            self.index = self.end;
            return;
        }
        self.index += 1;
        while (self.index < self.end and items[self.index].item_type == .Tag) self.index += 1;
    }
};

fn blockLess(items: []const AssemblyItem, left_index: usize, right_index: usize, push_self: *const AssemblyItem) bool {
    if (left_index == right_index) return false;
    var left_tag = push_self.*;
    var right_tag = push_self.*;
    if (left_index < items.len and items[left_index].item_type == .Tag) {
        left_tag = items[left_index].pushTag() catch unreachable; // zlinter-disable-current-line no_swallow_error - assembly item kind was checked immediately before this invariant conversion
    }
    if (right_index < items.len and items[right_index].item_type == .Tag) {
        right_tag = items[right_index].pushTag() catch unreachable; // zlinter-disable-current-line no_swallow_error - assembly item kind was checked immediately before this invariant conversion
    }
    var left: BlockCursor = .{
        .index = left_index,
        .end = items.len,
        .replace_item = &left_tag,
        .replace_with = push_self,
    };
    var right: BlockCursor = .{
        .index = right_index,
        .end = items.len,
        .replace_item = &right_tag,
        .replace_with = push_self,
    };
    if (left.index < left.end and items[left.index].item_type == .Tag) left.advance(items);
    if (right.index < right.end and items[right.index].item_type == .Tag) right.advance(items);

    while (left.index < left.end and right.index < right.end) {
        const left_item = left.current(items);
        const right_item = right.current(items);
        if (left_item.lessThan(right_item)) return true;
        if (right_item.lessThan(left_item)) return false;
        left.advance(items);
        right.advance(items);
    }
    return left.index == left.end and right.index != right.end;
}

fn lowerBoundBlock(
    items: []const AssemblyItem,
    indices: []const usize,
    index: usize,
    push_self: *const AssemblyItem,
) usize {
    var lower: usize = 0;
    var upper = indices.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (blockLess(items, indices[middle], index, push_self)) lower = middle + 1 else upper = middle;
    }
    return lower;
}

fn lowerBoundReplacement(replacements: []const TagReplacement, from: u256) usize {
    var lower: usize = 0;
    var upper = replacements.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (replacements[middle].from < from) lower = middle + 1 else upper = middle;
    }
    return lower;
}

fn findReplacement(replacements: []const TagReplacement, from: u256) ?TagReplacement {
    const index = lowerBoundReplacement(replacements, from);
    return if (index < replacements.len and replacements[index].from == from)
        replacements[index]
    else
        null;
}

test "identical terminal blocks are unified and tag references are rewritten" {
    var items: std.ArrayList(AssemblyItem) = .empty;
    defer {
        for (items.items) |*item| item.deinit(std.testing.allocator);
        items.deinit(std.testing.allocator);
    }
    try items.appendSlice(std.testing.allocator, &.{
        AssemblyItem.initType(.Tag, 1, .{}),
        AssemblyItem.initPush(42, .{}),
        AssemblyItem.initInstruction(.STOP, .{}),
        AssemblyItem.initType(.Tag, 2, .{}),
        AssemblyItem.initPush(42, .{}),
        AssemblyItem.initInstruction(.STOP, .{}),
        AssemblyItem.initType(.PushTag, 2, .{}),
    });
    var deduplicator: BlockDeduplicator = .{};
    defer deduplicator.deinit(std.testing.allocator);
    try std.testing.expect(try deduplicator.deduplicate(std.testing.allocator, &items));
    try std.testing.expectEqual(@as(usize, 1), deduplicator.replacements().len);
    try std.testing.expectEqual(@as(u256, 2), deduplicator.replacements()[0].from);
    try std.testing.expectEqual(@as(u256, 1), deduplicator.replacements()[0].to);
    try std.testing.expectEqual(@as(u256, 1), items.items[6].data_value);
}

test "foreign replacement filtering preserves unrelated subassemblies" {
    const local = AssemblyItem.initType(.PushTag, 2, .{});
    var foreign = AssemblyItem.initType(.PushTag, 2, .{});
    try foreign.setPushTagSubIdAndTag(SubAssemblyID.init(3), 2);
    var items = [_]AssemblyItem{ local, foreign };
    try std.testing.expect(applyTagReplacement(&items, &.{.{ .from = 2, .to = 9 }}, SubAssemblyID.init(3)));
    try std.testing.expectEqual(@as(u256, 2), items[0].data_value);
    try std.testing.expectEqual(@as(usize, 9), (try items[1].splitForeignPushTag())[1]);
}
