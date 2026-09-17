// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic sorted-vector compatibility containers for `std::map` and
//! `std::set`, preserving source correspondence and stable iteration.

const std = @import("std");

pub fn OrderedMap(
    comptime Key: type,
    comptime Value: type,
    comptime less_than: fn (Key, Key) bool,
) type {
    return struct {
        const Self = @This();

        pub const Entry = struct {
            key: Key,
            value: Value,
        };

        pub const SearchResult = struct {
            index: usize,
            found: bool,
        };

        entries: std.ArrayList(Entry) = .empty,

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.entries.deinit(allocator);
            self.* = undefined;
        }

        pub fn len(self: *const Self) usize {
            return self.entries.items.len;
        }

        pub fn isEmpty(self: *const Self) bool {
            return self.entries.items.len == 0;
        }

        pub fn items(self: *const Self) []const Entry {
            return self.entries.items;
        }

        pub fn mutableItems(self: *Self) []Entry {
            return self.entries.items;
        }

        pub fn search(self: *const Self, key: Key) SearchResult {
            var lower: usize = 0;
            var upper = self.entries.items.len;
            while (lower < upper) {
                const middle = lower + (upper - lower) / 2;
                const candidate = self.entries.items[middle].key;
                if (less_than(candidate, key)) {
                    lower = middle + 1;
                } else {
                    upper = middle;
                }
            }
            const found = lower < self.entries.items.len and
                !less_than(key, self.entries.items[lower].key) and
                !less_than(self.entries.items[lower].key, key);
            return .{ .index = lower, .found = found };
        }

        pub fn contains(self: *const Self, key: Key) bool {
            return self.search(key).found;
        }

        pub fn get(self: *const Self, key: Key) ?*const Value {
            const result = self.search(key);
            return if (result.found) &self.entries.items[result.index].value else null;
        }

        pub fn getPtr(self: *Self, key: Key) ?*Value {
            const result = self.search(key);
            return if (result.found) &self.entries.items[result.index].value else null;
        }

        /// Inserts only when absent. Ownership of `key` and `value` transfers
        /// exactly when this returns true.
        pub fn insert(
            self: *Self,
            allocator: std.mem.Allocator,
            key: Key,
            value: Value,
        ) std.mem.Allocator.Error!bool {
            const result = self.search(key);
            if (result.found) return false;
            try self.entries.insert(allocator, result.index, .{ .key = key, .value = value });
            return true;
        }

        /// Inserts or replaces and returns the displaced entry, if any.
        pub fn fetchPut(
            self: *Self,
            allocator: std.mem.Allocator,
            key: Key,
            value: Value,
        ) std.mem.Allocator.Error!?Entry {
            const result = self.search(key);
            if (result.found) {
                const previous = self.entries.items[result.index];
                self.entries.items[result.index] = .{ .key = key, .value = value };
                return previous;
            }
            try self.entries.insert(allocator, result.index, .{ .key = key, .value = value });
            return null;
        }

        /// Inserts or replaces without materializing the displaced entry.
        /// Use this only when the old key and value carry no ownership that
        /// the caller must release.
        pub fn put(
            self: *Self,
            allocator: std.mem.Allocator,
            key: Key,
            value: Value,
        ) std.mem.Allocator.Error!void {
            const result = self.search(key);
            if (result.found) {
                self.entries.items[result.index] = .{ .key = key, .value = value };
                return;
            }
            try self.entries.insert(allocator, result.index, .{ .key = key, .value = value });
        }

        pub fn remove(self: *Self, key: Key) ?Entry {
            const result = self.search(key);
            if (!result.found) return null;
            return self.entries.orderedRemove(result.index);
        }

        pub fn clearRetainingCapacity(self: *Self) void {
            self.entries.clearRetainingCapacity();
        }

        pub fn clone(self: *const Self, allocator: std.mem.Allocator) std.mem.Allocator.Error!Self {
            var result: Self = .{};
            errdefer result.deinit(allocator);
            try result.entries.appendSlice(allocator, self.entries.items);
            return result;
        }

        pub fn take(self: *Self) Self {
            const result = self.*;
            self.* = .{};
            return result;
        }
    };
}

pub fn OrderedSet(comptime Key: type, comptime less_than: fn (Key, Key) bool) type {
    return struct {
        const Self = @This();
        const Map = OrderedMap(Key, void, less_than);

        map: Map = .{},

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.map.deinit(allocator);
            self.* = undefined;
        }

        pub fn len(self: *const Self) usize {
            return self.map.len();
        }

        pub fn isEmpty(self: *const Self) bool {
            return self.map.isEmpty();
        }

        pub fn contains(self: *const Self, key: Key) bool {
            return self.map.contains(key);
        }

        pub fn insert(
            self: *Self,
            allocator: std.mem.Allocator,
            key: Key,
        ) std.mem.Allocator.Error!bool {
            return self.map.insert(allocator, key, {});
        }

        pub fn remove(self: *Self, key: Key) bool {
            return self.map.remove(key) != null;
        }

        pub fn at(self: *const Self, index: usize) Key {
            return self.map.entries.items[index].key;
        }

        pub fn clone(self: *const Self, allocator: std.mem.Allocator) std.mem.Allocator.Error!Self {
            return .{ .map = try self.map.clone(allocator) };
        }

        pub fn take(self: *Self) Self {
            return .{ .map = self.map.take() };
        }
    };
}

fn lessU32(lhs: u32, rhs: u32) bool {
    return lhs < rhs;
}

test "ordered map and set preserve lexical ordering and ownership transfer" {
    const Map = OrderedMap(u32, []const u8, lessU32);
    var map: Map = .{};
    defer map.deinit(std.testing.allocator);
    try std.testing.expect(try map.insert(std.testing.allocator, 3, "three"));
    try std.testing.expect(try map.insert(std.testing.allocator, 1, "one"));
    try std.testing.expect(try map.insert(std.testing.allocator, 2, "two"));
    try std.testing.expect(!(try map.insert(std.testing.allocator, 2, "ignored")));
    try std.testing.expectEqualSlices(u32, &.{ 1, 2, 3 }, &.{
        map.items()[0].key,
        map.items()[1].key,
        map.items()[2].key,
    });
    try std.testing.expectEqualStrings("two", map.get(2).?.*);
    try map.put(std.testing.allocator, 2, "replaced");
    try std.testing.expectEqualStrings("replaced", map.get(2).?.*);
    try map.put(std.testing.allocator, 4, "four");
    try std.testing.expectEqual(@as(usize, 4), map.len());

    const Set = OrderedSet(u32, lessU32);
    var set: Set = .{};
    defer set.deinit(std.testing.allocator);
    _ = try set.insert(std.testing.allocator, 8);
    _ = try set.insert(std.testing.allocator, 4);
    try std.testing.expectEqual(@as(u32, 4), set.at(0));
    try std.testing.expect(set.remove(8));
}
