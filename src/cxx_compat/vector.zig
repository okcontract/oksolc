// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");

/// Narrow `std::vector` compatibility wrapper over Zig 0.16's unmanaged list.
///
/// Pointers and slices returned by `items` are invalidated by any operation
/// that can grow capacity. Element teardown remains the caller's responsibility.
pub fn Vector(comptime T: type) type {
    return struct {
        const Self = @This();

        storage: std.ArrayList(T) = .empty,

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.storage.deinit(allocator);
            self.* = undefined;
        }

        pub fn append(
            self: *Self,
            allocator: std.mem.Allocator,
            value: T,
        ) std.mem.Allocator.Error!void {
            try self.storage.append(allocator, value);
        }

        pub fn appendSlice(
            self: *Self,
            allocator: std.mem.Allocator,
            values: []const T,
        ) std.mem.Allocator.Error!void {
            try self.storage.appendSlice(allocator, values);
        }

        pub fn reserve(
            self: *Self,
            allocator: std.mem.Allocator,
            total_capacity: usize,
        ) std.mem.Allocator.Error!void {
            try self.storage.ensureTotalCapacity(allocator, total_capacity);
        }

        pub fn clearRetainingCapacity(self: *Self) void {
            self.storage.clearRetainingCapacity();
        }

        pub fn len(self: *const Self) usize {
            return self.storage.items.len;
        }

        pub fn last(self: *Self) *T {
            std.debug.assert(self.storage.items.len != 0);
            return &self.storage.items[self.storage.items.len - 1];
        }

        pub fn pop(self: *Self) ?T {
            return self.storage.pop();
        }

        pub fn items(self: *Self) []T {
            return self.storage.items;
        }

        pub fn constItems(self: *const Self) []const T {
            return self.storage.items;
        }

        pub fn capacity(self: *const Self) usize {
            return self.storage.capacity;
        }

        /// Transfers ownership of the allocation to the caller and empties
        /// this vector. The returned slice must be freed with `allocator`.
        pub fn toOwnedSlice(
            self: *Self,
            allocator: std.mem.Allocator,
        ) std.mem.Allocator.Error![]T {
            return self.storage.toOwnedSlice(allocator);
        }
    };
}

test "Vector preserves insertion order" {
    var values: Vector(u32) = .{};
    defer values.deinit(std.testing.allocator);

    try values.reserve(std.testing.allocator, 3);
    try values.appendSlice(std.testing.allocator, &.{ 3, 1, 2 });

    try std.testing.expectEqualSlices(u32, &.{ 3, 1, 2 }, values.constItems());
    try std.testing.expect(values.capacity() >= 3);
}

test "Vector can be reused without releasing capacity" {
    var values: Vector(u8) = .{};
    defer values.deinit(std.testing.allocator);

    try values.appendSlice(std.testing.allocator, "first");
    const old_capacity = values.capacity();
    values.clearRetainingCapacity();
    try values.appendSlice(std.testing.allocator, "next");

    try std.testing.expectEqualStrings("next", values.constItems());
    try std.testing.expectEqual(old_capacity, values.capacity());
}

test "Vector can transfer its allocation" {
    var values: Vector(u8) = .{};
    defer values.deinit(std.testing.allocator);

    try values.appendSlice(std.testing.allocator, "owned");
    const owned = try values.toOwnedSlice(std.testing.allocator);
    defer std.testing.allocator.free(owned);

    try std.testing.expectEqualStrings("owned", owned);
    try std.testing.expectEqual(@as(usize, 0), values.constItems().len);
    try std.testing.expectEqual(@as(usize, 0), values.capacity());
}

test "Vector exposes stack operations without changing order" {
    var values: Vector(u8) = .{};
    defer values.deinit(std.testing.allocator);
    try values.appendSlice(std.testing.allocator, "abc");

    try std.testing.expectEqual(@as(usize, 3), values.len());
    values.last().* = 'd';
    try std.testing.expectEqual(@as(?u8, 'd'), values.pop());
    try std.testing.expectEqualStrings("ab", values.constItems());
}
