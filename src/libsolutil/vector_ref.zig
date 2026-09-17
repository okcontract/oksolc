// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `vector_ref.h` using explicit borrowed slices.

const std = @import("std");

pub fn VectorRef(comptime T: type) type {
    return struct {
        const Self = @This();

        data_pointer: ?[*]T = null,
        count: usize = 0,

        pub fn init(input_slice: []T) Self {
            return if (input_slice.len == 0)
                .{}
            else
                .{ .data_pointer = input_slice.ptr, .count = input_slice.len };
        }

        pub fn initPointer(pointer: ?[*]T, count: usize) Self {
            if (pointer == null or count == 0) return .{};
            return .{ .data_pointer = pointer, .count = count };
        }

        pub fn isPresent(self: Self) bool {
            return self.data_pointer != null and self.count != 0;
        }

        pub fn data(self: Self) ?[*]T {
            return self.data_pointer;
        }

        pub fn size(self: Self) usize {
            return self.count;
        }

        pub fn empty(self: Self) bool {
            return self.count == 0;
        }

        pub fn slice(self: Self) []T {
            if (self.data_pointer) |pointer| return pointer[0..self.count];
            return &.{};
        }

        pub fn constSlice(self: Self) []const T {
            return self.slice();
        }

        pub fn croppedCount(self: Self, begin: usize, count: usize) Self {
            if (self.data_pointer == null or begin > self.count or
                count > self.count or begin > self.count - count)
            {
                return .{};
            }
            return .{
                .data_pointer = self.data_pointer.? + begin,
                .count = count,
            };
        }

        pub fn cropped(self: Self, begin: usize) Self {
            if (self.data_pointer == null or begin > self.count) return .{};
            return .{
                .data_pointer = self.data_pointer.? + begin,
                .count = self.count - begin,
            };
        }

        pub fn at(self: Self, index: usize) *T {
            std.debug.assert(self.data_pointer != null and index < self.count);
            return &self.data_pointer.?[index];
        }

        pub fn eqlIdentity(self: Self, other: Self) bool {
            return self.data_pointer == other.data_pointer and self.count == other.count;
        }

        pub fn reset(self: *Self) void {
            self.* = .{};
        }

        pub fn toBytesAlloc(self: Self, allocator: std.mem.Allocator) ![]u8 {
            return allocator.dupe(u8, std.mem.sliceAsBytes(self.constSlice()));
        }

        pub fn toStringAlloc(self: Self, allocator: std.mem.Allocator) ![]u8 {
            return self.toBytesAlloc(allocator);
        }
    };
}

pub fn ConstVectorRef(comptime T: type) type {
    return struct {
        const Self = @This();

        data_pointer: ?[*]const T = null,
        count: usize = 0,

        pub fn init(slice_value: []const T) Self {
            return if (slice_value.len == 0)
                .{}
            else
                .{ .data_pointer = slice_value.ptr, .count = slice_value.len };
        }

        pub fn slice(self: Self) []const T {
            if (self.data_pointer) |pointer| return pointer[0..self.count];
            return &.{};
        }

        pub fn size(self: Self) usize {
            return self.count;
        }

        pub fn empty(self: Self) bool {
            return self.count == 0;
        }

        pub fn croppedCount(self: Self, begin: usize, count: usize) Self {
            if (self.data_pointer == null or begin > self.count or
                count > self.count or begin > self.count - count)
            {
                return .{};
            }
            return .{ .data_pointer = self.data_pointer.? + begin, .count = count };
        }

        pub fn cropped(self: Self, begin: usize) Self {
            if (self.data_pointer == null or begin > self.count) return .{};
            return .{
                .data_pointer = self.data_pointer.? + begin,
                .count = self.count - begin,
            };
        }
    };
}

pub const BytesRef = VectorRef(u8);
pub const BytesConstRef = ConstVectorRef(u8);

test "vector_ref preserves borrowed identity and checked crops" {
    var bytes = [_]u8{ 1, 2, 3, 4 };
    var reference = VectorRef(u8).init(&bytes);
    try std.testing.expect(reference.isPresent());
    try std.testing.expectEqualSlices(u8, &.{ 2, 3 }, reference.croppedCount(1, 2).slice());
    try std.testing.expect(reference.croppedCount(3, 2).empty());
    reference.at(0).* = 9;
    try std.testing.expectEqual(@as(u8, 9), bytes[0]);
    reference.reset();
    try std.testing.expect(reference.empty());
}
