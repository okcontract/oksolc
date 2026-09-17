// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");

/// Allocator-owned bytes used where translated C++ requires `std::string`
/// ownership and append behavior. The empty value owns no allocation.
pub const OwnedString = struct {
    storage: std.ArrayList(u8) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        initial_bytes: []const u8,
    ) std.mem.Allocator.Error!OwnedString {
        var result: OwnedString = .{};
        errdefer result.deinit(allocator);
        try result.storage.appendSlice(allocator, initial_bytes);
        return result;
    }

    pub fn deinit(self: *OwnedString, allocator: std.mem.Allocator) void {
        self.storage.deinit(allocator);
        self.* = .{};
    }

    pub fn bytes(self: *const OwnedString) []const u8 {
        return self.storage.items;
    }

    pub fn append(
        self: *OwnedString,
        allocator: std.mem.Allocator,
        suffix: []const u8,
    ) std.mem.Allocator.Error!void {
        if (suffix.len == 0) return;

        // ArrayList growth invalidates a borrowed slice into its old storage.
        // Retain an offset across growth for `string += string` and subslices.
        const current = self.storage.items;
        if (current.len != 0) {
            const current_address = @intFromPtr(current.ptr);
            const suffix_address = @intFromPtr(suffix.ptr);
            if (suffix_address >= current_address) {
                const offset = suffix_address - current_address;
                if (offset <= current.len and suffix.len <= current.len - offset) {
                    try self.storage.ensureUnusedCapacity(allocator, suffix.len);
                    const stable_suffix = self.storage.items[offset..][0..suffix.len];
                    self.storage.appendSliceAssumeCapacity(stable_suffix);
                    return;
                }
            }
        }
        try self.storage.appendSlice(allocator, suffix);
    }

    pub fn clone(
        self: *const OwnedString,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!OwnedString {
        return init(allocator, self.bytes());
    }

    /// Transfers the allocation and resets the source to its empty state.
    pub fn take(self: *OwnedString) OwnedString {
        const result = self.*;
        self.* = .{};
        return result;
    }
};

test "OwnedString appends, clones, and transfers ownership" {
    var value = try OwnedString.init(std.testing.allocator, "first");
    defer value.deinit(std.testing.allocator);
    try value.append(std.testing.allocator, " second");

    var cloned = try value.clone(std.testing.allocator);
    defer cloned.deinit(std.testing.allocator);
    try std.testing.expectEqualStrings("first second", cloned.bytes());

    var moved = cloned.take();
    defer moved.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 0), cloned.bytes().len);
    try std.testing.expectEqualStrings("first second", moved.bytes());
}

test "OwnedString safely appends itself and an internal subslice" {
    var value = try OwnedString.init(std.testing.allocator, "abcdef");
    defer value.deinit(std.testing.allocator);

    try value.append(std.testing.allocator, value.bytes());
    try std.testing.expectEqualStrings("abcdefabcdef", value.bytes());
    try value.append(std.testing.allocator, value.bytes()[2..5]);
    try std.testing.expectEqualStrings("abcdefabcdefcde", value.bytes());
}

fn exerciseAllocationFailure(allocator: std.mem.Allocator) !void {
    var value = try OwnedString.init(allocator, "message");
    defer value.deinit(allocator);
    try value.append(allocator, " with a suffix large enough to force growth");
}

fn exerciseAliasedAllocationFailure(allocator: std.mem.Allocator) !void {
    var value = try OwnedString.init(allocator, "a diagnostic that owns storage");
    defer value.deinit(allocator);
    try value.append(allocator, value.bytes());
}

test "OwnedString append is leak-free on allocation failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        exerciseAllocationFailure,
        .{},
    );
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        exerciseAliasedAllocationFailure,
        .{},
    );
}
