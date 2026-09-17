// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `libsolutil/SetOnce.h`.

const std = @import("std");

pub const SetOnceError = error{
    BadSetOnceReassignment,
    BadSetOnceAccess,
};

pub const reassignment_message =
    "Attempt to reassign to a SetOnce that already has a value.";
pub const access_message =
    "Attempt to access the value of a SetOnce that does not have a value.";

pub fn SetOnce(comptime T: type) type {
    return struct {
        const Self = @This();

        value: ?T = null,

        pub fn assign(self: *Self, new_value: T) SetOnceError!void {
            if (self.value != null) return error.BadSetOnceReassignment;
            self.value = new_value;
        }

        pub fn get(self: *const Self) SetOnceError!*const T {
            if (self.value == null) return error.BadSetOnceAccess;
            return &self.value.?;
        }

        pub fn isSet(self: *const Self) bool {
            return self.value != null;
        }

        pub fn deinitWith(
            self: *Self,
            context: anytype,
            comptime deinit_value: anytype,
        ) void {
            if (self.value) |*value| deinit_value(context, value);
            self.value = null;
        }
    };
}

test "SetOnce preserves assignment and access failure classes" {
    var value: SetOnce(u32) = .{};
    try std.testing.expect(!value.isSet());
    try std.testing.expectError(error.BadSetOnceAccess, value.get());

    try value.assign(42);
    try std.testing.expect(value.isSet());
    try std.testing.expectEqual(@as(u32, 42), (try value.get()).*);
    try std.testing.expectError(error.BadSetOnceReassignment, value.assign(99));
    try std.testing.expectEqual(@as(u32, 42), (try value.get()).*);
    try std.testing.expectEqualStrings(
        "Attempt to reassign to a SetOnce that already has a value.",
        reassignment_message,
    );
    try std.testing.expectEqualStrings(
        "Attempt to access the value of a SetOnce that does not have a value.",
        access_message,
    );
}
