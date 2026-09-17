// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of the common byte aliases and scope helpers in
//! `Common.h`. Allocator ownership remains explicit at call sites.

const std = @import("std");
const refs = @import("vector_ref.zig");

pub const Bytes = []u8;
pub const ConstBytes = []const u8;
pub const BytesRef = refs.BytesRef;
pub const BytesConstRef = refs.BytesConstRef;

pub fn ScopeGuard(comptime Context: type) type {
    return struct {
        const Self = @This();

        context: *Context,
        callback: *const fn (*Context) void,
        armed: bool = true,

        pub fn init(context: *Context, callback: *const fn (*Context) void) Self {
            return .{ .context = context, .callback = callback };
        }

        pub fn dismiss(self: *Self) void {
            self.armed = false;
        }

        pub fn deinit(self: *Self) void {
            if (self.armed) self.callback(self.context);
            self.* = undefined;
        }
    };
}

pub fn ScopedSaveAndRestore(comptime T: type) type {
    return struct {
        const Self = @This();

        variable: *T,
        old_value: T,

        pub fn init(variable: *T, replacement: T) Self {
            const old_value = variable.*;
            variable.* = replacement;
            return .{ .variable = variable, .old_value = old_value };
        }

        pub fn deinit(self: *Self) void {
            const current = self.variable.*;
            self.variable.* = self.old_value;
            self.old_value = current;
            self.* = undefined;
        }
    };
}

test "scope helpers run once and restore values" {
    const Context = struct { calls: usize = 0 };
    const Helpers = struct {
        fn call(context: *Context) void {
            context.calls += 1;
        }
    };
    var context: Context = .{};
    {
        var guard = ScopeGuard(Context).init(&context, Helpers.call);
        defer guard.deinit();
    }
    try std.testing.expectEqual(@as(usize, 1), context.calls);

    var value: i32 = 3;
    {
        var saved = ScopedSaveAndRestore(i32).init(&value, 7);
        defer saved.deinit();
        try std.testing.expectEqual(@as(i32, 7), value);
    }
    try std.testing.expectEqual(@as(i32, 3), value);
}
