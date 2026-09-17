// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `libsolutil/LazyInit.h`.

const std = @import("std");

pub fn LazyInit(comptime T: type) type {
    return struct {
        const Self = @This();

        value: ?T = null,

        pub fn init(
            self: *Self,
            context: anytype,
            comptime factory: anytype,
        ) *T {
            if (self.value == null) self.value = factory(context);
            return &self.value.?;
        }

        /// Mirrors the upstream logically-const overload backed by its
        /// `mutable std::optional`. The returned view remains const.
        pub fn initConst(
            self: *const Self,
            context: anytype,
            comptime factory: anytype,
        ) *const T {
            const mutable_self: *Self = @constCast(self);
            if (mutable_self.value == null) mutable_self.value = factory(context);
            return &mutable_self.value.?;
        }

        pub fn tryInit(
            self: *Self,
            comptime Error: type,
            context: anytype,
            comptime factory: anytype,
        ) Error!*T {
            if (self.value == null) self.value = try factory(context);
            return &self.value.?;
        }

        pub fn tryInitConst(
            self: *const Self,
            comptime Error: type,
            context: anytype,
            comptime factory: anytype,
        ) Error!*const T {
            const mutable_self: *Self = @constCast(self);
            if (mutable_self.value == null) mutable_self.value = try factory(context);
            return &mutable_self.value.?;
        }

        pub fn isInitialized(self: *const Self) bool {
            return self.value != null;
        }

        /// Structural move construction: the destination receives the value
        /// and the moved-from source is explicitly empty.
        pub fn take(self: *Self) Self {
            const moved = self.*;
            self.value = null;
            return moved;
        }

        pub fn resetWith(
            self: *Self,
            context: anytype,
            comptime deinit_value: anytype,
        ) void {
            if (self.value) |*value| deinit_value(context, value);
            self.value = null;
        }

        /// Structural move assignment. Any old destination value is destroyed
        /// through the supplied operation before ownership transfers.
        pub fn moveAssignWith(
            self: *Self,
            other: *Self,
            context: anytype,
            comptime deinit_value: anytype,
        ) void {
            if (self == other) return;
            self.resetWith(context, deinit_value);
            self.* = other.take();
        }
    };
}

fn intFactory(value: i32) i32 {
    return value;
}

fn failFactory(_: void) error{FactoryFailed}!i32 {
    return error.FactoryFailed;
}

fn noDeinit(_: void, _: *i32) void {}

test "initialization runs once and returns stable storage" {
    var lazy: LazyInit(i32) = .{};
    try std.testing.expect(!lazy.isInitialized());
    try std.testing.expectEqual(@as(i32, 12), lazy.init(@as(i32, 12), intFactory).*);
    try std.testing.expectEqual(@as(i32, 12), lazy.init(@as(i32, 42), intFactory).*);
    try std.testing.expect(lazy.isInitialized());
}

test "const views retain lazy initialization" {
    var lazy: LazyInit(i32) = .{};
    const const_view: *const LazyInit(i32) = &lazy;
    try std.testing.expectEqual(@as(i32, 12), const_view.initConst(@as(i32, 12), intFactory).*);
    try std.testing.expectEqual(@as(i32, 12), const_view.initConst(@as(i32, 42), intFactory).*);
    try std.testing.expect(lazy.isInitialized());
}

test "fallible initialization leaves failure empty" {
    var lazy: LazyInit(i32) = .{};
    try std.testing.expectError(
        error.FactoryFailed,
        lazy.tryInit(error{FactoryFailed}, {}, failFactory),
    );
    try std.testing.expect(!lazy.isInitialized());
}

test "move construction and assignment empty moved-from values" {
    var original: LazyInit(i32) = .{};
    _ = original.init(@as(i32, 12), intFactory);
    var moved = original.take();
    try std.testing.expect(!original.isInitialized());
    try std.testing.expectEqual(@as(i32, 12), moved.value.?);

    var destination: LazyInit(i32) = .{};
    _ = destination.init(@as(i32, 99), intFactory);
    destination.moveAssignWith(&moved, {}, noDeinit);
    try std.testing.expect(!moved.isInitialized());
    try std.testing.expectEqual(@as(i32, 12), destination.value.?);
}
