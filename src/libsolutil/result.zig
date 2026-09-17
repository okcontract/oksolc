// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `libsolutil/Result.h`.

const std = @import("std");
const cxx_compat = @import("cxx_compat");

/// Provides the source template's default-error value for common translated
/// result types. More complex values use `ResultWithDefault` explicitly.
pub fn Result(comptime T: type) type {
    return ResultWithDefault(T, comptime defaultValue(T));
}

/// Result type for trivially copied or externally owned values.
pub fn ResultWithDefault(comptime T: type, comptime default_value: T) type {
    return ResultImpl(T, default_value, null);
}

/// Result type for allocator-owning values. `default_value` must be an empty,
/// non-owning value that can safely be copied when an error/result is reset.
pub fn ResultWithLifecycle(
    comptime T: type,
    comptime default_value: T,
    comptime deinit_value: *const fn (*T, std.mem.Allocator) void,
) type {
    return ResultImpl(T, default_value, deinit_value);
}

fn ResultImpl(
    comptime T: type,
    comptime default_value: T,
    comptime deinit_value: ?*const fn (*T, std.mem.Allocator) void,
) type {
    return struct {
        const Self = @This();

        value: T,
        error_message: cxx_compat.OwnedString = .{},

        pub fn init(value: T) Self {
            return .{ .value = value };
        }

        pub fn err(
            allocator: std.mem.Allocator,
            error_bytes: []const u8,
        ) std.mem.Allocator.Error!Self {
            return .{
                .value = default_value,
                .error_message = try cxx_compat.OwnedString.init(allocator, error_bytes),
            };
        }

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.error_message.deinit(allocator);
            if (deinit_value) |destroy| destroy(&self.value, allocator);
            self.* = init(default_value);
        }

        pub fn get(self: *const Self) *const T {
            return &self.value;
        }

        pub fn message(self: *const Self) []const u8 {
            return self.error_message.bytes();
        }

        /// Preserves the C++ operation order: merge the value first, then
        /// append the other diagnostic. Allocation failure may therefore leave
        /// the merged value committed while retaining a valid old message.
        pub fn merge(
            self: *Self,
            allocator: std.mem.Allocator,
            other: *const Self,
            context: anytype,
            comptime merger: anytype,
        ) std.mem.Allocator.Error!void {
            if (deinit_value != null) @compileError(
                "allocator-owning Result values must use mergeWith()",
            );
            self.value = merger(context, self.value, other.value);
            try self.error_message.append(allocator, other.message());
        }

        /// Lifecycle-aware merge. The merger mutates the existing value so it
        /// can reuse or tear down owned storage before replacing it.
        pub fn mergeWith(
            self: *Self,
            allocator: std.mem.Allocator,
            other: *const Self,
            context: anytype,
            comptime merger: anytype,
        ) std.mem.Allocator.Error!void {
            try merger(context, allocator, &self.value, &other.value);
            try self.error_message.append(allocator, other.message());
        }

        /// Transfers owned message storage and resets the source.
        pub fn take(self: *Self) Self {
            const moved = self.*;
            self.* = init(default_value);
            return moved;
        }
    };
}

fn defaultValue(comptime T: type) T {
    return switch (@typeInfo(T)) {
        .bool => false,
        .optional => null,
        else => @compileError(
            "Result(T) has no structural default for this type; use ResultWithDefault(T, value)",
        ),
    };
}

fn logicalAnd(_: void, lhs: bool, rhs: bool) bool {
    return lhs and rhs;
}

fn takeRight(_: void, _: []const u8, rhs: []const u8) []const u8 {
    return rhs;
}

test "bool results match upstream merge behavior" {
    const BoolResult = Result(bool);
    var success = BoolResult.init(true);
    defer success.deinit(std.testing.allocator);
    var failure = try BoolResult.err(std.testing.allocator, "Failure.");
    defer failure.deinit(std.testing.allocator);
    try success.merge(std.testing.allocator, &failure, {}, logicalAnd);
    try std.testing.expect(!success.get().*);
    try std.testing.expectEqualStrings("Failure.", success.message());

    var both = BoolResult.init(true);
    defer both.deinit(std.testing.allocator);
    var other = BoolResult.init(true);
    defer other.deinit(std.testing.allocator);
    try both.merge(std.testing.allocator, &other, {}, logicalAnd);
    try std.testing.expect(both.get().*);
    try std.testing.expectEqualStrings("", both.message());
}

test "self merge safely appends its own diagnostic" {
    const BoolResult = Result(bool);
    var value = try BoolResult.err(std.testing.allocator, "Failure.");
    defer value.deinit(std.testing.allocator);

    try value.merge(std.testing.allocator, &value, {}, logicalAnd);
    try std.testing.expectEqualStrings("Failure.Failure.", value.message());
}

test "custom defaults preserve string-result behavior" {
    const StringResult = ResultWithDefault([]const u8, "");
    var success = StringResult.init("Success");
    defer success.deinit(std.testing.allocator);
    var failure = try StringResult.err(std.testing.allocator, "Failure");
    defer failure.deinit(std.testing.allocator);
    try success.merge(std.testing.allocator, &failure, {}, takeRight);
    try std.testing.expectEqualStrings("", success.get().*);
    try std.testing.expectEqualStrings("Failure", success.message());
}

const ByteVector = cxx_compat.Vector(u8);

fn deinitByteVector(value: *ByteVector, allocator: std.mem.Allocator) void {
    value.deinit(allocator);
}

fn appendByteVector(
    _: void,
    allocator: std.mem.Allocator,
    left: *ByteVector,
    right: *const ByteVector,
) std.mem.Allocator.Error!void {
    try left.appendSlice(allocator, right.constItems());
}

test "owning Result values use explicit lifecycle-aware merge and teardown" {
    const VectorResult = ResultWithLifecycle(ByteVector, .{}, deinitByteVector);
    var left_value: ByteVector = .{};
    try left_value.appendSlice(std.testing.allocator, "left");
    var left = VectorResult.init(left_value);
    defer left.deinit(std.testing.allocator);

    var right_value: ByteVector = .{};
    try right_value.appendSlice(std.testing.allocator, "right");
    var right = VectorResult.init(right_value);
    defer right.deinit(std.testing.allocator);

    try left.mergeWith(std.testing.allocator, &right, {}, appendByteVector);
    try std.testing.expectEqualStrings("leftright", left.get().constItems());
}

fn exerciseAllocationFailure(allocator: std.mem.Allocator) !void {
    const BoolResult = Result(bool);
    var lhs = BoolResult.init(true);
    defer lhs.deinit(allocator);
    var rhs = try BoolResult.err(allocator, "a diagnostic that owns storage");
    defer rhs.deinit(allocator);
    try lhs.merge(allocator, &rhs, {}, logicalAnd);
}

test "result diagnostics are leak-free on allocation failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        exerciseAllocationFailure,
        .{},
    );
}
