// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Fixed-width subassembly identity translated from `SubAssemblyID.h`.

const std = @import("std");

pub const SubAssemblyID = struct {
    pub const ValueType = u64;
    pub const empty_value = std.math.maxInt(ValueType);

    value: ValueType = empty_value,

    pub fn init(value: ValueType) SubAssemblyID {
        return .{ .value = value };
    }

    pub fn fromU256(value: u256) error{Overflow}!SubAssemblyID {
        if (value > std.math.maxInt(ValueType)) return error.Overflow;
        return .{ .value = @intCast(value) };
    }

    pub fn asIndex(self: SubAssemblyID) error{Overflow}!usize {
        if (@bitSizeOf(ValueType) > @bitSizeOf(usize) and valueExceedsUsize(self.value)) {
            return error.Overflow;
        }
        return @intCast(self.value);
    }

    pub fn toInt(self: SubAssemblyID) ValueType {
        return self.value;
    }

    pub fn empty(self: SubAssemblyID) bool {
        return self.value == empty_value;
    }

    pub fn eql(self: SubAssemblyID, other: SubAssemblyID) bool {
        return self.value == other.value;
    }

    pub fn lessThan(self: SubAssemblyID, other: SubAssemblyID) bool {
        return self.value < other.value;
    }

    fn valueExceedsUsize(value: ValueType) bool {
        if (@bitSizeOf(ValueType) <= @bitSizeOf(usize)) return false;
        return value >= std.math.maxInt(usize);
    }
};

test "subassembly identifiers preserve root sentinel and checked conversion" {
    try std.testing.expect((SubAssemblyID{}).empty());
    try std.testing.expect(!SubAssemblyID.init(0).empty());
    try std.testing.expectEqual(@as(usize, 42), try (try SubAssemblyID.fromU256(42)).asIndex());
    try std.testing.expectError(
        error.Overflow,
        SubAssemblyID.fromU256(@as(u256, std.math.maxInt(u64)) + 1),
    );
}
