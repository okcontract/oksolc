// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Stable handle for a dialect-owned builtin function.

pub const BuiltinHandle = struct {
    id: usize,

    pub fn eql(self: BuiltinHandle, other: BuiltinHandle) bool {
        return self.id == other.id;
    }

    pub fn lessThan(self: BuiltinHandle, other: BuiltinHandle) bool {
        return self.id < other.id;
    }
};

test "builtin handles compare by dialect-local id" {
    const first: BuiltinHandle = .{ .id = 1 };
    const second: BuiltinHandle = .{ .id = 2 };
    @import("std").testing.expect(first.lessThan(second)) catch unreachable;
    @import("std").testing.expect(!first.eql(second)) catch unreachable;
}
