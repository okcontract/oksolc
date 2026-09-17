// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Zig slices already provide the range behavior for `Views.h`; these helpers
//! retain the checked and unchecked pointer-dereference contracts.

const std = @import("std");

pub fn dereference(pointer: anytype) @TypeOf(pointer.*) {
    return pointer.*;
}

pub fn dereferenceChecked(pointer: anytype) @TypeOf(pointer.?.*) {
    std.debug.assert(pointer != null);
    return pointer.?.*;
}

test "checked pointer view dereferences values" {
    var value: u32 = 42;
    const pointer: ?*u32 = &value;
    try std.testing.expectEqual(@as(u32, 42), dereferenceChecked(pointer));
}
