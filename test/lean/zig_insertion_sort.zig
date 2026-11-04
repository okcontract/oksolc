// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

const std = @import("std");

// The caller retains ownership and supplies an initialized, writable u32 slice.
// No pointer escapes this synchronous invocation, including at length zero.
export fn sort_ids(items: [*]u32, length: usize) void {
    std.sort.insertion(u32, items[0..length], {}, std.sort.asc(u32));
}

// Both indices must select distinct initialized elements in the caller's array.
// The native noalias precondition is never deliberately violated by this test.
export fn swap_ids(items: [*]u32, left: usize, right: usize) void {
    std.mem.swap(u32, &items[left], &items[right]);
}
