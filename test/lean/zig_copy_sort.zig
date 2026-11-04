// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

const std = @import("std");

// Both slices must be live, equally sized and non-overlapping. The source is
// initialized; the destination is writable. Ownership stays with the caller.
export fn copy_sort_ids(source: [*]const u32, target: [*]u32, length: usize) void {
    @memcpy(target[0..length], source[0..length]);
    std.sort.insertion(u32, target[0..length], {}, std.sort.asc(u32));
}
