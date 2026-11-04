// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
//! Exercise the actual production helper through a full-width C ABI wrapper.
const numeric = @import("numeric");

fn word(a: u64, b: u64, c: u64, d: u64) u256 {
    return @as(u256, a) | (@as(u256, b) << 64) | (@as(u256, c) << 128) | (@as(u256, d) << 192);
}

export fn power256(output: [*]u64, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64) void {
    const result = numeric.exp256(word(a, b, c, d), word(e, f, g, h));
    output[0] = @truncate(result);
    output[1] = @truncate(result >> 64);
    output[2] = @truncate(result >> 128);
    output[3] = @truncate(result >> 192);
}
