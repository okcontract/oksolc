// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");

export fn swap_words(noalias a: *u32, noalias b: *u32) void {
    std.mem.swap(u32, a, b);
}

export fn swap_halves(noalias a: *u16, noalias b: *u16) void {
    std.mem.swap(u16, a, b);
}

fn biased(comptime T: type, x: T, comptime bias: T) T {
    return x +% bias;
}

export fn biased_word(x: u32) u32 {
    return biased(u32, x, 7);
}

fn fallible(x: u32) error{Bad}!u32 {
    if (x == 0) return error.Bad;
    return x;
}

// This call must retain its unsupported coercion, not join to fallible's body.
export fn widened_result(x: u32) u32 {
    const widened: fn (u32) anyerror!u32 = fallible;
    return widened(x) catch 0;
}
