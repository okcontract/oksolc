// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
export fn add_wrapping(x: u32, y: u32) u32 {
    return x +% y;
}

export fn add_constant(x: u32) u32 {
    return x +% 7;
}

export fn undefined_value() u32 {
    return undefined;
}

export fn source_slice_bound(p: [*]const u8, length: usize, end: usize) usize {
    @setRuntimeSafety(false);
    const original = p[0..length];
    const sub = original[0..end];
    return sub.len;
}

export fn source_parallel_lengths(a: [*]const u8, an: usize, b: [*]const u8, bn: usize) usize {
    @setRuntimeSafety(false);
    var sum: usize = 0;
    for (a[0..an], b[0..bn]) |x, y| {
        sum +%= @as(usize, x) +% @as(usize, y);
    }
    return sum;
}
