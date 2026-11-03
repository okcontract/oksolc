// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
export fn bounded_slice(p: [*]const u8, length: usize, start: usize, end: usize) usize {
    @setRuntimeSafety(false);
    const original = p[0..length];
    return original[start..end].len;
}

export fn conditional_slice(p: [*]const u8, length: usize, end: usize, take: bool) usize {
    @setRuntimeSafety(false);
    if (take) {
        const original = p[0..length];
        return original[0..end].len;
    }
    return 0;
}

export fn array_slice(p: *const [16]u8, start: usize, end: usize) usize {
    @setRuntimeSafety(false);
    return p[start..end].len;
}

export fn constant_length(p: [*]const u8, length: usize) usize {
    @setRuntimeSafety(false);
    const original = p[0..length];
    return original[0..4].len;
}

export fn unbounded_constant_length(p: [*]const u8) usize {
    @setRuntimeSafety(false);
    return p[0..4].len;
}

export fn unused_slice(p: [*]const u8, length: usize, end: usize) usize {
    @setRuntimeSafety(false);
    const original = p[0..length];
    _ = original[0..end];
    return 1;
}

export fn sentinel_slice(p: *const [16:0]u8, end: usize) usize {
    @setRuntimeSafety(false);
    return p[0..end].len;
}

export fn c_pointer_slice(p: [*c]const u8, end: usize) usize {
    @setRuntimeSafety(false);
    return p[0..end].len;
}

export fn length_form(p: [*]const u8, start: usize, length: usize) usize {
    @setRuntimeSafety(false);
    return p[start..][0..length].len;
}
