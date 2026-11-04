// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
export fn move_back(p: [*]u32, count: usize) [*]u32 {
    @setRuntimeSafety(false);
    return p - count;
}

export fn load_store(p: *u32, value: u32) u32 {
    p.* = value;
    return p.*;
}

export fn slice_fields(p: *[]u8, length: usize) [*]u8 {
    p.len = length;
    return p.ptr;
}

export fn buffer_alias(p: [*]u32, index: usize, first: u32, second: u32) u32 {
    @setRuntimeSafety(false);
    const left: *u32 = @ptrCast(p);
    const right: *u32 = @ptrCast(p + index);
    left.* = first;
    right.* = second;
    return left.*;
}

export fn initialize_slice(p: *[]u8, pointer: [*]u8, length: usize) void {
    p.ptr = pointer;
    p.len = length;
}

export fn initialize_length(p: *[]u8, length: usize) usize {
    p.len = length;
    return p.len;
}

export fn unaligned_volatile(p: *align(1) volatile u32) u32 {
    return p.*;
}

export fn allow_zero(p: *allowzero u8) u8 {
    return p.*;
}

export fn packed_pointer(p: *align(1:3:1) u3) u8 {
    return p.*;
}

const Opaque = opaque {};
export fn opaque_pointer(p: *Opaque) *Opaque {
    return p;
}

export fn undefined_store(p: *u32) void {
    p.* = undefined;
}
