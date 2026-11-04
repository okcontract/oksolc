// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const builtin = @import("builtin");

export fn word_byte_order() u8 {
    return switch (builtin.cpu.arch.endian()) {
        .little => 0,
        .big => 1,
    };
}

export fn read_word_byte(pointer: *const u32, index: usize) u8 {
    const bytes: []align(@alignOf(u32)) const u8 = @ptrCast(pointer);
    return bytes[index];
}

export fn write_word_byte(pointer: *u32, index: usize, byte: u8) void {
    const bytes: []align(@alignOf(u32)) u8 = @ptrCast(pointer);
    bytes[index] = byte;
}
