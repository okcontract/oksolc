// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const W = std.hash.Wyhash;
const lengths = [_]usize{ 1, 5, 9, 13, 17, 21, 25, 29, 33, 37, 41, 45 };
const Case = struct {
    length: usize,
    total: usize,
    state: [3]u64,
    // Absent entries are never read from the native buffer.
    initialized: [48]?u16,
    native_hash: u64,
    repeated_hash: u64,
    changed_a_hash: u64,
    changed_b_hash: u64,
    source_retained: bool,
};
fn Capture(comptime count: usize) type {
    return struct {
        schema: []const u8 = "oksolc.wyhash-local.v1",
        endian: []const u8 = @tagName(builtin.cpu.arch.endian()),
        usize_bytes: usize = @sizeOf(usize),
        size: usize = @sizeOf(W),
        alignment: usize = @alignOf(W),
        offsets: [6]usize = .{ @offsetOf(W, "a"), @offsetOf(W, "b"), @offsetOf(W, "state"), @offsetOf(W, "total_len"), @offsetOf(W, "buf"), @offsetOf(W, "buf_len") },
        cases: [count]Case,
    };
}

fn observeCase(len: usize, index: usize) Case {
    const initial = [3]u64{ (@as(u64, 1) << 63) + index, 0x1122334455667788 + index, 0x99aabbccddeeff00 + index };
    const total = if (len < 41) len + 48 else len;
    var value: W = .{ .a = undefined, .b = undefined, .state = initial, .total_len = total, .buf = undefined, .buf_len = len };
    var observed: [48]?u16 = @splat(null);
    for (0..48) |i| {
        if (i < len or (len < 16 and i >= 48 - (16 - len))) {
            const byte: u8 = @truncate(i * 17 + index * 29 + 3);
            value.buf[i] = byte;
            observed[i] = byte;
        }
    }
    const first = value.final();
    const repeated = value.final();
    var alternate = value;
    alternate.a = 0;
    alternate.b = std.math.maxInt(u64);
    const changed_a = alternate.final();
    alternate.a = std.math.maxInt(u64);
    alternate.b = 0;
    const changed_b = alternate.final();
    var retained = std.mem.eql(u64, &value.state, &initial) and value.total_len == total and value.buf_len == len;
    for (observed, 0..) |entry, i| {
        if (entry) |byte| retained = retained and value.buf[i] == byte;
    }
    return .{ .length = len, .total = total, .state = initial, .initialized = observed, .native_hash = first, .repeated_hash = repeated, .changed_a_hash = changed_a, .changed_b_hash = changed_b, .source_retained = retained };
}

// The pinned compiler also evaluates the actual stdlib copy of undefined a/b
// at comptime, where using such a value in arithmetic would be rejected.
comptime {
    @setEvalBranchQuota(100000);
    const sample = observeCase(1, 0);
    if (!sample.source_retained or sample.native_hash != sample.repeated_hash or
        sample.native_hash != sample.changed_a_hash or sample.native_hash != sample.changed_b_hash)
        @compileError("partial-initialization finalization changed its observation");
}

pub fn observe() Capture(lengths.len) {
    var cases: [lengths.len]Case = undefined;
    for (lengths, 0..) |len, index| cases[index] = observeCase(len, index);
    return .{ .cases = cases };
}

pub fn observeFinal() Capture(49) {
    var cases: [49]Case = undefined;
    for (0..49) |len| cases[len] = observeCase(len, len);
    return .{ .schema = "oksolc.wyhash-final.v1", .cases = cases };
}
