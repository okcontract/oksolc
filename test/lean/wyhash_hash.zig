// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const W = std.hash.Wyhash;
const lengths = [_][5]usize{
    .{ 4, 1, 32, 0, 4 },     .{ 4, 1, 32, 4, 4 },   .{ 4, 1, 32, 8, 4 }, .{ 4, 1, 32, 12, 4 },
    .{ 4, 1, 32, 60, 4 },    .{ 0, 0, 0, 48, 0 },   .{ 48, 1, 0, 0, 0 }, .{ 47, 2, 0, 0, 0 },
    .{ 1, 47, 1, 0, 0 },     .{ 0, 0, 0, 49, 0 },   .{ 0, 0, 0, 96, 0 }, .{ 0, 0, 0, 97, 0 },
    .{ 16, 16, 16, 16, 16 }, .{ 49, 15, 1, 47, 2 },
};
const Step = struct { length: usize, total: usize, state: [3]u64, initialized: [48]?u16 };
const Case = struct {
    lengths: [5]usize,
    steps: [6]Step,
    native_hash: u64,
    repeated_hash: u64,
    changed_a_hash: u64,
    changed_b_hash: u64,
    source_retained: bool,
};
const Capture = struct {
    schema: []const u8 = "oksolc.wyhash-hash.v1",
    endian: []const u8 = @tagName(builtin.cpu.arch.endian()),
    usize_bytes: usize = @sizeOf(usize),
    size: usize = @sizeOf(W),
    alignment: usize = @alignOf(W),
    offsets: [6]usize = .{ @offsetOf(W, "a"), @offsetOf(W, "b"), @offsetOf(W, "state"), @offsetOf(W, "total_len"), @offsetOf(W, "buf"), @offsetOf(W, "buf_len") },
    cases: [lengths.len]Case,
};

fn snapshot(value: *const W) Step {
    var bytes: [48]?u16 = @splat(null);
    // Never observe undefined a/b or an unused buffer gap.
    for (0..48) |i| {
        if (i < value.buf_len or (value.total_len > 16 and value.buf_len < 16 and i >= 48 - (16 - value.buf_len)))
            bytes[i] = value.buf[i];
    }
    return .{ .length = value.buf_len, .total = value.total_len, .state = value.state, .initialized = bytes };
}

fn observeCase(sizes: [5]usize, index: usize) Case {
    var value = W.init(0);
    var steps: [6]Step = undefined;
    steps[0] = snapshot(&value);
    var position: usize = 0;
    for (sizes, 0..) |size, step| {
        var input: [97]u8 = undefined;
        for (input[0..size], 0..) |*byte, i| byte.* = @truncate((position + i) * 17 + index * 29 + 3);
        value.update(input[0..size]);
        position += size;
        steps[step + 1] = snapshot(&value);
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
    return .{ .lengths = sizes, .steps = steps, .native_hash = first, .repeated_hash = repeated, .changed_a_hash = changed_a, .changed_b_hash = changed_b, .source_retained = std.meta.eql(snapshot(&value), steps[5]) };
}

comptime {
    @setEvalBranchQuota(100000);
    const sample = observeCase(lengths[11], 11);
    if (!sample.source_retained or sample.native_hash != sample.repeated_hash or
        sample.native_hash != sample.changed_a_hash or sample.native_hash != sample.changed_b_hash)
        @compileError("incremental Wyhash changed its observation");
}

pub fn observe() Capture {
    var cases: [lengths.len]Case = undefined;
    for (lengths, 0..) |sizes, index| cases[index] = observeCase(sizes, index);
    return .{ .cases = cases };
}
