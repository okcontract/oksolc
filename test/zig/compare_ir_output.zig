// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");

pub fn main(init: std.process.Init) !void {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len != 3) return error.InvalidArguments;
    const expected = try std.Io.Dir.cwd().readFileAlloc(init.io, args[1], init.gpa, .limited(20 * 1024 * 1024));
    defer init.gpa.free(expected);
    const actual = try std.Io.Dir.cwd().readFileAlloc(init.io, args[2], init.gpa, .limited(20 * 1024 * 1024));
    defer init.gpa.free(actual);
    try @import("ir_comparison.zig").compare(init.gpa, expected, actual);
}
