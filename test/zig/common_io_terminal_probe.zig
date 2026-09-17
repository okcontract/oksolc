// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");
const CommonIO = @import("common_io");

pub fn main(init: std.process.Init) !void {
    var args = try init.minimal.args.iterateAllocator(init.gpa);
    defer args.deinit();
    _ = args.next();
    if (args.next()) |_| {
        var vtable = init.io.vtable.*;
        vtable.fileReadPositional = cancelRead;
        const io: std.Io = .{ .userdata = init.io.userdata, .vtable = &vtable };
        try std.testing.expectError(error.Canceled, CommonIO.readStandardInputChar(io));
        return;
    }
    if (try CommonIO.readStandardInputChar(init.io)) |byte|
        try std.Io.File.stdout().writeStreamingAll(init.io, &.{byte});
}

fn cancelRead(_: ?*anyopaque, file: std.Io.File, _: []const []u8, _: u64) std.Io.File.ReadPositionalError!usize {
    if (comptime @import("builtin").os.tag != .windows) {
        const mode = std.posix.tcgetattr(file.handle) catch return error.InputOutput;
        if (mode.lflag.ICANON or mode.lflag.ECHO) return error.InputOutput;
    }
    return error.Canceled;
}
