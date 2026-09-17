// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! ANSI formatting constants and scoped writer helper from `AnsiColorized.h`.

const std = @import("std");

pub const formatting = struct {
    pub const reset = "\x1b[0m";
    pub const inverse = "\x1b[7m";
    pub const bold = "\x1b[1m";
    pub const bright = bold;
    pub const black = "\x1b[30m";
    pub const red = "\x1b[31m";
    pub const green = "\x1b[32m";
    pub const yellow = "\x1b[33m";
    pub const blue = "\x1b[34m";
    pub const magenta = "\x1b[35m";
    pub const cyan = "\x1b[36m";
    pub const white = "\x1b[37m";
    pub const black_background = "\x1b[40m";
    pub const red_background = "\x1b[41m";
    pub const green_background = "\x1b[42m";
    pub const yellow_background = "\x1b[43m";
    pub const blue_background = "\x1b[44m";
    pub const magenta_background = "\x1b[45m";
    pub const cyan_background = "\x1b[46m";
    pub const white_background = "\x1b[47m";
    pub const gray_background = "\x1b[100m";
    pub const red_background_256 = "\x1b[48;5;160m";
    pub const orange_background_256 = "\x1b[48;5;166m";
};

pub fn writeColorized(
    writer: *std.Io.Writer,
    enabled: bool,
    codes: []const []const u8,
    text: []const u8,
) std.Io.Writer.Error!void {
    if (enabled) for (codes) |code| try writer.writeAll(code);
    try writer.writeAll(text);
    if (enabled) try writer.writeAll(formatting.reset);
}

test "colorized output resets formatting exactly once" {
    var output: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer output.deinit();
    try writeColorized(&output.writer, true, &.{ formatting.bold, formatting.red }, "error");
    try std.testing.expectEqualStrings("\x1b[1m\x1b[31merror\x1b[0m", output.written());
}
