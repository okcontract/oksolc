// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Debug and revert-string settings translated from `DebugSettings.h`.

const std = @import("std");

pub const RevertStrings = enum(c_int) {
    Default,
    Strip,
    Debug,
    VerboseDebug,

    pub fn toString(self: RevertStrings) []const u8 {
        return switch (self) {
            .Default => "default",
            .Strip => "strip",
            .Debug => "debug",
            .VerboseDebug => "verboseDebug",
        };
    }

    pub fn fromString(input: []const u8) ?RevertStrings {
        inline for (std.meta.fields(RevertStrings)) |field| {
            const value: RevertStrings = @enumFromInt(field.value);
            if (std.mem.eql(u8, input, value.toString())) return value;
        }
        return null;
    }
};

test "revert-string settings retain ABI order and exact spellings" {
    try std.testing.expectEqual(@as(c_int, 0), @intFromEnum(RevertStrings.Default));
    try std.testing.expectEqual(@as(c_int, 3), @intFromEnum(RevertStrings.VerboseDebug));
    try std.testing.expectEqualStrings("verboseDebug", RevertStrings.VerboseDebug.toString());
    try std.testing.expectEqual(RevertStrings.Strip, RevertStrings.fromString("strip").?);
    try std.testing.expect(RevertStrings.fromString("verbose-debug") == null);
}
