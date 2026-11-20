// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");

pub const SolcVersion = enum(u8) {
    v0_8_36 = 36,
    v0_8_37 = 37,
    v0_8_38 = 38,
    v0_8_39 = 39,

    pub const default: SolcVersion = .v0_8_36;

    pub fn parse(text: []const u8) ?SolcVersion {
        for (std.enums.values(SolcVersion)) |version| {
            if (std.mem.eql(u8, text, version.number())) return version;
        }
        return null;
    }

    pub fn number(self: SolcVersion) []const u8 {
        return switch (self) {
            .v0_8_36 => "0.8.36",
            .v0_8_37 => "0.8.37",
            .v0_8_38 => "0.8.38",
            .v0_8_39 => "0.8.39",
        };
    }

    pub fn metadataVersion(self: SolcVersion) []const u8 {
        return switch (self) {
            .v0_8_36 => "0.8.36+commit.8a079791",
            .v0_8_37 => "0.8.37+commit.f401782d",
            .v0_8_38 => "0.8.38+commit.1835d247",
            .v0_8_39 => "0.8.39+commit.ce47f2c8",
        };
    }

    pub fn compactBytes(self: SolcVersion) [3]u8 {
        return .{ 0, 8, @backingInt(self) };
    }
};
