// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Compiler version constants.

const std = @import("std");

pub const VersionNumber = "0.8.36";
pub const VersionString = "0.8.36+zig";
/// Serialized only to preserve Solidity 0.8.36 metadata and bytecode hashes.
/// This is the reference compiler's identity, not oksolc's version string.
pub const MetadataVersion = "0.8.36+commit.8a079791";
pub const VersionCompactBytes = [3]u8{ 0, 8, 36 };
pub const VersionIsRelease = true;

test "compiler version constants distinguish oksolc from its compatibility target" {
    try std.testing.expectEqualStrings("0.8.36", VersionNumber);
    try std.testing.expectEqualStrings("0.8.36+zig", VersionString);
    try std.testing.expectEqualSlices(u8, &.{ 0, 8, 36 }, &VersionCompactBytes);
    try std.testing.expect(VersionIsRelease);
}
