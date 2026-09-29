// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Independent oksolc release and Solidity compatibility identities.

const std = @import("std");
const build_options = @import("build_options");

/// Product version, sourced from build.zig.zon.
pub const OksolcVersion = build_options.oksolc_version;
/// Content-derived compiler identity, also used to isolate persistent caches.
pub const BuildIdentity: ?[]const u8 = if (build_options.compiler_build_identity_available)
    build_options.compiler_build_identity
else
    null;
/// Solidity version used for pragma matching and tool feature detection.
pub const VersionNumber = "0.8.36";
pub const VersionString = VersionNumber ++ "+oksolc." ++ OksolcVersion;
/// Serialized only to preserve Solidity 0.8.36 metadata and bytecode hashes.
/// This is the reference compiler's identity, not oksolc's version string.
pub const MetadataVersion = "0.8.36+commit.8a079791";
pub const VersionCompactBytes = [3]u8{ 0, 8, 36 };
/// Describes the Solidity target, including when oksolc itself is a prerelease.
pub const VersionIsRelease = true;

test "compiler version constants distinguish oksolc from its compatibility target" {
    const product = try std.SemanticVersion.parse(OksolcVersion);
    // Build provenance belongs in BuildIdentity, keeping the composite valid SemVer.
    try std.testing.expect(product.build == null);
    const compatibility = try std.SemanticVersion.parse(VersionString);
    try std.testing.expect(compatibility.pre == null);
    try std.testing.expectEqualStrings("oksolc." ++ OksolcVersion, compatibility.build.?);
    try std.testing.expectEqualStrings("0.8.36", VersionNumber);
    try std.testing.expectEqual(std.math.Order.eq, compatibility.order(try std.SemanticVersion.parse(VersionNumber)));
    try std.testing.expectEqualStrings("0.8.36+commit.8a079791", MetadataVersion);
    try std.testing.expectEqualSlices(u8, &.{ 0, 8, 36 }, &VersionCompactBytes);
    try std.testing.expect(VersionIsRelease);
}
