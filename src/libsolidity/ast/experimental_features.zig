// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Experimental feature inventory from `ExperimentalFeatures.h`.

const std = @import("std");

pub const ExperimentalFeature = enum(c_int) {
    ABIEncoderV2,
    SMTChecker,
    Test,
    TestOnlyAnalysis,
    Solidity,
};

pub const experimental_features_without_warning = [_]ExperimentalFeature{
    .ABIEncoderV2,
    .SMTChecker,
    .TestOnlyAnalysis,
};

pub const FeatureName = struct {
    name: []const u8,
    feature: ExperimentalFeature,
};

/// Lexically ordered like the upstream `std::map`.
pub const experimental_feature_names = [_]FeatureName{
    .{ .name = "ABIEncoderV2", .feature = .ABIEncoderV2 },
    .{ .name = "SMTChecker", .feature = .SMTChecker },
    .{ .name = "__test", .feature = .Test },
    .{ .name = "__testOnlyAnalysis", .feature = .TestOnlyAnalysis },
    .{ .name = "solidity", .feature = .Solidity },
};

pub fn fromName(name: []const u8) ?ExperimentalFeature {
    for (experimental_feature_names) |entry|
        if (std.mem.eql(u8, entry.name, name)) return entry.feature;
    return null;
}

pub fn suppressesWarning(feature: ExperimentalFeature) bool {
    for (experimental_features_without_warning) |candidate|
        if (candidate == feature) return true;
    return false;
}

test "experimental feature lookup and warning policy match the header tables" {
    try std.testing.expectEqual(ExperimentalFeature.Test, fromName("__test").?);
    try std.testing.expect(fromName("unknown") == null);
    try std.testing.expect(suppressesWarning(.SMTChecker));
    try std.testing.expect(!suppressesWarning(.Solidity));
}
