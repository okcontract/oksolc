// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deployment-size warnings, shared by serial and parallel artifact publication.

const std = @import("std");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const SolcVersion = @import("common").SolcVersion;

pub const Sizes = struct { creation: usize, deployed: usize };

pub fn report(
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    location: Diagnostics.SourceLocation,
    evm_version: EVMVersion,
    solc_version: SolcVersion,
    subject: []const u8,
    sizes: Sizes,
) !void {
    if (solc_version.atLeast(.v0_8_39) and evm_version.atLeast(.Amsterdam)) {
        try reportLimit(allocator, reporter, location, subject, "code", sizes.deployed, 65536, "Amsterdam", 5776);
        try reportLimit(allocator, reporter, location, subject, "initcode", sizes.creation, 131072, "Amsterdam", 7868);
        return;
    }
    if (evm_version.atLeast(.SpuriousDragon))
        try reportLimit(allocator, reporter, location, subject, "code", sizes.deployed, 24576, "Spurious Dragon", 5574);
    if (evm_version.atLeast(.Shanghai))
        try reportLimit(allocator, reporter, location, subject, "initcode", sizes.creation, 49152, "Shanghai", 3860);
}

fn reportLimit(
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    location: Diagnostics.SourceLocation,
    subject: []const u8,
    kind: []const u8,
    size: usize,
    limit: usize,
    fork: []const u8,
    diagnostic_id: u64,
) !void {
    if (size <= limit) return;
    const message = try allocator.print(
        "{s} {s} size is {d} bytes and exceeds {d} bytes (a limit introduced in {s}). " ++
            "This contract may not be deployable on Mainnet. Consider enabling the optimizer (with a low \"runs\" value!), " ++
            "turning off revert strings, or using libraries.",
        .{ subject, kind, size, limit, fork },
    );
    defer allocator.free(message);
    try reporter.warning(.{ .value = diagnostic_id }, location, message);
}

test "code size warnings respect exact limits and EVM activation boundaries" {
    const allocator = std.testing.allocator;
    const location: Diagnostics.SourceLocation = .{ .start = 0, .end = 10, .source_name = "C.sol" };
    for ([_]struct { version: EVMVersion, target: SolcVersion = .v0_8_36, sizes: Sizes, ids: []const u64 }{
        .{ .version = .init(.Homestead), .sizes = .{ .creation = 49153, .deployed = 24577 }, .ids = &.{} },
        .{ .version = .init(.SpuriousDragon), .sizes = .{ .creation = 49153, .deployed = 24577 }, .ids = &.{5574} },
        .{ .version = .init(.Paris), .sizes = .{ .creation = 49153, .deployed = 24576 }, .ids = &.{} },
        .{ .version = .init(.Shanghai), .sizes = .{ .creation = 49152, .deployed = 24576 }, .ids = &.{} },
        .{ .version = .init(.Shanghai), .sizes = .{ .creation = 49153, .deployed = 24576 }, .ids = &.{3860} },
        .{ .version = .init(.Shanghai), .sizes = .{ .creation = 49153, .deployed = 24577 }, .ids = &.{ 5574, 3860 } },
        .{ .version = .init(.Amsterdam), .target = .v0_8_39, .sizes = .{ .creation = 131072, .deployed = 65536 }, .ids = &.{} },
        .{ .version = .init(.Amsterdam), .target = .v0_8_39, .sizes = .{ .creation = 131073, .deployed = 65537 }, .ids = &.{ 5776, 7868 } },
    }) |case| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        try report(allocator, &reporter, location, case.version, case.target, "Contract", case.sizes);
        try std.testing.expectEqual(case.ids.len, reporter.diagnostics().len);
        for (reporter.diagnostics(), case.ids) |diagnostic, id| {
            try std.testing.expectEqual(id, diagnostic.error_id.value);
            try std.testing.expectEqual(.Warning, diagnostic.error_type);
            try std.testing.expect(diagnostic.location.?.eql(location));
        }
    }
}
