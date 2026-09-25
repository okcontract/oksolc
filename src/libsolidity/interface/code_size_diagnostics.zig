// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deployment-size warnings, shared by serial and parallel artifact publication.

const std = @import("std");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;

pub const Sizes = struct { creation: usize, deployed: usize };

pub fn report(
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    location: Diagnostics.SourceLocation,
    evm_version: EVMVersion,
    sizes: Sizes,
) !void {
    if (evm_version.atLeast(.SpuriousDragon) and sizes.deployed > 0x6000) {
        const message = try std.fmt.allocPrint(
            allocator,
            "Contract code size is {d} bytes and exceeds 24576 bytes (a limit introduced in Spurious Dragon). " ++
                "This contract may not be deployable on Mainnet. Consider enabling the optimizer (with a low \"runs\" value!), " ++
                "turning off revert strings, or using libraries.",
            .{sizes.deployed},
        );
        defer allocator.free(message);
        try reporter.warning(.{ .value = 5574 }, location, message);
    }
    if (evm_version.atLeast(.Shanghai) and sizes.creation > 0xc000) {
        const message = try std.fmt.allocPrint(
            allocator,
            "Contract initcode size is {d} bytes and exceeds 49152 bytes (a limit introduced in Shanghai). " ++
                "This contract may not be deployable on Mainnet. Consider enabling the optimizer (with a low \"runs\" value!), " ++
                "turning off revert strings, or using libraries.",
            .{sizes.creation},
        );
        defer allocator.free(message);
        try reporter.warning(.{ .value = 3860 }, location, message);
    }
}

test "code size warnings respect exact limits and EVM activation boundaries" {
    const allocator = std.testing.allocator;
    const location: Diagnostics.SourceLocation = .{ .start = 0, .end = 10, .source_name = "C.sol" };
    for ([_]struct { version: EVMVersion, sizes: Sizes, ids: []const u64 }{
        .{ .version = .init(.Homestead), .sizes = .{ .creation = 49153, .deployed = 24577 }, .ids = &.{} },
        .{ .version = .init(.SpuriousDragon), .sizes = .{ .creation = 49153, .deployed = 24577 }, .ids = &.{5574} },
        .{ .version = .init(.Paris), .sizes = .{ .creation = 49153, .deployed = 24576 }, .ids = &.{} },
        .{ .version = .init(.Shanghai), .sizes = .{ .creation = 49152, .deployed = 24576 }, .ids = &.{} },
        .{ .version = .init(.Shanghai), .sizes = .{ .creation = 49153, .deployed = 24576 }, .ids = &.{3860} },
        .{ .version = .init(.Shanghai), .sizes = .{ .creation = 49153, .deployed = 24577 }, .ids = &.{ 5574, 3860 } },
    }) |case| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        try report(allocator, &reporter, location, case.version, case.sizes);
        try std.testing.expectEqual(case.ids.len, reporter.diagnostics().len);
        for (reporter.diagnostics(), case.ids) |diagnostic, id| {
            try std.testing.expectEqual(id, diagnostic.error_id.value);
            try std.testing.expectEqual(.Warning, diagnostic.error_type);
            try std.testing.expect(diagnostic.location.?.eql(location));
        }
    }
}
