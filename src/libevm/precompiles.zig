// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Revision-specific native dispatch addresses. Account bytecode cannot
//! override these handlers. This is dispatch metadata, not an implementation
//! of their execution, gas, or input validation rules.

const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

const known_addresses = [_]u160{ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0x100 };

/// Null means this revision's native dispatch set has not been established.
/// Consumers must not interpret an unsupported revision as an empty set.
pub fn addresses(revision: EVMVersion) ?[]const u160 {
    const count: usize = switch (revision.version) {
        .Homestead, .TangerineWhistle, .SpuriousDragon => 4,
        .Byzantium, .Constantinople, .Petersburg => 8,
        .Istanbul, .Berlin, .London, .Paris, .Shanghai => 9,
        .Cancun => 10,
        .Prague => 17,
        .Osaka => 18,
        .Amsterdam, .Future => return null,
    };
    return known_addresses[0..count];
}

test "precompile dispatch addresses match the pinned executable specification" {
    const std = @import("std");
    const Fixture = struct {
        repository: []const u8,
        commit: []const u8,
        forks: []const struct { revision: []const u8, source: []const u8, addresses: []const u160 },
    };
    const fixture = try std.json.parseFromSlice(Fixture, std.testing.allocator, @embedFile("fixtures/precompile-addresses.json"), .{});
    defer fixture.deinit();
    try std.testing.expectEqual(@as(usize, 14), fixture.value.forks.len);
    for (fixture.value.forks, 0..) |fork, index| {
        const revision = EVMVersion.fromString(fork.revision).?;
        try std.testing.expectEqual(index, @as(usize, @intCast(@intFromEnum(revision.version))));
        const actual = addresses(revision).?;
        try std.testing.expectEqualSlices(u160, fork.addresses, actual);
        for (actual, 0..) |address, ordinal| {
            try std.testing.expect(address != 0);
            if (ordinal != 0) try std.testing.expect(actual[ordinal - 1] < address);
        }
    }
    try std.testing.expect(addresses(.init(.Amsterdam)) == null);
    try std.testing.expect(addresses(.init(.Future)) == null);
}
