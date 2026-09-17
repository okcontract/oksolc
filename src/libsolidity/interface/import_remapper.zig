// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Import-prefix selection translated from `ImportRemapper.cpp`.

const std = @import("std");
const CommonIO = @import("../../libsolutil/common_io.zig");

pub const Remapping = struct {
    context: []const u8,
    prefix: []const u8,
    target: []const u8,

    pub fn eql(self: Remapping, other: Remapping) bool {
        return std.mem.eql(u8, self.context, other.context) and
            std.mem.eql(u8, self.prefix, other.prefix) and
            std.mem.eql(u8, self.target, other.target);
    }
};

/// Owned source and canonical path components. The original spelling is
/// externally observable in Solidity metadata; the normalized spelling is
/// used for matching and semantic fingerprints.
pub const NormalizedRemapping = struct {
    original_context: []u8,
    original_prefix: []u8,
    original_target: []u8,
    context: []u8,
    prefix: []u8,
    target: []u8,

    pub fn initAlloc(
        allocator: std.mem.Allocator,
        remapping: Remapping,
    ) std.mem.Allocator.Error!NormalizedRemapping {
        const original_context = try allocator.dupe(u8, remapping.context);
        errdefer allocator.free(original_context);
        const original_prefix = try allocator.dupe(u8, remapping.prefix);
        errdefer allocator.free(original_prefix);
        const original_target = try allocator.dupe(u8, remapping.target);
        errdefer allocator.free(original_target);
        const context = try CommonIO.sanitizePathAlloc(allocator, remapping.context);
        errdefer allocator.free(context);
        const prefix = try CommonIO.sanitizePathAlloc(allocator, remapping.prefix);
        errdefer allocator.free(prefix);
        const target = try CommonIO.sanitizePathAlloc(allocator, remapping.target);
        return .{
            .original_context = original_context,
            .original_prefix = original_prefix,
            .original_target = original_target,
            .context = context,
            .prefix = prefix,
            .target = target,
        };
    }

    pub fn deinit(self: *NormalizedRemapping, allocator: std.mem.Allocator) void {
        allocator.free(self.target);
        allocator.free(self.prefix);
        allocator.free(self.context);
        allocator.free(self.original_target);
        allocator.free(self.original_prefix);
        allocator.free(self.original_context);
        self.* = undefined;
    }

    pub fn original(self: NormalizedRemapping) Remapping {
        return .{
            .context = self.original_context,
            .prefix = self.original_prefix,
            .target = self.original_target,
        };
    }

    pub fn eql(self: NormalizedRemapping, other: NormalizedRemapping) bool {
        return std.mem.eql(u8, self.context, other.context) and
            std.mem.eql(u8, self.prefix, other.prefix) and
            std.mem.eql(u8, self.target, other.target);
    }
};

pub const ImportRemapper = struct {
    allocator: std.mem.Allocator,
    remapping_items: std.ArrayList(NormalizedRemapping) = .empty,

    pub fn init(allocator: std.mem.Allocator) ImportRemapper {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *ImportRemapper) void {
        self.clear();
        self.remapping_items.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clear(self: *ImportRemapper) void {
        for (self.remapping_items.items) |*remapping|
            remapping.deinit(self.allocator);
        self.remapping_items.clearRetainingCapacity();
    }

    pub fn setRemappings(
        self: *ImportRemapper,
        new_remappings: []const Remapping,
    ) std.mem.Allocator.Error!void {
        var replacement: std.ArrayList(NormalizedRemapping) = .empty;
        errdefer {
            for (replacement.items) |*remapping|
                remapping.deinit(self.allocator);
            replacement.deinit(self.allocator);
        }
        try replacement.ensureTotalCapacity(self.allocator, new_remappings.len);
        for (new_remappings) |remapping| {
            std.debug.assert(remapping.prefix.len != 0);
            replacement.appendAssumeCapacity(try NormalizedRemapping.initAlloc(
                self.allocator,
                remapping,
            ));
        }
        self.clear();
        self.remapping_items.deinit(self.allocator);
        self.remapping_items = replacement;
    }

    pub fn remappings(self: *const ImportRemapper) []const NormalizedRemapping {
        return self.remapping_items.items;
    }

    pub fn applyAlloc(
        self: *const ImportRemapper,
        allocator: std.mem.Allocator,
        path: []const u8,
        context: []const u8,
    ) std.mem.Allocator.Error![]u8 {
        return applyNormalizedRemappingsAlloc(
            allocator,
            self.remapping_items.items,
            path,
            context,
        );
    }
};

pub fn applyNormalizedRemappingsAlloc(
    allocator: std.mem.Allocator,
    remappings: []const NormalizedRemapping,
    path: []const u8,
    current_context: []const u8,
) std.mem.Allocator.Error![]u8 {
    var longest_prefix: usize = 0;
    var longest_context: usize = 0;
    var best_match_target: []const u8 = "";

    for (remappings) |remapping| {
        if (remapping.context.len < longest_context) continue;
        if (!std.mem.startsWith(u8, current_context, remapping.context)) continue;
        if (remapping.prefix.len < longest_prefix and
            remapping.context.len == longest_context) continue;
        if (!std.mem.startsWith(u8, path, remapping.prefix)) continue;

        longest_context = remapping.context.len;
        longest_prefix = remapping.prefix.len;
        best_match_target = remapping.target;
    }

    return std.mem.concat(
        allocator,
        u8,
        &.{ best_match_target, path[longest_prefix..] },
    );
}

pub fn isRemapping(input: []const u8) bool {
    return std.mem.findScalar(u8, input, '=') != null;
}

/// Returns borrowed slices into `input`, matching the three textual fields of
/// `context:prefix=target` without allocating.
pub fn parseRemapping(input: []const u8) ?Remapping {
    const equals = std.mem.findScalar(u8, input, '=') orelse return null;
    const colon = std.mem.findScalar(u8, input[0..equals], ':');
    const prefix_start = if (colon) |index| index + 1 else 0;
    if (prefix_start == equals) return null;
    return .{
        .context = if (colon) |index| input[0..index] else "",
        .prefix = input[prefix_start..equals],
        .target = input[equals + 1 ..],
    };
}

test "remapping parsing and longest context-prefix selection match upstream" {
    const first = parseRemapping("contracts:pkg/=vendor/pkg/").?;
    try std.testing.expectEqualStrings("contracts", first.context);
    try std.testing.expectEqualStrings("pkg/", first.prefix);
    try std.testing.expectEqualStrings("vendor/pkg/", first.target);
    try std.testing.expect(parseRemapping("=:target") == null);
    try std.testing.expect(parseRemapping("plain-path") == null);

    const remappings = [_]Remapping{
        .{ .context = "", .prefix = "pkg/", .target = "global/" },
        .{ .context = "contracts/", .prefix = "pkg/", .target = "local/" },
        .{ .context = "contracts/", .prefix = "pkg/deep/", .target = "deep/" },
    };
    var remapper = ImportRemapper.init(std.testing.allocator);
    defer remapper.deinit();
    try remapper.setRemappings(&remappings);

    const local = try remapper.applyAlloc(
        std.testing.allocator,
        "pkg/deep/A.sol",
        "contracts/C.sol",
    );
    defer std.testing.allocator.free(local);
    try std.testing.expectEqualStrings("deep/A.sol", local);

    const global = try remapper.applyAlloc(
        std.testing.allocator,
        "pkg/A.sol",
        "other/C.sol",
    );
    defer std.testing.allocator.free(global);
    try std.testing.expectEqualStrings("global/A.sol", global);
}

test "applying normalized remappings allocates only the result" {
    var remapper = ImportRemapper.init(std.testing.allocator);
    defer remapper.deinit();
    try remapper.setRemappings(&.{
        .{ .context = "", .prefix = "pkg/", .target = "global/" },
        .{ .context = "contracts/", .prefix = "pkg/", .target = "local/" },
        .{ .context = "contracts/", .prefix = "pkg/deep/", .target = "deep/" },
    });

    var failing = std.testing.FailingAllocator.init(
        std.testing.allocator,
        .{ .fail_index = 1 },
    );
    const allocator = failing.allocator();
    const result = try remapper.applyAlloc(
        allocator,
        "pkg/deep/A.sol",
        "contracts/C.sol",
    );
    defer allocator.free(result);
    try std.testing.expectEqualStrings("deep/A.sol", result);
    try std.testing.expectEqual(@as(usize, 1), failing.alloc_index);
    try std.testing.expect(!failing.has_induced_failure);
}

fn exerciseNormalizationAllocationFailures(allocator: std.mem.Allocator) !void {
    var remapper = ImportRemapper.init(allocator);
    defer remapper.deinit();
    try remapper.setRemappings(&.{
        .{ .context = "contracts", .prefix = "pkg/", .target = "vendor/pkg/" },
        .{ .context = "", .prefix = "lib/", .target = "vendor/lib/" },
    });
    const resolved = try remapper.applyAlloc(
        allocator,
        "pkg/A.sol",
        "contracts/C.sol",
    );
    defer allocator.free(resolved);
}

test "normalized remappings own partial state across allocation failures" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        exerciseNormalizationAllocationFailures,
        .{},
    );
}
