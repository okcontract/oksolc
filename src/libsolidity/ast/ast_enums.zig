// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Closed frontend enums and function-call argument shape from `ASTEnums.h`.

const std = @import("std");

pub const VirtualLookup = enum(c_int) {
    Static,
    Virtual,
    Super,
};

pub const StateMutability = enum(c_int) {
    Pure,
    View,
    NonPayable,
    Payable,
};

pub fn stateMutabilityToString(value: StateMutability) []const u8 {
    return switch (value) {
        .Pure => "pure",
        .View => "view",
        .NonPayable => "nonpayable",
        .Payable => "payable",
    };
}

/// Ordered from restricted to unrestricted, matching the upstream enum.
pub const Visibility = enum(c_int) {
    Default,
    Private,
    Internal,
    Public,
    External,
};

pub const Arithmetic = enum(c_int) {
    Checked,
    Wrapping,
};

pub const ContractKind = enum(c_int) {
    Interface,
    Contract,
    Library,
};

/// The concrete Type graph is introduced by `Types.h`. Until then the
/// argument list stores the same borrowed identity through an opaque pointer.
pub const TypeRef = *const anyopaque;

/// Container buffers are owned; type identities and optional argument names
/// are borrowed from the compilation arena.
pub const FuncCallArguments = struct {
    types: std.ArrayList(TypeRef) = .empty,
    names: std.ArrayList([]const u8) = .empty,

    pub fn deinit(self: *FuncCallArguments, allocator: std.mem.Allocator) void {
        self.types.deinit(allocator);
        self.names.deinit(allocator);
        self.* = undefined;
    }

    pub fn numArguments(self: *const FuncCallArguments) usize {
        return self.types.items.len;
    }

    pub fn numNames(self: *const FuncCallArguments) usize {
        return self.names.items.len;
    }

    pub fn hasNamedArguments(self: *const FuncCallArguments) bool {
        return self.names.items.len != 0;
    }
};

test "frontend enums retain ABI order and spelling" {
    try std.testing.expectEqual(@as(c_int, 0), @intFromEnum(VirtualLookup.Static));
    try std.testing.expectEqual(@as(c_int, 2), @intFromEnum(VirtualLookup.Super));
    try std.testing.expectEqual(@as(c_int, 4), @intFromEnum(Visibility.External));
    try std.testing.expectEqualStrings("nonpayable", stateMutabilityToString(.NonPayable));
    try std.testing.expectEqual(@as(c_int, 2), @intFromEnum(ContractKind.Library));
}

test "function-call argument counts distinguish positional and named calls" {
    var value: FuncCallArguments = .{};
    defer value.deinit(std.testing.allocator);
    var marker: u8 = 0;
    try value.types.append(std.testing.allocator, &marker);
    try std.testing.expectEqual(@as(usize, 1), value.numArguments());
    try std.testing.expect(!value.hasNamedArguments());
    try value.names.append(std.testing.allocator, "amount");
    try std.testing.expectEqual(@as(usize, 1), value.numNames());
    try std.testing.expect(value.hasNamedArguments());
}
