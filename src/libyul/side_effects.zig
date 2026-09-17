// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Data and state side-effect lattice used by Yul analysis and optimization.

const std = @import("std");

pub const Effect = enum(c_int) {
    none,
    read,
    write,

    pub fn combine(self: Effect, other: Effect) Effect {
        return @enumFromInt(@max(@intFromEnum(self), @intFromEnum(other)));
    }
};

pub const SideEffects = struct {
    movable: bool = true,
    movable_apart_from_effects: bool = true,
    can_be_removed: bool = true,
    can_be_removed_if_no_msize: bool = true,
    cannot_loop: bool = true,
    other_state: Effect = .none,
    storage: Effect = .none,
    memory: Effect = .none,
    transient_storage: Effect = .none,

    pub fn worst() SideEffects {
        return .{
            .movable = false,
            .movable_apart_from_effects = false,
            .can_be_removed = false,
            .can_be_removed_if_no_msize = false,
            .cannot_loop = false,
            .other_state = .write,
            .storage = .write,
            .memory = .write,
            .transient_storage = .write,
        };
    }

    pub fn combine(self: SideEffects, other: SideEffects) SideEffects {
        return .{
            .movable = self.movable and other.movable,
            .movable_apart_from_effects = self.movable_apart_from_effects and
                other.movable_apart_from_effects,
            .can_be_removed = self.can_be_removed and other.can_be_removed,
            .can_be_removed_if_no_msize = self.can_be_removed_if_no_msize and
                other.can_be_removed_if_no_msize,
            .cannot_loop = self.cannot_loop and other.cannot_loop,
            .other_state = self.other_state.combine(other.other_state),
            .storage = self.storage.combine(other.storage),
            .memory = self.memory.combine(other.memory),
            .transient_storage = self.transient_storage.combine(other.transient_storage),
        };
    }

    pub fn combineAssign(self: *SideEffects, other: SideEffects) void {
        self.* = self.combine(other);
    }

    pub fn eql(self: SideEffects, other: SideEffects) bool {
        return std.meta.eql(self, other);
    }
};

test "side effects form the upstream worst-case lattice" {
    const read_memory: SideEffects = .{ .memory = .read };
    const write_storage: SideEffects = .{
        .movable = false,
        .can_be_removed = false,
        .storage = .write,
    };
    const combined = read_memory.combine(write_storage);
    try std.testing.expectEqual(Effect.read, combined.memory);
    try std.testing.expectEqual(Effect.write, combined.storage);
    try std.testing.expect(!combined.movable);
    try std.testing.expect(SideEffects.worst().eql(SideEffects.worst()));
}
