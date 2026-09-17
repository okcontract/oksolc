// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit rule descriptor corresponding to `SimplificationRule.h`.

pub fn SimplificationRule(comptime Pattern: type) type {
    return struct {
        pattern: Pattern,
        action: *const fn (*const Pattern) anyerror!Pattern,
        feasible: ?*const fn (*const Pattern) bool = null,

        pub fn isFeasible(self: *const @This()) bool {
            return if (self.feasible) |check| check(&self.pattern) else true;
        }
    };
}

/// Opcode constructors in C++ are template helpers. Zig rule consumers use
/// typed `Instruction` values directly, so the equivalent has no runtime data.
pub fn EVMBuiltins(comptime Pattern: type) type {
    return struct {
        pub fn operation(instruction: anytype, arguments: []const Pattern) Pattern {
            return Pattern.initOperation(instruction, arguments);
        }
    };
}
