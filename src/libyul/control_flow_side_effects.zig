// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reachability effects of Yul functions and builtin instructions.

const std = @import("std");
const Instruction = @import("../libevmasm/instruction.zig").Instruction;
const SemanticInformation = @import("../libevmasm/semantic_information.zig");

pub const ControlFlowSideEffects = struct {
    can_terminate: bool = false,
    can_revert: bool = false,
    can_continue: bool = true,

    pub fn terminatesOrReverts(self: ControlFlowSideEffects) bool {
        return (self.can_terminate or self.can_revert) and !self.can_continue;
    }

    pub fn fromInstruction(instruction: Instruction) ControlFlowSideEffects {
        if (!SemanticInformation.terminatesControlFlow(instruction)) return .{};
        if (SemanticInformation.reverts(instruction))
            return .{ .can_revert = true, .can_continue = false };
        return .{ .can_terminate = true, .can_continue = false };
    }

    pub fn worst() ControlFlowSideEffects {
        return .{ .can_terminate = true, .can_revert = true, .can_continue = true };
    }
};

test "instruction control-flow effects distinguish stop, revert, and add" {
    try std.testing.expect(ControlFlowSideEffects.fromInstruction(.STOP).can_terminate);
    try std.testing.expect(ControlFlowSideEffects.fromInstruction(.REVERT).can_revert);
    try std.testing.expect(ControlFlowSideEffects.fromInstruction(.ADD).can_continue);
}
