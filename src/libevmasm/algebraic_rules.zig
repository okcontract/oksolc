// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Production algebraic rewrite table shared by `RuleList` and exported to Lean.
//! Operands must be stable values; fact soundness belongs to the caller.
const Instruction = @import("instruction.zig").Instruction;
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;

pub const Guard = enum { left_zero, right_zero, left_one, right_one, left_max, right_max, equal };
pub const Replacement = enum { left, right, zero, one, max, not_right, neg_left, neg_right, iszero_left, iszero_right, bool_left, bool_right };
pub const Stage = enum { constants, equal };
pub const Rule = struct { instruction: Instruction, guard: Guard, replacement: Replacement };
pub const Facts = struct { left: ?u256 = null, right: ?u256 = null, equal: bool = false };
const max_word = ~@as(u256, 0);

// Order within each instruction/stage preserves RuleList's first-match policy.
pub const rules = [_]Rule{
    .{ .instruction = .ADD, .guard = .right_zero, .replacement = .left },
    .{ .instruction = .ADD, .guard = .left_zero, .replacement = .right },
    .{ .instruction = .SUB, .guard = .right_zero, .replacement = .left },
    .{ .instruction = .SUB, .guard = .left_max, .replacement = .not_right },
    .{ .instruction = .MUL, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .MUL, .guard = .left_zero, .replacement = .zero },
    .{ .instruction = .MUL, .guard = .right_one, .replacement = .left },
    .{ .instruction = .MUL, .guard = .left_one, .replacement = .right },
    .{ .instruction = .MUL, .guard = .right_max, .replacement = .neg_left },
    .{ .instruction = .MUL, .guard = .left_max, .replacement = .neg_right },
    .{ .instruction = .DIV, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .DIV, .guard = .left_zero, .replacement = .zero },
    .{ .instruction = .DIV, .guard = .right_one, .replacement = .left },
    .{ .instruction = .SDIV, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .SDIV, .guard = .left_zero, .replacement = .zero },
    .{ .instruction = .SDIV, .guard = .right_one, .replacement = .left },
    .{ .instruction = .AND, .guard = .right_max, .replacement = .left },
    .{ .instruction = .AND, .guard = .left_max, .replacement = .right },
    .{ .instruction = .AND, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .AND, .guard = .left_zero, .replacement = .zero },
    .{ .instruction = .OR, .guard = .right_zero, .replacement = .left },
    .{ .instruction = .OR, .guard = .left_zero, .replacement = .right },
    .{ .instruction = .OR, .guard = .right_max, .replacement = .max },
    .{ .instruction = .OR, .guard = .left_max, .replacement = .max },
    .{ .instruction = .XOR, .guard = .right_zero, .replacement = .left },
    .{ .instruction = .XOR, .guard = .left_zero, .replacement = .right },
    .{ .instruction = .MOD, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .MOD, .guard = .left_zero, .replacement = .zero },
    .{ .instruction = .EQ, .guard = .right_zero, .replacement = .iszero_left },
    .{ .instruction = .EQ, .guard = .left_zero, .replacement = .iszero_right },
    .{ .instruction = .SHL, .guard = .left_zero, .replacement = .right },
    .{ .instruction = .SHL, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .SHR, .guard = .left_zero, .replacement = .right },
    .{ .instruction = .SHR, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .GT, .guard = .right_zero, .replacement = .bool_left },
    .{ .instruction = .GT, .guard = .right_max, .replacement = .zero },
    .{ .instruction = .GT, .guard = .left_zero, .replacement = .zero },
    .{ .instruction = .LT, .guard = .left_zero, .replacement = .bool_right },
    .{ .instruction = .LT, .guard = .left_max, .replacement = .zero },
    .{ .instruction = .LT, .guard = .right_zero, .replacement = .zero },
    .{ .instruction = .AND, .guard = .equal, .replacement = .left },
    .{ .instruction = .OR, .guard = .equal, .replacement = .left },
    .{ .instruction = .XOR, .guard = .equal, .replacement = .zero },
    .{ .instruction = .SUB, .guard = .equal, .replacement = .zero },
    .{ .instruction = .LT, .guard = .equal, .replacement = .zero },
    .{ .instruction = .SLT, .guard = .equal, .replacement = .zero },
    .{ .instruction = .GT, .guard = .equal, .replacement = .zero },
    .{ .instruction = .SGT, .guard = .equal, .replacement = .zero },
    .{ .instruction = .MOD, .guard = .equal, .replacement = .zero },
    .{ .instruction = .EQ, .guard = .equal, .replacement = .one },
};

pub fn matches(guard: Guard, facts: Facts) bool {
    return switch (guard) {
        .left_zero => facts.left == 0,
        .right_zero => facts.right == 0,
        .left_one => facts.left == 1,
        .right_one => facts.right == 1,
        .left_max => facts.left == max_word,
        .right_max => facts.right == max_word,
        .equal => facts.equal,
    };
}

pub fn select(instruction: Instruction, stage: Stage, facts: Facts) ?Replacement {
    @setEvalBranchQuota(256 * (rules.len + 1) * 4);
    switch (@backingInt(instruction)) {
        inline else => |opcode| {
            inline for (rules) |rule| {
                if (comptime @backingInt(rule.instruction) == opcode) {
                    const rule_stage: Stage = if (rule.guard == .equal) .equal else .constants;
                    if (stage == rule_stage and matches(rule.guard, facts)) return rule.replacement;
                }
            }
        },
    }
    return null;
}

/// Reuse the owning graph's interner and its ordinary allocation/error policy.
/// Returning a capture preserves the original occurrence and its annotations.
pub fn apply(replacement: Replacement, classes: anytype, left: u32, right: u32, debug_data: DebugData) !u32 {
    return switch (replacement) {
        .left => left,
        .right => right,
        .zero => try classes.makeConstant(0, debug_data),
        .one => try classes.makeConstant(1, debug_data),
        .max => try classes.makeConstant(max_word, debug_data),
        .not_right => try classes.makeOperation(.NOT, &.{right}, debug_data),
        .neg_left, .neg_right => try classes.makeOperation(.SUB, &.{
            try classes.makeConstant(0, debug_data),
            if (replacement == .neg_left) left else right,
        }, debug_data),
        .iszero_left, .iszero_right => try classes.makeOperation(.ISZERO, &.{
            if (replacement == .iszero_left) left else right,
        }, debug_data),
        .bool_left, .bool_right => blk: {
            const first = try classes.makeOperation(.ISZERO, &.{
                if (replacement == .bool_left) left else right,
            }, debug_data);
            break :blk try classes.makeOperation(.ISZERO, &.{first}, debug_data);
        },
    };
}
