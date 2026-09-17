// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Procedural form of the ordered expression rules from `RuleList.h`.
//!
//! The C++ implementation builds a recursive pattern graph with capturing
//! lambdas. Zig keeps the same rule order but evaluates it directly against
//! stable expression IDs. This avoids hidden closure ownership while retaining
//! the first-match semantics used by `ExpressionClasses`.

const std = @import("std");
const DebugData = @import("../liblangutil/debug_data.zig").DebugData;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const Instruction = @import("instruction.zig").Instruction;

pub const ExpressionId = u32;

const max_word = ~@as(u256, 0);

pub const SimplificationOptions = struct {
    /// Part 5 contains two three-argument replacements that are deliberately
    /// unavailable to the classic libevmasm expression optimizer.
    for_yul_optimizer: bool = false,
    /// The final EVM-specific rule group is present only when the caller has a
    /// concrete EVM dialect (as opposed to the context-independent assembler).
    evm_version: ?EVMVersion = null,
};

pub fn binaryLogarithm(value: u256) ?usize {
    if (value == 0 or (value & (value - 1)) != 0) return null;
    return @intCast(@ctz(value));
}

/// Applies the non-EVM-version-specific rules used by libevmasm. The context
/// supplies expression lookup and construction; replacements recursively pass
/// through the same interner, exactly like C++ `rebuildExpression()`.
pub fn simplify(
    classes: anytype,
    instruction: Instruction,
    arguments: []const ExpressionId,
    debug_data: DebugData,
) !?ExpressionId {
    return simplifyWithOptions(classes, instruction, arguments, debug_data, .{});
}

/// Applies the same ordered rule list with the Yul-only and revision-specific
/// tail enabled when requested. Keeping this as a separate entry point leaves
/// classic libevmasm behavior unchanged.
pub fn simplifyWithOptions(
    classes: anytype,
    instruction: Instruction,
    arguments: []const ExpressionId,
    debug_data: DebugData,
    options: SimplificationOptions,
) !?ExpressionId {
    // Part 1: arithmetic on constants.
    var constant_arguments: [3]u256 = undefined;
    var all_constant = arguments.len <= constant_arguments.len and arguments.len != 0;
    if (all_constant) {
        for (arguments, 0..) |id, index| {
            constant_arguments[index] = classes.knownConstantValue(id) orelse {
                all_constant = false;
                break;
            };
        }
    }
    if (all_constant) {
        if (foldConstants(instruction, constant_arguments[0..arguments.len])) |value|
            return try classes.makeConstant(value, debug_data);
    }

    if (arguments.len == 2) {
        const left = arguments[0];
        const right = arguments[1];
        const left_constant = classes.knownConstantValue(left);
        const right_constant = classes.knownConstantValue(right);

        // Part 2: invariants involving constants.
        switch (instruction) {
            .ADD => {
                if (right_constant == 0) return left;
                if (left_constant == 0) return right;
            },
            .SUB => {
                if (right_constant == 0) return left;
                if (left_constant == max_word)
                    return try classes.makeOperation(.NOT, &.{right}, debug_data);
            },
            .MUL => {
                if (right_constant == 0 or left_constant == 0)
                    return try classes.makeConstant(0, debug_data);
                if (right_constant == 1) return left;
                if (left_constant == 1) return right;
                if (right_constant == max_word)
                    return try classes.makeOperation(.SUB, &.{ try classes.makeConstant(0, debug_data), left }, debug_data);
                if (left_constant == max_word)
                    return try classes.makeOperation(.SUB, &.{ try classes.makeConstant(0, debug_data), right }, debug_data);
            },
            .DIV, .SDIV => {
                if (right_constant == 0 or left_constant == 0)
                    return try classes.makeConstant(0, debug_data);
                if (right_constant == 1) return left;
            },
            .AND => {
                if (right_constant == max_word) return left;
                if (left_constant == max_word) return right;
                if (right_constant == 0 or left_constant == 0)
                    return try classes.makeConstant(0, debug_data);

                if (right_constant == 0xff) {
                    if (classes.operationArguments(left, .BYTE)) |byte_args|
                        return try classes.makeOperation(.BYTE, byte_args, debug_data);
                }
            },
            .OR => {
                if (right_constant == 0) return left;
                if (left_constant == 0) return right;
                if (right_constant == max_word or left_constant == max_word)
                    return try classes.makeConstant(max_word, debug_data);
            },
            .XOR => {
                if (right_constant == 0) return left;
                if (left_constant == 0) return right;
            },
            .MOD => {
                if (right_constant == 0 or left_constant == 0)
                    return try classes.makeConstant(0, debug_data);
            },
            .EQ => {
                if (right_constant == 0)
                    return try classes.makeOperation(.ISZERO, &.{left}, debug_data);
                if (left_constant == 0)
                    return try classes.makeOperation(.ISZERO, &.{right}, debug_data);
            },
            .SHL, .SHR => {
                if (left_constant == 0) return right;
                if (right_constant == 0) return try classes.makeConstant(0, debug_data);
            },
            .GT => {
                if (right_constant == 0)
                    return try doubleIsZero(classes, left, debug_data);
                if (right_constant == max_word or left_constant == 0)
                    return try classes.makeConstant(0, debug_data);
            },
            .LT => {
                if (left_constant == 0)
                    return try doubleIsZero(classes, right, debug_data);
                if (left_constant == max_word or right_constant == 0)
                    return try classes.makeConstant(0, debug_data);
            },
            .BYTE => {
                if (left_constant == 31)
                    return try classes.makeOperation(
                        .AND,
                        &.{ right, try classes.makeConstant(0xff, debug_data) },
                        debug_data,
                    );
            },
            else => {},
        }

        // Part 3: operations involving the same expression.
        if (left == right) switch (instruction) {
            .AND, .OR => return left,
            .XOR, .SUB, .LT, .SLT, .GT, .SGT, .MOD => return try classes.makeConstant(0, debug_data),
            .EQ => return try classes.makeConstant(1, debug_data),
            else => {},
        };

        // Part 4: logical combinations.
        if (instruction == .XOR) {
            if (try cancelNestedBinary(classes, .XOR, left, right)) |id| return id;
            if (try cancelNestedBinary(classes, .XOR, right, left)) |id| return id;
        }
        if (instruction == .OR) {
            if (absorbs(classes, left, right, .AND)) return left;
            if (absorbs(classes, right, left, .AND)) return right;
            if (isNegation(classes, left, right) or isNegation(classes, right, left))
                return try classes.makeConstant(max_word, debug_data);
        }
        if (instruction == .AND) {
            if (absorbs(classes, left, right, .OR)) return left;
            if (absorbs(classes, right, left, .OR)) return right;
            if (isNegation(classes, left, right) or isNegation(classes, right, left))
                return try classes.makeConstant(0, debug_data);
        }

        // Part 4.5: idempotent nested AND/OR and SIGNEXTEND.
        if (instruction == .AND or instruction == .OR) {
            if (try dropRepeatedNested(classes, instruction, left, right, debug_data)) |id| return id;
            if (try dropRepeatedNested(classes, instruction, right, left, debug_data)) |id| return id;
        }
        if (instruction == .SIGNEXTEND) {
            if (classes.operationArguments(right, .SIGNEXTEND)) |inner| {
                if (inner.len == 2) {
                    if (left == inner[0])
                        return try classes.makeOperation(.SIGNEXTEND, inner, debug_data);
                    if (left_constant) |outer_byte| if (classes.knownConstantValue(inner[0])) |inner_byte|
                        return try classes.makeOperation(
                            .SIGNEXTEND,
                            &.{ try classes.makeConstant(@min(outer_byte, inner_byte), debug_data), inner[1] },
                            debug_data,
                        );
                }
            }
        }

        // Part 5: dynamic constant families.
        if (instruction == .MOD) {
            // The Yul optimizer can express the three-argument ADDMOD and
            // MULMOD results; libevmasm's stack-expression optimizer cannot.
            // These precede the generic power-of-two MOD rule upstream.
            if (options.for_yul_optimizer and right_constant != null and
                binaryLogarithm(right_constant.?) != null)
            {
                if (classes.operationArguments(left, .MUL)) |nested|
                    if (nested.len == 2)
                        return try classes.makeOperation(
                            .MULMOD,
                            &.{ nested[0], nested[1], right },
                            debug_data,
                        );
                if (classes.operationArguments(left, .ADD)) |nested|
                    if (nested.len == 2)
                        return try classes.makeOperation(
                            .ADDMOD,
                            &.{ nested[0], nested[1], right },
                            debug_data,
                        );
            }
            if (right_constant) |modulus| if (binaryLogarithm(modulus) != null)
                return try classes.makeOperation(
                    .AND,
                    &.{ left, try classes.makeConstant(modulus - 1, debug_data) },
                    debug_data,
                );
        }
        if ((instruction == .SHL or instruction == .SHR) and
            left_constant != null and left_constant.? >= 256)
            return try classes.makeConstant(0, debug_data);
        if (instruction == .BYTE and left_constant != null and left_constant.? >= 32)
            return try classes.makeConstant(0, debug_data);
        if (instruction == .SIGNEXTEND and left_constant != null and left_constant.? >= 31)
            return right;

        if (instruction == .AND) {
            if (try stripRedundantSignExtendMask(classes, left, right, debug_data)) |id| return id;
            if (try stripRedundantSignExtendMask(classes, right, left, debug_data)) |id| return id;
            if (addressInstruction(classes, left, right)) |address_instruction|
                return try classes.makeOperation(address_instruction, &.{}, debug_data);
            if (addressInstruction(classes, right, left)) |address_instruction|
                return try classes.makeOperation(address_instruction, &.{}, debug_data);
        }

        // Part 7: associative normalization and shift/mask combinations.
        if (isAssociative(instruction)) {
            if (try reassociate(classes, instruction, left, right, false, debug_data)) |id| return id;
            if (try reassociate(classes, instruction, right, left, true, debug_data)) |id| return id;
        }

        if (instruction == .SHL or instruction == .SHR) {
            if (left_constant) |outer_shift| {
                if (classes.operationArguments(right, instruction)) |inner| if (inner.len == 2)
                    if (classes.knownConstantValue(inner[0])) |inner_shift| {
                        if (outer_shift >= 256 -| @min(inner_shift, 256))
                            return try classes.makeConstant(0, debug_data);
                        return try classes.makeOperation(
                            instruction,
                            &.{ try classes.makeConstant(outer_shift + inner_shift, debug_data), inner[1] },
                            debug_data,
                        );
                    };

                const opposite: Instruction = if (instruction == .SHL) .SHR else .SHL;
                if (classes.operationArguments(right, opposite)) |inner| if (inner.len == 2)
                    if (classes.knownConstantValue(inner[0])) |inner_shift|
                        if (outer_shift < 256 and inner_shift < 256)
                            return try combineOppositeShifts(
                                classes,
                                instruction,
                                outer_shift,
                                inner_shift,
                                inner[1],
                                debug_data,
                            );

                if (classes.operationArguments(right, .AND)) |inner| if (inner.len == 2)
                    if (splitConstant(classes, inner)) |masked| {
                        if (outer_shift < 256) {
                            const shifted_mask = if (instruction == .SHL)
                                masked.value << @intCast(outer_shift)
                            else
                                masked.value >> @intCast(outer_shift);
                            const shifted = try classes.makeOperation(
                                instruction,
                                &.{ left, masked.expression },
                                debug_data,
                            );
                            return try classes.makeOperation(
                                .AND,
                                &.{ shifted, try classes.makeConstant(shifted_mask, debug_data) },
                                debug_data,
                            );
                        }
                    };
            }
        }

        if (instruction == .AND) {
            if (try distributeAlternatingMask(classes, left, right, debug_data)) |id| return id;

            if (try removeCoveredShiftMask(classes, left, right, debug_data)) |id| return id;
            if (try removeCoveredShiftMask(classes, right, left, debug_data)) |id| return id;

            if (classes.operationArguments(left, .SHL)) |lhs_shift|
                if (classes.operationArguments(right, .SHL)) |rhs_shift|
                    if (lhs_shift.len == 2 and rhs_shift.len == 2 and lhs_shift[0] == rhs_shift[0]) {
                        const combined = try classes.makeOperation(.AND, &.{ lhs_shift[1], rhs_shift[1] }, debug_data);
                        return try classes.makeOperation(.SHL, &.{ lhs_shift[0], combined }, debug_data);
                    };
        }

        if (instruction == .MUL) {
            if (try powerOfTwoShiftProduct(classes, left, right, debug_data)) |id| return id;
            if (try powerOfTwoShiftProduct(classes, right, left, debug_data)) |id| return id;
        }
        if (instruction == .DIV)
            if (classes.operationArguments(right, .SHL)) |shift|
                if (shift.len == 2 and classes.knownConstantValue(shift[1]) == 1)
                    return try classes.makeOperation(.SHR, &.{ shift[0], left }, debug_data);

        if (instruction == .BYTE and left_constant != null) {
            if (classes.operationArguments(right, .SHL)) |shift| if (shift.len == 2)
                if (classes.knownConstantValue(shift[0])) |amount|
                    if (amount % 8 == 0 and left_constant.? <= 32 and amount <= 256)
                        return try classes.makeOperation(
                            .BYTE,
                            &.{ try classes.makeConstant(left_constant.? + amount / 8, debug_data), shift[1] },
                            debug_data,
                        );
            if (classes.operationArguments(right, .SHR)) |shift| if (shift.len == 2)
                if (classes.knownConstantValue(shift[0])) |amount| {
                    if (left_constant.? < amount / 8)
                        return try classes.makeConstant(0, debug_data);
                    if (amount % 8 == 0 and left_constant.? < 32 and amount <= 256)
                        return try classes.makeOperation(
                            .BYTE,
                            &.{ try classes.makeConstant(left_constant.? - amount / 8, debug_data), shift[1] },
                            debug_data,
                        );
                };
        }

        if (instruction == .SHL and left_constant != null) {
            if (classes.operationArguments(right, .SIGNEXTEND)) |sign_extend| if (sign_extend.len == 2)
                if (classes.knownConstantValue(sign_extend[0])) |byte_index|
                    if ((left_constant.? & 7) == 0 and left_constant.? <= 256 and byte_index <= 32) {
                        const shifted = try classes.makeOperation(.SHL, &.{ left, sign_extend[1] }, debug_data);
                        return try classes.makeOperation(
                            .SIGNEXTEND,
                            &.{ try classes.makeConstant((left_constant.? >> 3) + byte_index, debug_data), shifted },
                            debug_data,
                        );
                    };
        }

        if (instruction == .SIGNEXTEND and left_constant != null) {
            if (classes.operationArguments(right, .SHR)) |shift| if (shift.len == 2)
                if (classes.knownConstantValue(shift[0])) |amount|
                    if (amount % 8 == 0 and amount <= 256 and left_constant.? <= 256 and
                        (256 - amount) / 8 == left_constant.? + 1)
                        return try classes.makeOperation(.SAR, &.{ shift[0], shift[1] }, debug_data);
        }

        // Part 8: move constants across subtraction.
        if (instruction == .SUB) {
            if (right_constant) |constant|
                return try classes.makeOperation(
                    .ADD,
                    &.{ left, try classes.makeConstant(0 -% constant, debug_data) },
                    debug_data,
                );

            if (classes.operationArguments(left, .ADD)) |nested| if (splitConstant(classes, nested)) |parts| {
                const difference = try classes.makeOperation(.SUB, &.{ parts.expression, right }, debug_data);
                return try classes.makeOperation(.ADD, &.{ difference, try classes.makeConstant(parts.value, debug_data) }, debug_data);
            };
            if (classes.operationArguments(right, .ADD)) |nested| if (splitConstant(classes, nested)) |parts| {
                const difference = try classes.makeOperation(.SUB, &.{ left, parts.expression }, debug_data);
                return try classes.makeOperation(
                    .ADD,
                    &.{ difference, try classes.makeConstant(0 -% parts.value, debug_data) },
                    debug_data,
                );
            };
            if (classes.operationArguments(left, .SUB)) |nested| if (nested.len == 2) {
                if (classes.knownConstantValue(nested[1])) |_| {
                    const difference = try classes.makeOperation(.SUB, &.{ nested[0], right }, debug_data);
                    return try classes.makeOperation(.SUB, &.{ difference, nested[1] }, debug_data);
                }
                if (classes.knownConstantValue(nested[0])) |_| {
                    const sum = try classes.makeOperation(.ADD, &.{ nested[1], right }, debug_data);
                    return try classes.makeOperation(.SUB, &.{ nested[0], sum }, debug_data);
                }
            };
            if (classes.operationArguments(right, .SUB)) |nested| if (nested.len == 2) {
                if (classes.knownConstantValue(nested[1])) |constant| {
                    const difference = try classes.makeOperation(.SUB, &.{ left, nested[0] }, debug_data);
                    return try classes.makeOperation(
                        .ADD,
                        &.{ difference, try classes.makeConstant(constant, debug_data) },
                        debug_data,
                    );
                }
                if (classes.knownConstantValue(nested[0])) |constant| {
                    const sum = try classes.makeOperation(.ADD, &.{ left, nested[1] }, debug_data);
                    return try classes.makeOperation(
                        .ADD,
                        &.{ sum, try classes.makeConstant(0 -% constant, debug_data) },
                        debug_data,
                    );
                }
            };
        }
    }

    // Unary rules from parts 4 and 6.
    if (arguments.len == 1) {
        const value = arguments[0];
        if (instruction == .NOT)
            if (classes.operationArguments(value, .NOT)) |inner|
                if (inner.len == 1) return inner[0];

        if (instruction == .ISZERO) {
            if (classes.operationArguments(value, .ISZERO)) |second| if (second.len == 1) {
                if (classes.operationArguments(second[0], .ISZERO)) |third|
                    if (third.len == 1)
                        return try classes.makeOperation(.ISZERO, &.{third[0]}, debug_data);
                if (classes.operationArguments(second[0], .EQ)) |inner|
                    return try classes.makeOperation(.EQ, inner, debug_data);
                if (classes.operationArguments(second[0], .LT)) |inner|
                    return try classes.makeOperation(.LT, inner, debug_data);
                if (classes.operationArguments(second[0], .SLT)) |inner|
                    return try classes.makeOperation(.SLT, inner, debug_data);
                if (classes.operationArguments(second[0], .GT)) |inner|
                    return try classes.makeOperation(.GT, inner, debug_data);
                if (classes.operationArguments(second[0], .SGT)) |inner|
                    return try classes.makeOperation(.SGT, inner, debug_data);
            };
            if (classes.operationArguments(value, .XOR)) |inner|
                return try classes.makeOperation(.EQ, inner, debug_data);
            if (classes.operationArguments(value, .SUB)) |inner|
                return try classes.makeOperation(.EQ, inner, debug_data);
        }
    }

    // `evmRuleList()` is appended after all context-independent rules.
    if (options.evm_version) |evm_version| {
        if (instruction == .BALANCE and arguments.len == 1 and evm_version.hasSelfBalance())
            if (classes.operationArguments(arguments[0], .ADDRESS)) |address_arguments|
                if (address_arguments.len == 0)
                    return try classes.makeOperation(.SELFBALANCE, &.{}, debug_data);

        if (instruction == .EXP and arguments.len == 2) {
            const base = classes.knownConstantValue(arguments[0]);
            if (base == 0)
                return try classes.makeOperation(.ISZERO, &.{arguments[1]}, debug_data);
            if (base == 1)
                return try classes.makeConstant(1, debug_data);
            if (base == 2 and evm_version.hasBitwiseShifting())
                return try classes.makeOperation(
                    .SHL,
                    &.{ arguments[1], try classes.makeConstant(1, debug_data) },
                    debug_data,
                );
            if (base == max_word) {
                const one = try classes.makeConstant(1, debug_data);
                const parity = try classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data);
                const even = try classes.makeOperation(.ISZERO, &.{parity}, debug_data);
                return try classes.makeOperation(.SUB, &.{ even, parity }, debug_data);
            }
        }

        if (evm_version.hasBitwiseShifting() and arguments.len == 2) switch (instruction) {
            .MUL => {
                if (classes.knownConstantValue(arguments[0])) |constant|
                    if (binaryLogarithm(constant)) |power|
                        return try classes.makeOperation(
                            .SHL,
                            &.{ try classes.makeConstant(power, debug_data), arguments[1] },
                            debug_data,
                        );
                if (classes.knownConstantValue(arguments[1])) |constant|
                    if (binaryLogarithm(constant)) |power|
                        return try classes.makeOperation(
                            .SHL,
                            &.{ try classes.makeConstant(power, debug_data), arguments[0] },
                            debug_data,
                        );
            },
            .DIV => if (classes.knownConstantValue(arguments[1])) |constant|
                if (binaryLogarithm(constant)) |power|
                    return try classes.makeOperation(
                        .SHR,
                        &.{ try classes.makeConstant(power, debug_data), arguments[0] },
                        debug_data,
                    ),
            else => {},
        };
    }

    return null;
}

const ConstantOperand = struct {
    expression: ExpressionId,
    value: u256,
};

fn splitConstant(classes: anytype, arguments: []const ExpressionId) ?ConstantOperand {
    if (arguments.len != 2) return null;
    if (classes.knownConstantValue(arguments[1])) |value|
        return .{ .expression = arguments[0], .value = value };
    if (classes.knownConstantValue(arguments[0])) |value|
        return .{ .expression = arguments[1], .value = value };
    return null;
}

fn doubleIsZero(classes: anytype, value: ExpressionId, debug_data: DebugData) !ExpressionId {
    const inner = try classes.makeOperation(.ISZERO, &.{value}, debug_data);
    return classes.makeOperation(.ISZERO, &.{inner}, debug_data);
}

fn cancelNestedBinary(
    classes: anytype,
    instruction: Instruction,
    single: ExpressionId,
    nested_id: ExpressionId,
) !?ExpressionId {
    const nested = classes.operationArguments(nested_id, instruction) orelse return null;
    if (nested.len != 2) return null;
    if (nested[0] == single) return nested[1];
    if (nested[1] == single) return nested[0];
    return null;
}

fn absorbs(classes: anytype, single: ExpressionId, nested_id: ExpressionId, nested_instruction: Instruction) bool {
    const nested = classes.operationArguments(nested_id, nested_instruction) orelse return false;
    return nested.len == 2 and (nested[0] == single or nested[1] == single);
}

fn isNegation(classes: anytype, value: ExpressionId, possible_not: ExpressionId) bool {
    const arguments = classes.operationArguments(possible_not, .NOT) orelse return false;
    return arguments.len == 1 and arguments[0] == value;
}

fn dropRepeatedNested(
    classes: anytype,
    instruction: Instruction,
    nested_id: ExpressionId,
    repeated: ExpressionId,
    debug_data: DebugData,
) !?ExpressionId {
    const nested = classes.operationArguments(nested_id, instruction) orelse return null;
    if (nested.len != 2) return null;
    return if (nested[0] == repeated or nested[1] == repeated)
        try classes.makeOperation(instruction, nested, debug_data)
    else
        null;
}

fn stripRedundantSignExtendMask(
    classes: anytype,
    constant_id: ExpressionId,
    sign_extend_id: ExpressionId,
    debug_data: DebugData,
) !?ExpressionId {
    const mask = classes.knownConstantValue(constant_id) orelse return null;
    const sign_extend = classes.operationArguments(sign_extend_id, .SIGNEXTEND) orelse return null;
    if (sign_extend.len != 2) return null;
    const byte_index = classes.knownConstantValue(sign_extend[0]) orelse return null;
    if (byte_index >= 31) return null;
    const bit_count: u8 = @intCast((byte_index + 1) * 8);
    const low_mask = (@as(u256, 1) << bit_count) - 1;
    if ((mask & low_mask) != mask) return null;
    // C++ Pattern stores the resolved expression for a Constant match group,
    // so an SSA alias is materialized as the literal in the replacement.
    const materialized_mask = try classes.materializeConstant(constant_id, mask, debug_data);
    return try classes.makeOperation(.AND, &.{ materialized_mask, sign_extend[1] }, debug_data);
}

fn addressInstruction(classes: anytype, operation_id: ExpressionId, mask_id: ExpressionId) ?Instruction {
    if (classes.knownConstantValue(mask_id) != ((@as(u256, 1) << 160) - 1)) return null;
    inline for ([_]Instruction{ .ADDRESS, .CALLER, .ORIGIN, .COINBASE }) |instruction| {
        if (classes.operationArguments(operation_id, instruction)) |arguments|
            if (arguments.len == 0) return instruction;
    }
    return null;
}

fn isAssociative(instruction: Instruction) bool {
    return switch (instruction) {
        .ADD, .MUL, .AND, .OR, .XOR => true,
        else => false,
    };
}

fn combineConstants(instruction: Instruction, left: u256, right: u256) u256 {
    return switch (instruction) {
        .ADD => left +% right,
        .MUL => left *% right,
        .AND => left & right,
        .OR => left | right,
        .XOR => left ^ right,
        else => unreachable,
    };
}

fn reassociate(
    classes: anytype,
    instruction: Instruction,
    nested_id: ExpressionId,
    other: ExpressionId,
    nested_is_right: bool,
    debug_data: DebugData,
) !?ExpressionId {
    const nested = classes.operationArguments(nested_id, instruction) orelse return null;
    const parts = splitConstant(classes, nested) orelse return null;
    if (classes.knownConstantValue(other)) |other_constant|
        return try classes.makeOperation(
            instruction,
            &.{
                parts.expression,
                try classes.makeConstant(combineConstants(instruction, parts.value, other_constant), debug_data),
            },
            debug_data,
        );
    // Preserve the ordered C++ rules: (X + A) + Y becomes (X + Y) + A,
    // while Y + (X + A) becomes (Y + X) + A. This distinction is observable
    // in optimized Yul and, consequently, in bytecode operand order.
    const inner = if (nested_is_right)
        try classes.makeOperation(instruction, &.{ other, parts.expression }, debug_data)
    else
        try classes.makeOperation(instruction, &.{ parts.expression, other }, debug_data);
    return try classes.makeOperation(
        instruction,
        &.{ inner, try classes.makeConstant(parts.value, debug_data) },
        debug_data,
    );
}

fn combineOppositeShifts(
    classes: anytype,
    outer_instruction: Instruction,
    outer_shift: u256,
    inner_shift: u256,
    value: ExpressionId,
    debug_data: DebugData,
) !ExpressionId {
    const mask = if (outer_instruction == .SHR)
        (max_word << @intCast(inner_shift)) >> @intCast(outer_shift)
    else
        (max_word >> @intCast(inner_shift)) << @intCast(outer_shift);
    const shifted = if (inner_shift > outer_shift)
        try classes.makeOperation(
            if (outer_instruction == .SHR) .SHL else .SHR,
            &.{ try classes.makeConstant(inner_shift - outer_shift, debug_data), value },
            debug_data,
        )
    else if (outer_shift > inner_shift)
        try classes.makeOperation(
            outer_instruction,
            &.{ try classes.makeConstant(outer_shift - inner_shift, debug_data), value },
            debug_data,
        )
    else
        value;
    return classes.makeOperation(
        .AND,
        &.{ shifted, try classes.makeConstant(mask, debug_data) },
        debug_data,
    );
}

fn distributeAlternatingMask(
    classes: anytype,
    outer_left: ExpressionId,
    outer_right: ExpressionId,
    debug_data: DebugData,
) !?ExpressionId {
    const outer_arguments = [2]ExpressionId{ outer_left, outer_right };

    // Preserve the exact nested-loop order in RuleList.h. Both alternatives
    // can themselves be ANDs with constants, so collapsing the commutative
    // variants into splitConstant() changes which alternative is captured as
    // X. That operand order remains observable after stack allocation.
    for ([_]bool{ false, true }) |constant_first| {
        for (0..2) |inner_index| {
            for (0..2) |second_index| {
                const second_id = outer_arguments[second_index];
                const outer_mask_id = outer_arguments[1 - second_index];
                const outer_mask = classes.knownConstantValue(outer_mask_id) orelse continue;
                const alternatives = classes.operationArguments(second_id, .OR) orelse continue;
                if (alternatives.len != 2) continue;
                const inner = classes.operationArguments(alternatives[inner_index], .AND) orelse continue;
                if (inner.len != 2) continue;
                const constant_index: usize = @intFromBool(constant_first == false);
                const expression_index = 1 - constant_index;
                const inner_mask = classes.knownConstantValue(inner[constant_index]) orelse continue;

                const left = try classes.makeOperation(
                    .AND,
                    &.{ inner[expression_index], try classes.makeConstant(inner_mask & outer_mask, debug_data) },
                    debug_data,
                );
                // A Constant pattern captures the resolved literal rather
                // than the SSA identifier through which it was discovered.
                const materialized_outer_mask = try classes.materializeConstant(
                    outer_mask_id,
                    outer_mask,
                    debug_data,
                );
                const right = try classes.makeOperation(
                    .AND,
                    &.{ alternatives[1 - inner_index], materialized_outer_mask },
                    debug_data,
                );
                return try classes.makeOperation(.OR, &.{ left, right }, debug_data);
            }
        }
    }
    return null;
}

fn removeCoveredShiftMask(
    classes: anytype,
    mask_id: ExpressionId,
    shifted_id: ExpressionId,
    debug_data: DebugData,
) !?ExpressionId {
    const mask = classes.knownConstantValue(mask_id) orelse return null;
    const shifted = classes.operationArguments(shifted_id, .SHR) orelse return null;
    if (shifted.len != 2) return null;
    const amount = classes.knownConstantValue(shifted[0]) orelse return null;
    if (amount > 256) return null;
    const coverage = if (amount == 256) @as(u256, 0) else max_word >> @intCast(amount);
    return if ((mask & coverage) == coverage)
        try classes.makeOperation(.SHR, shifted, debug_data)
    else
        null;
}

fn powerOfTwoShiftProduct(
    classes: anytype,
    value: ExpressionId,
    shift_id: ExpressionId,
    debug_data: DebugData,
) !?ExpressionId {
    const shift = classes.operationArguments(shift_id, .SHL) orelse return null;
    if (shift.len != 2 or classes.knownConstantValue(shift[1]) != 1) return null;
    return try classes.makeOperation(.SHL, &.{ shift[0], value }, debug_data);
}

fn foldConstants(instruction: Instruction, arguments: []const u256) ?u256 {
    return switch (instruction) {
        .ADD => if (arguments.len == 2) arguments[0] +% arguments[1] else null,
        .MUL => if (arguments.len == 2) arguments[0] *% arguments[1] else null,
        .SUB => if (arguments.len == 2) arguments[0] -% arguments[1] else null,
        .DIV => if (arguments.len == 2) if (arguments[1] == 0) 0 else arguments[0] / arguments[1] else null,
        .SDIV => if (arguments.len == 2) signedDivision(arguments[0], arguments[1]) else null,
        .MOD => if (arguments.len == 2) if (arguments[1] == 0) 0 else arguments[0] % arguments[1] else null,
        .SMOD => if (arguments.len == 2) signedModulo(arguments[0], arguments[1]) else null,
        .EXP => if (arguments.len == 2) wrappingPower(arguments[0], arguments[1]) else null,
        .NOT => if (arguments.len == 1) ~arguments[0] else null,
        .LT => if (arguments.len == 2) @intFromBool(arguments[0] < arguments[1]) else null,
        .GT => if (arguments.len == 2) @intFromBool(arguments[0] > arguments[1]) else null,
        .SLT => if (arguments.len == 2) @intFromBool(asSigned(arguments[0]) < asSigned(arguments[1])) else null,
        .SGT => if (arguments.len == 2) @intFromBool(asSigned(arguments[0]) > asSigned(arguments[1])) else null,
        .EQ => if (arguments.len == 2) @intFromBool(arguments[0] == arguments[1]) else null,
        .ISZERO => if (arguments.len == 1) @intFromBool(arguments[0] == 0) else null,
        .AND => if (arguments.len == 2) arguments[0] & arguments[1] else null,
        .OR => if (arguments.len == 2) arguments[0] | arguments[1] else null,
        .XOR => if (arguments.len == 2) arguments[0] ^ arguments[1] else null,
        .BYTE => if (arguments.len == 2) byteValue(arguments[0], arguments[1]) else null,
        .ADDMOD => if (arguments.len == 3) addMod(arguments[0], arguments[1], arguments[2]) else null,
        .MULMOD => if (arguments.len == 3) mulMod(arguments[0], arguments[1], arguments[2]) else null,
        .SIGNEXTEND => if (arguments.len == 2) signExtend(arguments[0], arguments[1]) else null,
        .SHL => if (arguments.len == 2) shiftLeft(arguments[0], arguments[1]) else null,
        .SHR => if (arguments.len == 2) shiftRight(arguments[0], arguments[1]) else null,
        else => null,
    };
}

fn asSigned(value: u256) i256 {
    return @bitCast(value);
}

fn signedDivision(left: u256, right: u256) u256 {
    if (right == 0) return 0;
    const lhs = asSigned(left);
    const rhs = asSigned(right);
    if (lhs == std.math.minInt(i256) and rhs == -1) return left;
    return @bitCast(@divTrunc(lhs, rhs));
}

fn signedModulo(left: u256, right: u256) u256 {
    if (right == 0) return 0;
    const lhs = asSigned(left);
    const rhs = asSigned(right);
    if (rhs == 1 or rhs == -1) return 0;
    return @bitCast(@rem(lhs, rhs));
}

fn wrappingPower(base_value: u256, exponent_value: u256) u256 {
    var base = base_value;
    var exponent = exponent_value;
    var result: u256 = 1;
    while (exponent != 0) : (exponent >>= 1) {
        if ((exponent & 1) != 0) result *%= base;
        base *%= base;
    }
    return result;
}

fn byteValue(index: u256, value: u256) u256 {
    if (index >= 32) return 0;
    const shift: u8 = @intCast(8 * (31 - index));
    return (value >> shift) & 0xff;
}

fn addMod(left: u256, right: u256, modulus: u256) u256 {
    if (modulus == 0) return 0;
    return @intCast((@as(u257, left) + @as(u257, right)) % @as(u257, modulus));
}

fn mulMod(left: u256, right: u256, modulus: u256) u256 {
    if (modulus == 0) return 0;
    return @intCast((@as(u512, left) * @as(u512, right)) % @as(u512, modulus));
}

fn signExtend(byte_index: u256, value: u256) u256 {
    if (byte_index >= 31) return value;
    const test_bit: u8 = @intCast(byte_index * 8 + 7);
    const mask = (@as(u256, 1) << test_bit) - 1;
    return if ((value & (@as(u256, 1) << test_bit)) != 0) value | ~mask else value & mask;
}

fn shiftLeft(amount: u256, value: u256) u256 {
    return if (amount >= 256) 0 else value << @intCast(amount);
}

fn shiftRight(amount: u256, value: u256) u256 {
    return if (amount >= 256) 0 else value >> @intCast(amount);
}

test "constant EVM arithmetic uses 256-bit wrapping and signed semantics" {
    try std.testing.expectEqual(@as(u256, 0), foldConstants(.ADD, &.{ max_word, 1 }).?);
    try std.testing.expectEqual(max_word, foldConstants(.SDIV, &.{ max_word, 1 }).?);
    try std.testing.expectEqual(max_word, foldConstants(.SMOD, &.{ max_word, 2 }).?);
    try std.testing.expectEqual(@as(u256, 0), foldConstants(.SHL, &.{ 256, max_word }).?);
    try std.testing.expectEqual(@as(u256, 5), foldConstants(.ADDMOD, &.{ max_word, 8, 9 }).?);
}
