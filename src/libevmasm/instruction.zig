// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Complete EVM opcode and metadata table translated from `Instruction.cpp`.

const std = @import("std");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

/// Non-exhaustive because every byte decodes to an opcode value even when the
/// value has no instruction assigned to it.
pub const Instruction = enum(u8) {
    STOP = 0x00,
    ADD = 0x01,
    MUL = 0x02,
    SUB = 0x03,
    DIV = 0x04,
    SDIV = 0x05,
    MOD = 0x06,
    SMOD = 0x07,
    ADDMOD = 0x08,
    MULMOD = 0x09,
    EXP = 0x0a,
    SIGNEXTEND = 0x0b,

    LT = 0x10,
    GT = 0x11,
    SLT = 0x12,
    SGT = 0x13,
    EQ = 0x14,
    ISZERO = 0x15,
    AND = 0x16,
    OR = 0x17,
    XOR = 0x18,
    NOT = 0x19,
    BYTE = 0x1a,
    SHL = 0x1b,
    SHR = 0x1c,
    SAR = 0x1d,
    CLZ = 0x1e,

    KECCAK256 = 0x20,

    ADDRESS = 0x30,
    BALANCE = 0x31,
    ORIGIN = 0x32,
    CALLER = 0x33,
    CALLVALUE = 0x34,
    CALLDATALOAD = 0x35,
    CALLDATASIZE = 0x36,
    CALLDATACOPY = 0x37,
    CODESIZE = 0x38,
    CODECOPY = 0x39,
    GASPRICE = 0x3a,
    EXTCODESIZE = 0x3b,
    EXTCODECOPY = 0x3c,
    RETURNDATASIZE = 0x3d,
    RETURNDATACOPY = 0x3e,
    EXTCODEHASH = 0x3f,

    BLOCKHASH = 0x40,
    COINBASE = 0x41,
    TIMESTAMP = 0x42,
    NUMBER = 0x43,
    PREVRANDAO = 0x44,
    GASLIMIT = 0x45,
    CHAINID = 0x46,
    SELFBALANCE = 0x47,
    BASEFEE = 0x48,
    BLOBHASH = 0x49,
    BLOBBASEFEE = 0x4a,

    POP = 0x50,
    MLOAD = 0x51,
    MSTORE = 0x52,
    MSTORE8 = 0x53,
    SLOAD = 0x54,
    SSTORE = 0x55,
    JUMP = 0x56,
    JUMPI = 0x57,
    PC = 0x58,
    MSIZE = 0x59,
    GAS = 0x5a,
    JUMPDEST = 0x5b,
    TLOAD = 0x5c,
    TSTORE = 0x5d,
    MCOPY = 0x5e,

    PUSH0 = 0x5f,
    PUSH1 = 0x60,
    PUSH2 = 0x61,
    PUSH3 = 0x62,
    PUSH4 = 0x63,
    PUSH5 = 0x64,
    PUSH6 = 0x65,
    PUSH7 = 0x66,
    PUSH8 = 0x67,
    PUSH9 = 0x68,
    PUSH10 = 0x69,
    PUSH11 = 0x6a,
    PUSH12 = 0x6b,
    PUSH13 = 0x6c,
    PUSH14 = 0x6d,
    PUSH15 = 0x6e,
    PUSH16 = 0x6f,
    PUSH17 = 0x70,
    PUSH18 = 0x71,
    PUSH19 = 0x72,
    PUSH20 = 0x73,
    PUSH21 = 0x74,
    PUSH22 = 0x75,
    PUSH23 = 0x76,
    PUSH24 = 0x77,
    PUSH25 = 0x78,
    PUSH26 = 0x79,
    PUSH27 = 0x7a,
    PUSH28 = 0x7b,
    PUSH29 = 0x7c,
    PUSH30 = 0x7d,
    PUSH31 = 0x7e,
    PUSH32 = 0x7f,

    DUP1 = 0x80,
    DUP2 = 0x81,
    DUP3 = 0x82,
    DUP4 = 0x83,
    DUP5 = 0x84,
    DUP6 = 0x85,
    DUP7 = 0x86,
    DUP8 = 0x87,
    DUP9 = 0x88,
    DUP10 = 0x89,
    DUP11 = 0x8a,
    DUP12 = 0x8b,
    DUP13 = 0x8c,
    DUP14 = 0x8d,
    DUP15 = 0x8e,
    DUP16 = 0x8f,

    SWAP1 = 0x90,
    SWAP2 = 0x91,
    SWAP3 = 0x92,
    SWAP4 = 0x93,
    SWAP5 = 0x94,
    SWAP6 = 0x95,
    SWAP7 = 0x96,
    SWAP8 = 0x97,
    SWAP9 = 0x98,
    SWAP10 = 0x99,
    SWAP11 = 0x9a,
    SWAP12 = 0x9b,
    SWAP13 = 0x9c,
    SWAP14 = 0x9d,
    SWAP15 = 0x9e,
    SWAP16 = 0x9f,

    LOG0 = 0xa0,
    LOG1 = 0xa1,
    LOG2 = 0xa2,
    LOG3 = 0xa3,
    LOG4 = 0xa4,

    CREATE = 0xf0,
    CALL = 0xf1,
    CALLCODE = 0xf2,
    RETURN = 0xf3,
    DELEGATECALL = 0xf4,
    CREATE2 = 0xf5,
    STATICCALL = 0xfa,
    REVERT = 0xfd,
    INVALID = 0xfe,
    SELFDESTRUCT = 0xff,

    _,
};

pub const Tier = enum {
    Zero,
    Base,
    VeryLow,
    Low,
    Mid,
    High,
    BlockHash,
    WarmAccess,
    Special,
    Invalid,
};

pub const InstructionInfo = struct {
    name: []const u8,
    additional: u8,
    args: u8,
    ret: u8,
    side_effects: bool,
    gas_price_tier: Tier,
};

pub fn isCallInstruction(instruction: Instruction) bool {
    return switch (instruction) {
        .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL => true,
        else => false,
    };
}

pub fn isPushInstruction(instruction: Instruction) bool {
    const opcode = @intFromEnum(instruction);
    return opcode >= @intFromEnum(Instruction.PUSH0) and opcode <= @intFromEnum(Instruction.PUSH32);
}

pub fn isDupInstruction(instruction: Instruction) bool {
    const opcode = @intFromEnum(instruction);
    return opcode >= @intFromEnum(Instruction.DUP1) and opcode <= @intFromEnum(Instruction.DUP16);
}

pub fn isSwapInstruction(instruction: Instruction) bool {
    const opcode = @intFromEnum(instruction);
    return opcode >= @intFromEnum(Instruction.SWAP1) and opcode <= @intFromEnum(Instruction.SWAP16);
}

pub fn isLogInstruction(instruction: Instruction) bool {
    const opcode = @intFromEnum(instruction);
    return opcode >= @intFromEnum(Instruction.LOG0) and opcode <= @intFromEnum(Instruction.LOG4);
}

pub fn getPushNumber(instruction: Instruction) u8 {
    std.debug.assert(isPushInstruction(instruction));
    return @intFromEnum(instruction) - @intFromEnum(Instruction.PUSH0);
}

pub fn getDupNumber(instruction: Instruction) u8 {
    std.debug.assert(isDupInstruction(instruction));
    return @intFromEnum(instruction) - @intFromEnum(Instruction.DUP1) + 1;
}

pub fn getSwapNumber(instruction: Instruction) u8 {
    std.debug.assert(isSwapInstruction(instruction));
    return @intFromEnum(instruction) - @intFromEnum(Instruction.SWAP1) + 1;
}

pub fn getLogNumber(instruction: Instruction) u8 {
    std.debug.assert(isLogInstruction(instruction));
    return @intFromEnum(instruction) - @intFromEnum(Instruction.LOG0);
}

pub fn pushInstruction(number: u8) Instruction {
    std.debug.assert(number <= 32);
    return @enumFromInt(@intFromEnum(Instruction.PUSH0) + number);
}

pub fn dupInstruction(number: u8) Instruction {
    std.debug.assert(number >= 1 and number <= 16);
    return @enumFromInt(@intFromEnum(Instruction.DUP1) + number - 1);
}

pub fn swapInstruction(number: u8) Instruction {
    std.debug.assert(number >= 1 and number <= 16);
    return @enumFromInt(@intFromEnum(Instruction.SWAP1) + number - 1);
}

pub fn logInstruction(number: u8) Instruction {
    std.debug.assert(number <= 4);
    return @enumFromInt(@intFromEnum(Instruction.LOG0) + number);
}

pub fn instructionByName(name: []const u8) ?Instruction {
    if (std.mem.eql(u8, name, "DIFFICULTY")) return .PREVRANDAO;
    return std.meta.stringToEnum(Instruction, name);
}

pub fn instructionInfo(instruction: Instruction, evm_version: EVMVersion) InstructionInfo {
    if (isPushInstruction(instruction)) {
        const count = getPushNumber(instruction);
        return knownInfo(
            instruction,
            count,
            0,
            1,
            false,
            if (count == 0) .Base else .VeryLow,
        );
    }
    if (isDupInstruction(instruction)) {
        const count = getDupNumber(instruction);
        return knownInfo(instruction, 0, count, count + 1, false, .VeryLow);
    }
    if (isSwapInstruction(instruction)) {
        const count = getSwapNumber(instruction) + 1;
        return knownInfo(instruction, 0, count, count, false, .VeryLow);
    }
    if (isLogInstruction(instruction)) {
        return knownInfo(instruction, 0, getLogNumber(instruction) + 2, 0, true, .Special);
    }

    const result = switch (instruction) {
        .STOP => knownInfo(instruction, 0, 0, 0, true, .Zero),
        .ADD, .SUB => knownInfo(instruction, 0, 2, 1, false, .VeryLow),
        .MUL, .DIV, .SDIV, .MOD, .SMOD => knownInfo(instruction, 0, 2, 1, false, .Low),
        .EXP => knownInfo(instruction, 0, 2, 1, false, .Special),
        .NOT, .ISZERO => knownInfo(instruction, 0, 1, 1, false, .VeryLow),
        .LT, .GT, .SLT, .SGT, .EQ, .AND, .OR, .XOR, .BYTE, .SHL, .SHR, .SAR => knownInfo(instruction, 0, 2, 1, false, .VeryLow),
        .CLZ => knownInfo(instruction, 0, 1, 1, false, .Low),
        .ADDMOD, .MULMOD => knownInfo(instruction, 0, 3, 1, false, .Mid),
        .SIGNEXTEND => knownInfo(instruction, 0, 2, 1, false, .Low),
        .KECCAK256 => knownInfo(instruction, 0, 2, 1, true, .Special),
        .ADDRESS,
        .ORIGIN,
        .CALLER,
        .CALLVALUE,
        .CALLDATASIZE,
        .CODESIZE,
        .GASPRICE,
        .COINBASE,
        .TIMESTAMP,
        .NUMBER,
        .PREVRANDAO,
        .GASLIMIT,
        .CHAINID,
        .BASEFEE,
        .BLOBBASEFEE,
        .PC,
        .MSIZE,
        .GAS,
        => knownInfo(instruction, 0, 0, 1, false, .Base),
        .BALANCE, .EXTCODESIZE, .EXTCODEHASH => knownInfo(instruction, 0, 1, 1, false, .Special),
        .CALLDATALOAD => knownInfo(instruction, 0, 1, 1, false, .VeryLow),
        .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY, .MCOPY => knownInfo(instruction, 0, 3, 0, true, .VeryLow),
        .EXTCODECOPY => knownInfo(instruction, 0, 4, 0, true, .Special),
        .RETURNDATASIZE => knownInfo(instruction, 0, 0, 1, false, .Base),
        .BLOCKHASH => knownInfo(instruction, 0, 1, 1, false, .BlockHash),
        .BLOBHASH => knownInfo(instruction, 0, 1, 1, false, .VeryLow),
        .SELFBALANCE => knownInfo(instruction, 0, 0, 1, false, .Low),
        .POP => knownInfo(instruction, 0, 1, 0, false, .Base),
        .MLOAD => knownInfo(instruction, 0, 1, 1, true, .VeryLow),
        .MSTORE, .MSTORE8 => knownInfo(instruction, 0, 2, 0, true, .VeryLow),
        .SLOAD => knownInfo(instruction, 0, 1, 1, false, .Special),
        .SSTORE => knownInfo(instruction, 0, 2, 0, true, .Special),
        .TLOAD => knownInfo(instruction, 0, 1, 1, false, .WarmAccess),
        .TSTORE => knownInfo(instruction, 0, 2, 0, true, .WarmAccess),
        .JUMP => knownInfo(instruction, 0, 1, 0, true, .Mid),
        .JUMPI => knownInfo(instruction, 0, 2, 0, true, .High),
        .JUMPDEST => knownInfo(instruction, 0, 0, 0, true, .Special),
        .CREATE => knownInfo(instruction, 0, 3, 1, true, .Special),
        .CALL, .CALLCODE => knownInfo(instruction, 0, 7, 1, true, .Special),
        .RETURN => knownInfo(instruction, 0, 2, 0, true, .Zero),
        .DELEGATECALL, .STATICCALL => knownInfo(instruction, 0, 6, 1, true, .Special),
        .CREATE2 => knownInfo(instruction, 0, 4, 1, true, .Special),
        .REVERT => knownInfo(instruction, 0, 2, 0, true, .Zero),
        .INVALID => knownInfo(instruction, 0, 0, 0, true, .Zero),
        .SELFDESTRUCT => knownInfo(instruction, 0, 1, 0, true, .Special),
        else => invalidInfo(instruction),
    };
    if (instruction == .PREVRANDAO and !evm_version.atLeast(.Paris)) {
        var difficulty = result;
        difficulty.name = "DIFFICULTY";
        return difficulty;
    }
    return result;
}

pub fn isValidInstruction(instruction: Instruction) bool {
    return instructionInfo(instruction, EVMVersion.current()).gas_price_tier != .Invalid;
}

fn knownInfo(
    instruction: Instruction,
    additional: u8,
    args: u8,
    ret: u8,
    side_effects: bool,
    tier: Tier,
) InstructionInfo {
    return .{
        .name = @tagName(instruction),
        .additional = additional,
        .args = args,
        .ret = ret,
        .side_effects = side_effects,
        .gas_price_tier = tier,
    };
}

const invalid_names: [256][]const u8 = names: {
    @setEvalBranchQuota(100_000);
    var names: [256][]const u8 = undefined;
    for (0..256) |opcode| {
        names[opcode] = std.fmt.comptimePrint("<INVALID_INSTRUCTION: {d}>", .{opcode});
    }
    break :names names;
};

fn invalidInfo(instruction: Instruction) InstructionInfo {
    return .{
        .name = invalid_names[@intFromEnum(instruction)],
        .additional = 0,
        .args = 0,
        .ret = 0,
        .side_effects = false,
        .gas_price_tier = .Invalid,
    };
}

test "every declared opcode round-trips through its mnemonic" {
    inline for (std.meta.fields(Instruction)) |field| {
        const instruction: Instruction = @enumFromInt(field.value);
        try std.testing.expect(isValidInstruction(instruction));
        try std.testing.expectEqual(instruction, instructionByName(field.name).?);
        try std.testing.expectEqualStrings(field.name, instructionInfo(instruction, EVMVersion.current()).name);
    }
    try std.testing.expectEqual(Instruction.PREVRANDAO, instructionByName("DIFFICULTY").?);
    try std.testing.expect(instructionByName("difficulty") == null);
}

test "opcode family arithmetic and metadata match the EVM stack model" {
    try std.testing.expectEqual(Instruction.PUSH32, pushInstruction(32));
    try std.testing.expectEqual(@as(u8, 32), getPushNumber(.PUSH32));
    try std.testing.expectEqual(Instruction.DUP16, dupInstruction(16));
    try std.testing.expectEqual(Instruction.SWAP16, swapInstruction(16));
    try std.testing.expectEqual(Instruction.LOG4, logInstruction(4));
    try std.testing.expectEqual(@as(u8, 17), instructionInfo(.DUP16, EVMVersion.current()).ret);
    try std.testing.expectEqual(@as(u8, 17), instructionInfo(.SWAP16, EVMVersion.current()).args);
    try std.testing.expectEqual(@as(u8, 6), instructionInfo(.LOG4, EVMVersion.current()).args);
    try std.testing.expect(!isValidInstruction(@enumFromInt(0x0c)));
    try std.testing.expectEqualStrings(
        "<INVALID_INSTRUCTION: 12>",
        instructionInfo(@enumFromInt(0x0c), EVMVersion.current()).name,
    );
}

test "opcode 0x44 changes mnemonic at Paris only" {
    try std.testing.expectEqualStrings(
        "DIFFICULTY",
        instructionInfo(.PREVRANDAO, EVMVersion.init(.London)).name,
    );
    try std.testing.expectEqualStrings(
        "PREVRANDAO",
        instructionInfo(.PREVRANDAO, EVMVersion.init(.Paris)).name,
    );
}
