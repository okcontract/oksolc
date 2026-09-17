// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Context-independent assembly semantics from `SemanticInformation.cpp`.

const std = @import("std");
const AssemblyItemModule = @import("assembly_item.zig");
const InstructionModule = @import("instruction.zig");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

pub const Effect = enum(c_int) {
    None,
    Read,
    Write,
};

pub const Location = enum(c_int) {
    Storage,
    Memory,
    TransientStorage,
};

pub const Operation = struct {
    location: Location,
    effect: Effect,
    start_parameter: ?usize = null,
    length_parameter: ?usize = null,
    length_constant: ?usize = null,
};

pub const Operations = struct {
    storage: [6]Operation = undefined,
    len: u8 = 0,

    pub fn slice(self: *const Operations) []const Operation {
        return self.storage[0..self.len];
    }

    fn append(self: *Operations, operation: Operation) void {
        std.debug.assert(self.len < self.storage.len);
        self.storage[self.len] = operation;
        self.len += 1;
    }
};

pub const SemanticError = error{
    AssemblyException,
    OptimizerException,
    InvalidItemType,
};

pub fn readWriteOperations(instruction: InstructionModule.Instruction) SemanticError!Operations {
    var result: Operations = .{};
    switch (instruction) {
        .SSTORE, .SLOAD => result.append(.{
            .effect = storage(instruction),
            .location = .Storage,
            .start_parameter = 0,
            .length_constant = 1,
        }),
        .MSTORE, .MSTORE8, .MLOAD => result.append(.{
            .effect = memory(instruction),
            .location = .Memory,
            .start_parameter = 0,
            .length_constant = if (instruction == .MSTORE or instruction == .MLOAD) 32 else 1,
        }),
        .TSTORE, .TLOAD => result.append(.{
            .effect = transientStorage(instruction),
            .location = .TransientStorage,
            .start_parameter = 0,
            .length_constant = 1,
        }),
        .REVERT, .RETURN, .KECCAK256, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4 => result.append(.{
            .effect = .Read,
            .location = .Memory,
            .start_parameter = 0,
            .length_parameter = 1,
        }),
        .EXTCODECOPY => result.append(.{
            .effect = .Write,
            .location = .Memory,
            .start_parameter = 1,
            .length_parameter = 3,
        }),
        .CODECOPY, .CALLDATACOPY, .RETURNDATACOPY => result.append(.{
            .effect = .Write,
            .location = .Memory,
            .start_parameter = 0,
            .length_parameter = 2,
        }),
        .MCOPY => {
            result.append(.{
                .effect = .Read,
                .location = .Memory,
                .start_parameter = 1,
                .length_parameter = 2,
            });
            result.append(.{
                .effect = .Write,
                .location = .Memory,
                .start_parameter = 0,
                .length_parameter = 2,
            });
        },
        .STATICCALL, .CALL, .CALLCODE, .DELEGATECALL => {
            const parameter_count: usize = InstructionModule.instructionInfo(
                instruction,
                EVMVersion.current(),
            ).args;
            result.append(.{
                .location = .Memory,
                .effect = .Read,
                .start_parameter = parameter_count - 4,
                .length_parameter = parameter_count - 3,
            });
            result.append(.{ .location = .Storage, .effect = .Read });
            result.append(.{ .location = .TransientStorage, .effect = .Read });
            if (instruction != .STATICCALL) {
                result.append(.{ .location = .Storage, .effect = .Write });
                result.append(.{ .location = .TransientStorage, .effect = .Write });
            }
            result.append(.{
                .location = .Memory,
                .effect = .Write,
                .start_parameter = parameter_count - 2,
            });
        },
        .CREATE, .CREATE2 => {
            result.append(.{
                .location = .Memory,
                .effect = .Read,
                .start_parameter = 1,
                .length_parameter = 2,
            });
            result.append(.{ .location = .Storage, .effect = .Read });
            result.append(.{ .location = .Storage, .effect = .Write });
            result.append(.{ .location = .TransientStorage, .effect = .Read });
            result.append(.{ .location = .TransientStorage, .effect = .Write });
        },
        .MSIZE => {},
        else => if (storage(instruction) != .None or
            memory(instruction) != .None or
            transientStorage(instruction) != .None)
        {
            return error.AssemblyException;
        },
    }
    return result;
}

pub fn breaksCSEAnalysisBlock(item: *const AssemblyItemModule.AssemblyItem, msize_important: bool) bool {
    return switch (item.item_type) {
        .UndefinedItem, .Tag, .PushDeployTimeAddress, .AssignImmutable, .VerbatimBytecode => true,
        .Push,
        .PushTag,
        .PushSub,
        .PushSubSize,
        .PushProgramSize,
        .PushData,
        .PushLibraryAddress,
        .PushImmutable,
        => false,
        .Operation => blk: {
            if (isSwapItem(item) or isDupItem(item)) break :blk false;
            const opcode = item.instruction_value.?;
            if (opcode == .GAS or opcode == .PC or opcode == .MSIZE) break :blk true;
            if (opcode == .SSTORE or opcode == .MSTORE) break :blk false;
            if (!msize_important and (opcode == .MLOAD or opcode == .KECCAK256)) break :blk false;
            const info = InstructionModule.instructionInfo(opcode, EVMVersion.current());
            break :blk info.side_effects or info.args > 2;
        },
    };
}

pub fn isCommutativeOperation(item: *const AssemblyItemModule.AssemblyItem) bool {
    if (item.item_type != .Operation) return false;
    return switch (item.instruction_value.?) {
        .ADD, .MUL, .EQ, .AND, .OR, .XOR => true,
        else => false,
    };
}

pub fn isDupItem(item: *const AssemblyItemModule.AssemblyItem) bool {
    return item.item_type == .Operation and InstructionModule.isDupInstruction(item.instruction_value.?);
}

pub fn isSwapItem(item: *const AssemblyItemModule.AssemblyItem) bool {
    return item.item_type == .Operation and InstructionModule.isSwapInstruction(item.instruction_value.?);
}

pub fn altersControlFlow(item: *const AssemblyItemModule.AssemblyItem) bool {
    if (!item.hasInstruction()) return false;
    return switch (item.instruction_value.?) {
        .JUMP, .JUMPI, .RETURN, .SELFDESTRUCT, .STOP, .INVALID, .REVERT => true,
        else => false,
    };
}

pub fn terminatesControlFlowItem(item: *const AssemblyItemModule.AssemblyItem) bool {
    return item.hasInstruction() and terminatesControlFlow(item.instruction_value.?);
}

pub fn terminatesControlFlow(instruction: InstructionModule.Instruction) bool {
    return switch (instruction) {
        .RETURN, .SELFDESTRUCT, .STOP, .INVALID, .REVERT => true,
        else => false,
    };
}

pub fn reverts(instruction: InstructionModule.Instruction) bool {
    return instruction == .INVALID or instruction == .REVERT;
}

pub fn getDupNumber(item: *const AssemblyItemModule.AssemblyItem) error{OptimizerException}!usize {
    if (!isDupItem(item)) return error.OptimizerException;
    return InstructionModule.getDupNumber(item.instruction_value.?);
}

pub fn getSwapNumber(item: *const AssemblyItemModule.AssemblyItem) error{OptimizerException}!usize {
    if (!isSwapItem(item)) return error.OptimizerException;
    return InstructionModule.getSwapNumber(item.instruction_value.?);
}

pub fn isDeterministic(item: *const AssemblyItemModule.AssemblyItem) error{AssemblyException}!bool {
    if (item.item_type == .VerbatimBytecode) return error.AssemblyException;
    if (!item.hasInstruction()) return true;
    return switch (item.instruction_value.?) {
        .CALL,
        .CALLCODE,
        .DELEGATECALL,
        .STATICCALL,
        .CREATE,
        .CREATE2,
        .GAS,
        .PC,
        .MSIZE,
        .BALANCE,
        .SELFBALANCE,
        .EXTCODESIZE,
        .EXTCODEHASH,
        .RETURNDATACOPY,
        .RETURNDATASIZE,
        => false,
        else => true,
    };
}

pub fn movable(instruction: InstructionModule.Instruction) bool {
    if (InstructionModule.isDupInstruction(instruction) or InstructionModule.isSwapInstruction(instruction)) {
        return false;
    }
    if (InstructionModule.instructionInfo(instruction, EVMVersion.current()).side_effects) return false;
    return switch (instruction) {
        .KECCAK256,
        .BALANCE,
        .SELFBALANCE,
        .EXTCODESIZE,
        .EXTCODEHASH,
        .RETURNDATASIZE,
        .SLOAD,
        .TLOAD,
        .PC,
        .MSIZE,
        .GAS,
        => false,
        else => true,
    };
}

pub fn movableApartFromEffects(instruction: InstructionModule.Instruction) bool {
    return switch (instruction) {
        .EXTCODEHASH,
        .EXTCODESIZE,
        .RETURNDATASIZE,
        .BALANCE,
        .SELFBALANCE,
        .SLOAD,
        .TLOAD,
        .KECCAK256,
        .MLOAD,
        => true,
        else => movable(instruction),
    };
}

pub fn canBeRemoved(instruction: InstructionModule.Instruction) error{AssemblyException}!bool {
    if (InstructionModule.isDupInstruction(instruction) or InstructionModule.isSwapInstruction(instruction)) {
        return error.AssemblyException;
    }
    return !InstructionModule.instructionInfo(instruction, EVMVersion.current()).side_effects;
}

pub fn canBeRemovedIfNoMSize(instruction: InstructionModule.Instruction) error{AssemblyException}!bool {
    if (instruction == .KECCAK256 or instruction == .MLOAD) return true;
    return canBeRemoved(instruction);
}

pub fn memory(instruction: InstructionModule.Instruction) Effect {
    return switch (instruction) {
        .CALLDATACOPY,
        .CODECOPY,
        .EXTCODECOPY,
        .RETURNDATACOPY,
        .MCOPY,
        .MSTORE,
        .MSTORE8,
        .CALL,
        .CALLCODE,
        .DELEGATECALL,
        .STATICCALL,
        => .Write,
        .CREATE,
        .CREATE2,
        .KECCAK256,
        .MLOAD,
        .MSIZE,
        .RETURN,
        .REVERT,
        .LOG0,
        .LOG1,
        .LOG2,
        .LOG3,
        .LOG4,
        => .Read,
        else => .None,
    };
}

pub fn storage(instruction: InstructionModule.Instruction) Effect {
    return switch (instruction) {
        .CALL, .CALLCODE, .DELEGATECALL, .CREATE, .CREATE2, .SSTORE => .Write,
        .SLOAD, .STATICCALL => .Read,
        else => .None,
    };
}

pub fn transientStorage(instruction: InstructionModule.Instruction) Effect {
    return switch (instruction) {
        .CALL, .CALLCODE, .DELEGATECALL, .CREATE, .CREATE2, .TSTORE => .Write,
        .TLOAD, .STATICCALL => .Read,
        else => .None,
    };
}

pub fn otherState(instruction: InstructionModule.Instruction) Effect {
    return switch (instruction) {
        .CALL, .CALLCODE, .DELEGATECALL, .CREATE, .CREATE2, .SELFDESTRUCT, .STATICCALL => .Write,
        .EXTCODESIZE,
        .EXTCODEHASH,
        .RETURNDATASIZE,
        .BALANCE,
        .SELFBALANCE,
        .RETURNDATACOPY,
        .EXTCODECOPY,
        => .Read,
        else => .None,
    };
}

pub fn invalidInPureFunctions(instruction: InstructionModule.Instruction) bool {
    return switch (instruction) {
        .ADDRESS,
        .SELFBALANCE,
        .BALANCE,
        .ORIGIN,
        .CALLER,
        .CALLVALUE,
        .CHAINID,
        .BASEFEE,
        .BLOBBASEFEE,
        .GAS,
        .GASPRICE,
        .EXTCODESIZE,
        .EXTCODECOPY,
        .EXTCODEHASH,
        .BLOCKHASH,
        .BLOBHASH,
        .COINBASE,
        .TIMESTAMP,
        .NUMBER,
        .PREVRANDAO,
        .GASLIMIT,
        .STATICCALL,
        .SLOAD,
        .TLOAD,
        => true,
        else => invalidInViewFunctions(instruction),
    };
}

pub fn invalidInViewFunctions(instruction: InstructionModule.Instruction) bool {
    return switch (instruction) {
        .SSTORE,
        .TSTORE,
        .JUMP,
        .JUMPI,
        .LOG0,
        .LOG1,
        .LOG2,
        .LOG3,
        .LOG4,
        .CREATE,
        .CALL,
        .CALLCODE,
        .DELEGATECALL,
        .CREATE2,
        .SELFDESTRUCT,
        => true,
        else => false,
    };
}

test "opcode effects preserve ordered memory and state access descriptions" {
    const mcopy = try readWriteOperations(.MCOPY);
    try std.testing.expectEqual(@as(usize, 2), mcopy.slice().len);
    try std.testing.expectEqual(Effect.Read, mcopy.slice()[0].effect);
    try std.testing.expectEqual(Effect.Write, mcopy.slice()[1].effect);

    const call = try readWriteOperations(.CALL);
    try std.testing.expectEqual(@as(usize, 6), call.slice().len);
    try std.testing.expectEqual(Location.Memory, call.slice()[0].location);
    try std.testing.expectEqual(Location.Memory, call.slice()[5].location);
}

test "control-flow, mutability, and optimizer classifications cover every opcode" {
    for (0..256) |raw_opcode| {
        const instruction: InstructionModule.Instruction = @enumFromInt(@as(u8, @intCast(raw_opcode)));
        _ = terminatesControlFlow(instruction);
        _ = reverts(instruction);
        _ = movable(instruction);
        _ = movableApartFromEffects(instruction);
        _ = memory(instruction);
        _ = storage(instruction);
        _ = transientStorage(instruction);
        _ = otherState(instruction);
        _ = invalidInPureFunctions(instruction);
        _ = invalidInViewFunctions(instruction);
    }
    try std.testing.expect(movable(.ADD));
    try std.testing.expect(!movable(.SLOAD));
    try std.testing.expect(invalidInPureFunctions(.ADDRESS));
    try std.testing.expect(!invalidInViewFunctions(.SLOAD));
}
