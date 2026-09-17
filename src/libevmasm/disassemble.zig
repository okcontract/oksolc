// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Bytecode iteration and textual disassembly translated from `Disassemble.cpp`.

const std = @import("std");
const instruction = @import("instruction.zig");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;

pub const DecodedInstruction = struct {
    instruction: instruction.Instruction,
    data: u256,
};

pub const InstructionIterator = struct {
    code: []const u8,
    evm_version: EVMVersion,
    index: usize = 0,

    pub fn next(self: *@This()) ?DecodedInstruction {
        if (self.index >= self.code.len) return null;
        const decoded: instruction.Instruction = @enumFromInt(self.code[self.index]);
        self.index += 1;
        var additional: u8 = if (instruction.isValidInstruction(decoded))
            instruction.instructionInfo(decoded, self.evm_version).additional
        else
            0;
        var data: u256 = 0;
        while (additional != 0) : (additional -= 1) {
            data <<= 8;
            if (self.index < self.code.len) {
                data |= self.code[self.index];
                self.index += 1;
            }
        }
        return .{ .instruction = decoded, .data = data };
    }
};

pub fn iterator(code: []const u8, evm_version: EVMVersion) InstructionIterator {
    return .{ .code = code, .evm_version = evm_version };
}

pub fn eachInstruction(
    code: []const u8,
    evm_version: EVMVersion,
    context: anytype,
    comptime on_instruction: anytype,
) void {
    var decoded = iterator(code, evm_version);
    while (decoded.next()) |item| on_instruction(context, item.instruction, item.data);
}

pub fn disassembleAlloc(
    allocator: std.mem.Allocator,
    code: []const u8,
    evm_version: EVMVersion,
    delimiter: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var decoded = iterator(code, evm_version);
    while (decoded.next()) |item| {
        if (!instruction.isValidInstruction(item.instruction)) {
            try appendFormat(allocator, &output, "0x{X}", .{@intFromEnum(item.instruction)});
        } else {
            const info = instruction.instructionInfo(item.instruction, evm_version);
            try output.appendSlice(allocator, info.name);
            if (info.additional != 0)
                try appendFormat(allocator, &output, " 0x{X}", .{item.data});
        }
        try output.appendSlice(allocator, delimiter);
    }
    return output.toOwnedSlice(allocator);
}

fn appendFormat(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    comptime format: []const u8,
    args: anytype,
) std.mem.Allocator.Error!void {
    const formatted = try std.fmt.allocPrint(allocator, format, args);
    defer allocator.free(formatted);
    try output.appendSlice(allocator, formatted);
}

test "truncated push data is right-padded with zero bytes" {
    const code = [_]u8{ 0x60, 0x01, 0x61, 0xab };
    var decoded = iterator(&code, EVMVersion.current());
    const first = decoded.next().?;
    try std.testing.expectEqual(instruction.Instruction.PUSH1, first.instruction);
    try std.testing.expectEqual(@as(u256, 1), first.data);
    const second = decoded.next().?;
    try std.testing.expectEqual(instruction.Instruction.PUSH2, second.instruction);
    try std.testing.expectEqual(@as(u256, 0xab00), second.data);
    try std.testing.expect(decoded.next() == null);

    const text = try disassembleAlloc(std.testing.allocator, &code, EVMVersion.current(), " ");
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("PUSH1 0x1 PUSH2 0xAB00 ", text);
}

test "invalid byte values remain visible in disassembly" {
    const text = try disassembleAlloc(
        std.testing.allocator,
        &.{ 0x0c, 0x00 },
        EVMVersion.current(),
        "\n",
    );
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings("0xC\nSTOP\n", text);
}
