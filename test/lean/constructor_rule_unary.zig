// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
// Reach the three live unary literals through the unmodified complete dispatcher.
// Query and constructor implementations are controlled fixtures, not native
// ExpressionClasses correspondence or a proof of the enclosing exponent rule.
const Rules = @import("src/libevmasm/rule_list.zig");
const Instruction = @import("src/libevmasm/instruction.zig").Instruction;
const DebugData = @import("src/liblangutil/debug_data.zig").DebugData;
const EVMVersion = @import("src/liblangutil/evm_version.zig").EVMVersion;

pub const Event = extern struct {
    opcode: u32,
    first: u32,
    second: u32,
    length: usize,
    pointer: usize,
    alignment: usize,
};
pub const Observation = extern struct {
    site: u32,
    fail_operation: u32,
    fail_constant: u32,
    constant_result: u32,
    first_result: u32,
    second_result: u32,
    third_result: u32,
    operation_calls: u32,
    constant_calls: u32,
    graph_growth: u32,
    returned_error: u32,
    constant_low_word: u32,
    second_length: usize,
    third_length: usize,
    input_words: [4]u32,
    second_words: [4]u32,
    third_words: [4]u32,
    events: [3]Event,
};

const Graph = struct {
    observation: *Observation,

    pub fn knownConstantValue(self: *Graph, id: u32) ?u256 {
        if (id != 7 or self.observation.site == 0) return null;
        return if (self.observation.site == 1) 0 else ~@as(u256, 0);
    }

    pub fn operationArguments(self: *Graph, id: u32, opcode: Instruction) ?[]const u32 {
        if (self.observation.site != 0 or opcode != .ISZERO) return null;
        if (id == 29) return self.observation.second_words[1 .. 1 + self.observation.second_length];
        if (id == 17) return self.observation.third_words[1 .. 1 + self.observation.third_length];
        return null;
    }

    pub noinline fn makeConstant(self: *Graph, value: u256, _: DebugData) error{OutOfMemory}!u32 {
        self.observation.constant_calls += 1;
        self.observation.constant_low_word = @truncate(value);
        if (self.observation.fail_constant != 0) return error.OutOfMemory;
        self.observation.graph_growth += 1;
        return self.observation.constant_result;
    }

    pub fn materializeConstant(_: *Graph, _: u32, _: u256, _: DebugData) error{UnexpectedConstructor}!u32 {
        return error.UnexpectedConstructor;
    }

    pub noinline fn makeOperation(self: *Graph, opcode: Instruction, arguments: []const u32, _: DebugData) error{ OutOfMemory, UnexpectedConstructor }!u32 {
        const index = self.observation.operation_calls;
        self.observation.operation_calls += 1;
        if (index >= 3) return error.UnexpectedConstructor;
        self.observation.events[index] = .{
            .opcode = @backingInt(opcode),
            .first = if (arguments.len > 0) arguments[0] else 0xA5A5A5A5,
            .second = if (arguments.len > 1) arguments[1] else 0xA5A5A5A5,
            .length = arguments.len,
            .pointer = @intFromPtr(arguments.ptr),
            .alignment = @intFromPtr(arguments.ptr) % @alignOf(u32),
        };
        if (self.observation.fail_operation == self.observation.operation_calls) return error.OutOfMemory;
        self.observation.graph_growth += 1;
        return switch (index) {
            0 => self.observation.first_result,
            1 => self.observation.second_result,
            else => self.observation.third_result,
        };
    }
};

export fn rule_literal(observation: *Observation) u32 {
    var graph: Graph = .{ .observation = observation };
    const arguments: []const u32 = observation.input_words[1..if (observation.site == 0) 2 else 3];
    return (Rules.simplifyWithOptions(&graph, if (observation.site == 0) .ISZERO else .EXP, arguments, DebugData{}, .{ .evm_version = EVMVersion.init(.Osaka) }) catch {
        observation.returned_error = 1;
        return 0;
    }) orelse 0;
}
