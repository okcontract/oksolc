// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
// Reach both modular literals through the complete unmodified dispatcher.
// Queries/constructors are fixtures, not ExpressionClasses correspondence.
const Rules = @import("src/libevmasm/rule_list.zig");
const Instruction = @import("src/libevmasm/instruction.zig").Instruction;
const DebugData = @import("src/liblangutil/debug_data.zig").DebugData;

pub const Observation = extern struct {
    site: u32,
    for_yul: u32,
    fail_operation: u32,
    fail_constant: u32,
    constant_result: u32,
    operation_result: u32,
    operation_calls: u32,
    constant_calls: u32,
    graph_growth: u32,
    returned_error: u32,
    opcode: u32,
    modulus: u64,
    constant_value: u64,
    nested_length: usize,
    length: usize,
    pointer: usize,
    alignment: usize,
    input_words: [4]u32,
    nested_words: [5]u32,
    observed_words: [3]u32,
};

const Graph = struct {
    observation: *Observation,

    pub fn knownConstantValue(self: *Graph, id: u32) ?u256 {
        return if (id == self.observation.input_words[2]) self.observation.modulus else null;
    }

    pub fn operationArguments(self: *Graph, id: u32, opcode: Instruction) ?[]const u32 {
        if (id == self.observation.input_words[1] and opcode == (if (self.observation.site == 0) Instruction.MUL else Instruction.ADD))
            return self.observation.nested_words[1 .. 1 + self.observation.nested_length];
        return null;
    }

    pub noinline fn makeConstant(self: *Graph, value: u256, _: DebugData) error{OutOfMemory}!u32 {
        self.observation.constant_calls += 1;
        self.observation.constant_value = @truncate(value);
        if (self.observation.fail_constant != 0) return error.OutOfMemory;
        self.observation.graph_growth += 1;
        return self.observation.constant_result;
    }

    pub fn materializeConstant(_: *Graph, _: u32, _: u256, _: DebugData) error{UnexpectedConstructor}!u32 {
        return error.UnexpectedConstructor;
    }

    pub noinline fn makeOperation(self: *Graph, opcode: Instruction, arguments: []const u32, _: DebugData) error{ OutOfMemory, UnexpectedConstructor }!u32 {
        self.observation.operation_calls += 1;
        if (self.observation.operation_calls != 1) return error.UnexpectedConstructor;
        self.observation.opcode = @backingInt(opcode);
        self.observation.length = arguments.len;
        self.observation.pointer = @intFromPtr(arguments.ptr);
        self.observation.alignment = @intFromPtr(arguments.ptr) % @alignOf(u32);
        for (arguments[0..@min(arguments.len, 3)], 0..) |value, index|
            self.observation.observed_words[index] = value;
        if (self.observation.fail_operation != 0) return error.OutOfMemory;
        self.observation.graph_growth += 1;
        return self.observation.operation_result;
    }
};

export fn rule_ternary(observation: *Observation) u32 {
    var graph: Graph = .{ .observation = observation };
    return (Rules.simplifyWithOptions(&graph, .MOD, observation.input_words[1..3], DebugData{}, .{ .for_yul_optimizer = observation.for_yul != 0 }) catch {
        observation.returned_error = 1;
        return 0;
    }) orelse 0;
}
