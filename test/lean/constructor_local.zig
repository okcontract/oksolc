// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
// Reach the unchanged named-array helper through the complete public simplifier.
// The equality callback supplies occurrence aliases; it is a template fixture,
// not a claim about native ExpressionClasses storage or Yul graph refinement.
const Rules = @import("src/libevmasm/rule_list.zig");
const Instruction = @import("src/libevmasm/instruction.zig").Instruction;
const DebugData = @import("src/liblangutil/debug_data.zig").DebugData;

pub const Observation = extern struct {
    repeated: u32,
    repeated_is_first: u32,
    matches_first: u32,
    matches_second: u32,
    found: u32,
    fail_operation: u32,
    result_id: u32,
    operation_calls: u32,
    constant_calls: u32,
    returned_error: u32,
    opcode: u32,
    first: u32,
    second: u32,
    borrowed_length: usize,
    length: usize,
    pointer: usize,
    borrowed_pointer: usize,
    alignment: usize,
    borrowed: [4]u32,
};

const Graph = struct {
    observation: *Observation,
    opcode: Instruction,

    pub fn knownConstantValue(_: *Graph, _: u32) ?u256 {
        return null;
    }

    pub fn sameExpression(self: *Graph, left: u32, right: u32) bool {
        if (left == right) return true;
        const observed = self.observation;
        const operand = if (left == observed.repeated) right else if (right == observed.repeated) left else return false;
        return (observed.matches_first != 0 and operand == observed.borrowed[1]) or
            (observed.matches_second != 0 and operand == observed.borrowed[2]);
    }

    pub fn operationArguments(self: *Graph, id: u32, opcode: Instruction) ?[]const u32 {
        if (id != 29 or opcode != self.opcode or self.observation.found == 0) return null;
        return self.observation.borrowed[1 .. 1 + self.observation.borrowed_length];
    }

    pub fn makeConstant(self: *Graph, _: u256, _: DebugData) error{UnexpectedConstructor}!u32 {
        self.observation.constant_calls += 1;
        return error.UnexpectedConstructor;
    }

    pub fn materializeConstant(self: *Graph, _: u32, _: u256, _: DebugData) error{UnexpectedConstructor}!u32 {
        self.observation.constant_calls += 1;
        return error.UnexpectedConstructor;
    }

    pub noinline fn makeOperation(self: *Graph, opcode: Instruction, arguments: []const u32, _: DebugData) error{OutOfMemory}!u32 {
        self.observation.operation_calls += 1;
        self.observation.opcode = @backingInt(opcode);
        self.observation.length = arguments.len;
        self.observation.pointer = @intFromPtr(arguments.ptr);
        self.observation.borrowed_pointer = @intFromPtr(self.observation.borrowed[1..].ptr);
        self.observation.alignment = @intFromPtr(arguments.ptr) % @alignOf(u32);
        if (arguments.len == 2) {
            self.observation.first = arguments[0];
            self.observation.second = arguments[1];
        }
        if (self.observation.fail_operation != 0) return error.OutOfMemory;
        return self.observation.result_id;
    }
};

export fn local_operands(observation: *Observation, use_or: u32) u32 {
    const opcode: Instruction = if (use_or != 0) .OR else .AND;
    var graph: Graph = .{ .observation = observation, .opcode = opcode };
    const arguments: [2]u32 = if (observation.repeated_is_first != 0)
        .{ observation.repeated, 29 }
    else
        .{ 29, observation.repeated };
    const result = Rules.simplify(&graph, opcode, &arguments, .{}) catch |err| {
        observation.returned_error = if (err == error.OutOfMemory) 1 else 2;
        return 0;
    };
    return result orelse 0;
}
