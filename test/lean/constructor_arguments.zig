// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

// The capture gate copies this fixture beside an exact snapshot of src/.
// Primitive callbacks inject ordinary failures; the production apply body,
// argument literal, Instruction and DebugData are imported without rewriting.
const Algebraic = @import("src/libevmasm/algebraic_rules.zig");
const Instruction = @import("src/libevmasm/instruction.zig").Instruction;
const DebugData = @import("src/liblangutil/debug_data.zig").DebugData;

pub const Observation = extern struct {
    fail_constant: u32,
    fail_operation: u32,
    constant_id: u32,
    result_id: u32,
    constant_calls: u32,
    operation_calls: u32,
    graph_growth: u32,
    returned_error: u32,
    opcode: u32,
    length: usize,
    alignment: usize,
    first: u32,
    second: u32,
};

const Graph = struct {
    observation: *Observation,

    pub noinline fn makeConstant(self: *Graph, value: u256, _: DebugData) error{OutOfMemory}!u32 {
        self.observation.constant_calls += 1;
        if (self.observation.fail_constant != 0) return error.OutOfMemory;
        if (value != 0) unreachable;
        self.observation.graph_growth += 1;
        return self.observation.constant_id;
    }

    pub noinline fn makeOperation(self: *Graph, opcode: Instruction, arguments: []const u32, _: DebugData) error{OutOfMemory}!u32 {
        self.observation.operation_calls += 1;
        self.observation.opcode = @backingInt(opcode);
        self.observation.length = arguments.len;
        self.observation.alignment = @intFromPtr(arguments.ptr) % @alignOf(u32);
        self.observation.first = arguments[0];
        self.observation.second = if (arguments.len > 1) arguments[1] else 0;
        if (self.observation.fail_operation != 0) return error.OutOfMemory;
        return self.observation.result_id;
    }
};

export fn negate_left(observation: *Observation, left: u32, right: u32) u32 {
    var graph: Graph = .{ .observation = observation };
    return @call(.always_inline, Algebraic.apply, .{ .neg_left, &graph, left, right, DebugData{} }) catch {
        observation.returned_error = 1;
        return 0;
    };
}

export fn negate_right(observation: *Observation, left: u32, right: u32) u32 {
    var graph: Graph = .{ .observation = observation };
    return @call(.always_inline, Algebraic.apply, .{ .neg_right, &graph, left, right, DebugData{} }) catch {
        observation.returned_error = 1;
        return 0;
    };
}
