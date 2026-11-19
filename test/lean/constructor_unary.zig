// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
// Import the unmodified production body; callbacks observe the actual literals
// during their lifetime and inject an ordinary error at either call boundary.
const Algebraic = @import("src/libevmasm/algebraic_rules.zig");
const Instruction = @import("src/libevmasm/instruction.zig").Instruction;
const DebugData = @import("src/liblangutil/debug_data.zig").DebugData;

pub const Event = extern struct { opcode: u32, operand: u32, length: usize, pointer: usize, alignment: usize };
pub const Observation = extern struct {
    fail_at: u32,
    first_result: u32,
    second_result: u32,
    operation_calls: u32,
    graph_growth: u32,
    returned_error: u32,
    events: [2]Event,
};

const Graph = struct {
    observation: *Observation,

    pub fn makeConstant(_: *Graph, _: u256, _: DebugData) error{OutOfMemory}!u32 {
        unreachable;
    }

    pub noinline fn makeOperation(self: *Graph, opcode: Instruction, arguments: []const u32, _: DebugData) error{OutOfMemory}!u32 {
        const index = self.observation.operation_calls;
        self.observation.operation_calls += 1;
        self.observation.events[index] = .{
            .opcode = @backingInt(opcode),
            .operand = arguments[0],
            .length = arguments.len,
            .pointer = @intFromPtr(arguments.ptr),
            .alignment = @intFromPtr(arguments.ptr) % @alignOf(u32),
        };
        if (self.observation.fail_at == self.observation.operation_calls) return error.OutOfMemory;
        self.observation.graph_growth += 1;
        return if (index == 0) self.observation.first_result else self.observation.second_result;
    }
};

fn run(comptime replacement: Algebraic.Replacement, observation: *Observation, left: u32, right: u32) u32 {
    var graph: Graph = .{ .observation = observation };
    return @call(.always_inline, Algebraic.apply, .{ replacement, &graph, left, right, DebugData{} }) catch {
        observation.returned_error = 1;
        return 0;
    };
}

export fn not_right(observation: *Observation, left: u32, right: u32) u32 {
    return @call(.always_inline, run, .{ .not_right, observation, left, right });
}
export fn iszero_left(observation: *Observation, left: u32, right: u32) u32 {
    return @call(.always_inline, run, .{ .iszero_left, observation, left, right });
}
export fn iszero_right(observation: *Observation, left: u32, right: u32) u32 {
    return @call(.always_inline, run, .{ .iszero_right, observation, left, right });
}
export fn bool_left(observation: *Observation, left: u32, right: u32) u32 {
    return @call(.always_inline, run, .{ .bool_left, observation, left, right });
}
export fn bool_right(observation: *Observation, left: u32, right: u32) u32 {
    return @call(.always_inline, run, .{ .bool_right, observation, left, right });
}
