// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
// Run the unmodified dispatcher with controlled constructor observations.
// Input mutation is an evaluation-order control, not native graph refinement.
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
    fail_at: u32,
    mutate_input: u32,
    replacement: u32,
    constant_result: u32,
    parity_result: u32,
    even_result: u32,
    final_result: u32,
    call_count: u32,
    graph_growth: u32,
    returned_error: u32,
    base_words: [4]u64,
    input_words: [4]u32,
    events: [4]Event,
};

const Graph = struct {
    observation: *Observation,
    mutation_index: usize = 2,

    pub fn knownConstantValue(self: *Graph, id: u32) ?u256 {
        if (id != 7) return null;
        const words = self.observation.base_words;
        return @as(u256, words[0]) | (@as(u256, words[1]) << 64) |
            (@as(u256, words[2]) << 128) | (@as(u256, words[3]) << 192);
    }

    pub fn operationArguments(_: *Graph, _: u32, _: Instruction) ?[]const u32 {
        return null;
    }

    pub noinline fn makeConstant(self: *Graph, value: u256, _: DebugData) error{ OutOfMemory, UnexpectedConstructor }!u32 {
        const index = self.observation.call_count;
        self.observation.call_count += 1;
        if (index != 0) return error.UnexpectedConstructor;
        self.observation.events[index] = .{
            .opcode = 256,
            .first = @truncate(value),
            .second = 0xA5A5A5A5,
            .length = 0,
            .pointer = 0,
            .alignment = 0,
        };
        if (self.observation.fail_at == self.observation.call_count) return error.OutOfMemory;
        self.observation.graph_growth += 1;
        if (self.observation.mutate_input != 0) self.observation.input_words[self.mutation_index] = self.observation.replacement;
        return self.observation.constant_result;
    }

    // Keep other dispatcher initializer bodies observable to AIR. Any reached
    // materialization is an unexpected event and fails the native observations.
    pub noinline fn materializeConstant(self: *Graph, _: u32, _: u256, _: DebugData) error{UnexpectedConstructor}!u32 {
        self.observation.call_count += 1;
        self.observation.returned_error = 2;
        return self.observation.constant_result;
    }

    pub noinline fn makeOperation(self: *Graph, opcode: Instruction, arguments: []const u32, _: DebugData) error{ OutOfMemory, UnexpectedConstructor }!u32 {
        const index = self.observation.call_count;
        self.observation.call_count += 1;
        if (index == 0 or index >= 4) return error.UnexpectedConstructor;
        self.observation.events[index] = .{
            .opcode = @backingInt(opcode),
            .first = if (arguments.len > 0) arguments[0] else 0xA5A5A5A5,
            .second = if (arguments.len > 1) arguments[1] else 0xA5A5A5A5,
            .length = arguments.len,
            .pointer = @intFromPtr(arguments.ptr),
            .alignment = @intFromPtr(arguments.ptr) % @alignOf(u32),
        };
        if (self.observation.fail_at == self.observation.call_count) return error.OutOfMemory;
        self.observation.graph_growth += 1;
        return switch (index) {
            1 => self.observation.parity_result,
            2 => self.observation.even_result,
            else => self.observation.final_result,
        };
    }
};

export fn max_exponent(observation: *Observation) u32 {
    var graph: Graph = .{ .observation = observation };
    return (Rules.simplifyWithOptions(&graph, .EXP, observation.input_words[1..3], DebugData{}, .{ .evm_version = EVMVersion.init(.Osaka) }) catch {
        observation.returned_error = 1;
        return 0;
    }) orelse 0;
}

// Reuse the same observations for the four adjacent shift literal sites.
// A child mutation distinguishes reads before and after the constant call.
export fn shift_input(observation: *Observation, site: u32) u32 {
    const instruction: Instruction = switch (site) {
        0 => .EXP,
        1, 2 => .MUL,
        3 => .DIV,
        else => {
            observation.returned_error = 2;
            return 0;
        },
    };
    var graph: Graph = .{ .observation = observation, .mutation_index = if (site < 2) 2 else 1 };
    return (Rules.simplifyWithOptions(&graph, instruction, observation.input_words[1..3], DebugData{}, .{ .evm_version = EVMVersion.init(.Osaka) }) catch {
        observation.returned_error = 1;
        return 0;
    }) orelse 0;
}
