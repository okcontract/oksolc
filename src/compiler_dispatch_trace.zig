// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Opt-in differential adapter for the complete production RuleList dispatcher.
//! Constructors record calls without recursive interning. This tests the exact
//! dispatcher/callback boundary; it is not a compiler-preservation certificate.
const std = @import("std");
const Rules = @import("libevmasm/rule_list.zig");
const Instruction = @import("libevmasm/instruction.zig").Instruction;
const DebugData = @import("liblangutil/debug_data.zig").DebugData;
const EVMVersion = @import("liblangutil/evm_version.zig").EVMVersion;
const Version = @import("liblangutil/evm_version.zig").Version;
const max_bytes = 1024 * 1024;

const Node = struct {
    constant: ?u256 = null,
    instruction: ?Instruction = null,
    arguments: []const u32 = &.{},
};
const Case = struct {
    name: []const u8,
    nodes: []const Node,
    instruction: Instruction,
    arguments: []const u32,
    forYul: bool = false,
    version: ?Version = null,
    failAt: u32 = 0,
};
const Request = struct { schema: []const u8, cases: []const Case };
const Call = struct {
    kind: u8,
    opcode: u8 = 0,
    value: u256 = 0,
    arguments: [4]u32 = @splat(0),
    length: u32 = 0,
    debug: ?i64,
};
const Observation = struct {
    name: []const u8,
    result: ?u32,
    failure: ?[]const u8,
    calls: []const Call,
};
const Trace = struct {
    nodes: []const Node,
    fail_at: u32,
    calls: [16]Call = undefined,
    length: u32 = 0,

    pub fn knownConstantValue(self: *Trace, id: u32) ?u256 {
        return if (id < self.nodes.len) self.nodes[id].constant else null;
    }

    pub fn operationArguments(self: *Trace, id: u32, instruction: Instruction) ?[]const u32 {
        if (id >= self.nodes.len) return null;
        const node = self.nodes[id];
        return if (node.instruction == instruction) node.arguments else null;
    }

    fn record(self: *Trace, call: Call, arguments: []const u32) !u32 {
        if (self.length == self.calls.len or arguments.len > call.arguments.len) return error.Capacity;
        const index = self.length;
        self.calls[index] = call;
        @memcpy(self.calls[index].arguments[0..arguments.len], arguments);
        self.calls[index].length = @intCast(arguments.len);
        self.length += 1;
        if (self.fail_at == self.length) return error.OutOfMemory;
        return 1024 + index;
    }

    pub fn makeConstant(self: *Trace, value: u256, debug: DebugData) !u32 {
        return self.record(.{ .kind = 2, .value = value, .debug = debug.ast_id }, &.{});
    }

    pub fn materializeConstant(self: *Trace, original: u32, value: u256, debug: DebugData) !u32 {
        return self.record(.{ .kind = 3, .value = value, .debug = debug.ast_id }, &.{original});
    }

    pub fn makeOperation(self: *Trace, instruction: Instruction, arguments: []const u32, debug: DebugData) !u32 {
        return self.record(.{ .kind = 1, .opcode = @backingInt(instruction), .debug = debug.ast_id }, arguments);
    }
};

fn traceAlloc(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    if (bytes.len > max_bytes) return error.InputLimit;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const request = try std.json.parseFromSliceLeaky(Request, a, bytes, .{});
    if (!std.mem.eql(u8, request.schema, "oksolc.compiler-dispatch-request.v1")) return error.UnsupportedSchema;
    if (request.cases.len > 512) return error.CaseLimit;
    const observations = try a.alloc(Observation, request.cases.len);
    for (request.cases, observations) |case, *observation| {
        if (case.nodes.len >= 1024) return error.NodeLimit;
        for (case.nodes) |node| {
            if (node.constant != null and (node.instruction != null or node.arguments.len != 0)) return error.InvalidNode;
        }
        var trace = Trace{ .nodes = case.nodes, .fail_at = case.failAt };
        var failure: ?[]const u8 = null;
        const result = Rules.simplifyWithOptions(&trace, case.instruction, case.arguments, .{ .ast_id = 42 }, .{
            .for_yul_optimizer = case.forYul,
            .evm_version = if (case.version) |version| EVMVersion.init(version) else null,
        }) catch |err| blk: {
            failure = @errorName(err);
            break :blk null;
        };
        observation.* = .{
            .name = case.name,
            .result = result,
            .failure = failure,
            .calls = try a.dupe(Call, trace.calls[0..trace.length]),
        };
    }
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &digest, .{});
    const hex = std.fmt.bytesToHex(digest, .lower);
    const encoded = try std.json.Stringify.valueAlloc(a, .{
        .schema = "oksolc.compiler-dispatch-response.v1",
        .requestSha256 = @as([]const u8, &hex),
        .usizeBits = @bitSizeOf(usize),
        .observations = observations,
    }, .{});
    return allocator.print("{s}\n", .{encoded});
}

pub fn main(init: std.process.Init) !void {
    var buffer: [4096]u8 = undefined;
    var input = std.Io.File.stdin().readerStreaming(init.io, &buffer);
    const bytes = try input.interface.allocRemaining(init.gpa, .limited(max_bytes));
    defer init.gpa.free(bytes);
    const output = try traceAlloc(init.gpa, bytes);
    defer init.gpa.free(output);
    try std.Io.File.stdout().writeStreamingAll(init.io, output);
}

const fixture =
    \\{"schema":"oksolc.compiler-dispatch-request.v1","cases":[{"name":"fold","nodes":[{"constant":7},{"constant":3}],"instruction":"ADD","arguments":[0,1],"failAt":1}]}
;

fn allocationFixture(allocator: std.mem.Allocator) !void {
    const output = try traceAlloc(allocator, fixture);
    defer allocator.free(output);
    try std.testing.expect(std.mem.find(u8, output, "OutOfMemory") != null);
    try std.testing.expect(std.mem.find(u8, output, "\"value\":10") != null);
}

test "dispatcher trace retains constructor failure and owns serialized arguments" {
    try allocationFixture(std.testing.allocator);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, allocationFixture, .{});
    var trace = Trace{ .nodes = &.{}, .fail_at = 0 };
    var arguments = [_]u32{ 7, 9 };
    _ = try trace.makeOperation(.ADD, &arguments, .{ .ast_id = 42 });
    arguments[0] = 77;
    try std.testing.expectEqual(@as(u32, 7), trace.calls[0].arguments[0]);
    try std.testing.expectError(error.Capacity, trace.makeOperation(.ADD, &.{ 0, 1, 2, 3, 4 }, .{}));
}

test "dispatcher trace rejects invalid model boundaries" {
    try std.testing.expectError(error.UnsupportedSchema, traceAlloc(std.testing.allocator, "{\"schema\":\"wrong\",\"cases\":[]}"));
    try std.testing.expectError(error.InvalidNode, traceAlloc(std.testing.allocator, "{\"schema\":\"oksolc.compiler-dispatch-request.v1\",\"cases\":[{\"name\":\"bad\",\"nodes\":[{\"constant\":1,\"instruction\":\"ADD\"}],\"instruction\":\"ADD\",\"arguments\":[]}]}"));
}
