// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Opt-in production expression-pass adapter. Output is untrusted proof input;
//! only the separate Lean graph validator can establish value preservation.
const std = @import("std");
const Graph = @import("compiler_verification/graph.zig");
const Failure = @import("compiler_verification/graph_failure.zig");
const max_bytes = Graph.max_bytes;
const Node = Graph.Node;
const Request = struct { schema: []const u8, nodes: []const Node, root: u32 };
const Response = struct {
    schema: []const u8,
    requestSha256: []const u8,
    nodes: []const Node,
    root: u32,
    resultIds: []const u32,
    cache: []const Graph.CacheEntry,
};

fn compileAlloc(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    if (bytes.len > max_bytes) return error.InputLimit;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const request = try std.json.parseFromSliceLeaky(Request, a, bytes, .{});
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &digest, .{});
    const hex = std.fmt.bytesToHex(digest, .lower);
    if (std.mem.eql(u8, request.schema, "oksolc.compiler-graph-failure-request.v1")) {
        const observations = try Failure.sweep(&arena, allocator, request.nodes, request.root);
        const encoded = try std.json.Stringify.valueAlloc(a, .{
            .schema = "oksolc.compiler-graph-failure-response.v1",
            .requestSha256 = &hex,
            .resizePolicy = "always-fail",
            .observations = observations,
        }, .{});
        return allocator.print("{s}\n", .{encoded});
    }
    if (!std.mem.eql(u8, request.schema, "oksolc.compiler-graph-request.v1")) return error.UnsupportedSchema;
    const result = try Graph.optimizeInventory(&arena, request.nodes, request.root);
    const encoded = try std.json.Stringify.valueAlloc(a, Response{
        .schema = "oksolc.compiler-graph-response.v1",
        .requestSha256 = &hex,
        .nodes = result.graph.nodes,
        .root = result.graph.root,
        .resultIds = result.result_ids,
        .cache = result.cache,
    }, .{});
    return allocator.print("{s}\n", .{encoded});
}

pub fn main(init: std.process.Init) !void {
    var buffer: [4096]u8 = undefined;
    var input = std.Io.File.stdin().readerStreaming(init.io, &buffer);
    const bytes = try input.interface.allocRemaining(init.gpa, .limited(max_bytes));
    defer init.gpa.free(bytes);
    const output = try compileAlloc(init.gpa, bytes);
    defer init.gpa.free(output);
    try std.Io.File.stdout().writeStreamingAll(init.io, output);
}

const fixture =
    \\{"schema":"oksolc.compiler-graph-request.v1","nodes":[{"input":"x"},{"literal":"0"},{"binary":{"op":"add","left":0,"right":1}}],"root":2}
;

fn allocationFixture(a: std.mem.Allocator) !void {
    const output = try compileAlloc(a, fixture);
    defer a.free(output);
    const response = try std.json.parseFromSlice(Response, a, output, .{});
    defer response.deinit();
    try std.testing.expectEqual(@as(u32, 0), response.value.root);
    try std.testing.expectEqualStrings("x", response.value.nodes[0].input);
    try std.testing.expectEqual(@as(usize, 2), response.value.nodes.len);
    try std.testing.expectEqualSlices(u32, &.{ 0, 1, 0 }, response.value.resultIds);
    try std.testing.expectEqual(@as(usize, 3), response.value.cache.len);
}

test "graph export production pass and allocation failures" {
    try allocationFixture(std.testing.allocator);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, allocationFixture, .{});
}

fn failureAllocationFixture(a: std.mem.Allocator) !void {
    const bytes =
        \\{"schema":"oksolc.compiler-graph-failure-request.v1","nodes":[{"input":"x"},{"literal":"0"},{"binary":{"op":"add","left":0,"right":1}}],"root":2}
    ;
    const output = try compileAlloc(a, bytes);
    defer a.free(output);
    const parsed = try std.json.parseFromSlice(std.json.Value, a, output, .{});
    defer parsed.deinit();
    try std.testing.expectEqualStrings("oksolc.compiler-graph-failure-response.v1", parsed.value.object.get("schema").?.string);
    const observations = parsed.value.object.get("observations").?.array.items;
    try std.testing.expect(observations.len > 1);
    try std.testing.expectEqualStrings("outOfMemory", observations[0].object.get("attempt").?.object.get("outcome").?.string);
    try std.testing.expectEqualStrings("complete", observations[observations.len - 1].object.get("attempt").?.object.get("outcome").?.string);
}

test "graph export failure-sweep observation and serialization OOM" {
    try failureAllocationFixture(std.testing.allocator);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, failureAllocationFixture, .{});
}

test "graph export supports extended opcodes including signextend, byte, sar, addmod, and caller" {
    const a = std.testing.allocator;
    const bytes =
        \\{"schema":"oksolc.compiler-graph-request.v1","nodes":[{"nullary":"caller"},{"literal":"1461501637330902918203684832716283019655932542975"},{"binary":{"op":"and","left":0,"right":1}},{"literal":"248"},{"input":"x"},{"binary":{"op":"shr","left":3,"right":4}},{"literal":"0"},{"binary":{"op":"signextend","left":6,"right":5}},{"ternary":{"op":"addmod","first":2,"second":7,"third":1}}],"root":8}
    ;
    const out = try compileAlloc(a, bytes);
    defer a.free(out);
    const response = try std.json.parseFromSlice(Response, a, out, .{});
    defer response.deinit();
    var saw_sar = false;
    var saw_caller = false;
    for (response.value.nodes) |node| switch (node) {
        .nullary => |op| if (op == .caller) {
            saw_caller = true;
        },
        .binary => |op| if (op.op == .sar) {
            saw_sar = true;
        },
        else => {},
    };
    try std.testing.expect(saw_sar);
    try std.testing.expect(saw_caller);
}

test "graph export rejects malformed unused nodes and unsupported requests" {
    try std.testing.expectError(error.InvalidReference, Graph.validateNodes(&.{ .{ .input = "x" }, .{ .unary = .{ .op = .bitnot, .arg = 1 } } }, 0));
    try std.testing.expectError(error.InvalidGraphSize, Graph.validateNodes(&.{}, 0));
    try std.testing.expectError(error.InvalidInputName, Graph.validateNodes(&.{.{ .input = "x\ncode" }}, 0));
    try std.testing.expectError(error.InvalidLiteral, Graph.literal("+1"));
    try std.testing.expectError(error.InvalidLiteral, Graph.literal("01"));
    try std.testing.expectError(error.InvalidLiteral, Graph.literal("115792089237316195423570985008687907853269984665640564039457584007913129639936"));
    try std.testing.expectError(error.UnsupportedSchema, compileAlloc(std.testing.allocator, "{\"schema\":\"wrong\",\"nodes\":[],\"root\":0}"));
}
