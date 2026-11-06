// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Opt-in resolved Solidity word projection -> production expression pass ->
//! production assembler. Exact bytes require independent Lean validation.
const std = @import("std");
const Graph = @import("compiler_verification/graph.zig");
const Assembly = @import("libevmasm/assembly.zig").Assembly;
const AssemblyItem = @import("libevmasm/assembly_item.zig").AssemblyItem;
const Instructions = @import("libevmasm/instruction.zig");

const Request = struct {
    schema: []const u8,
    arithmetic: []const u8,
    evmVersion: []const u8,
    parameters: []const []const u8,
    nodes: []const Graph.Node,
    root: u32,
};
const Response = struct { schema: []const u8, requestSha256: []const u8, bytecode: []const u8 };
const max_code_bytes = 4096;

fn parameterIndex(parameters: []const []const u8, name: []const u8) !usize {
    for (parameters, 0..) |parameter, index|
        if (std.mem.eql(u8, parameter, name)) return index;
    return error.UnknownParameter;
}

/// Validate every source node, including unused ones. Source shifts have
/// Solidity value/count order; conversion to EVM count/value happens here.
fn lower(a: std.mem.Allocator, request: Request) ![]const Graph.Node {
    if (!std.mem.eql(u8, request.schema, "oksolc.compiler-word-request.v1")) return error.UnsupportedSchema;
    if (!std.mem.eql(u8, request.arithmetic, "unchecked")) return error.UnsupportedArithmetic;
    if (!std.mem.eql(u8, request.evmVersion, "cancun")) return error.UnsupportedFork;
    if (request.parameters.len > 16) return error.ParameterLimit;
    for (request.parameters, 0..) |parameter, index| {
        if (!Graph.validName(parameter)) return error.InvalidParameter;
        for (request.parameters[0..index]) |previous|
            if (std.mem.eql(u8, parameter, previous)) return error.DuplicateParameter;
    }
    try Graph.validateNodes(request.nodes, request.root);
    const nodes = try a.dupe(Graph.Node, request.nodes);
    for (nodes) |*node| switch (node.*) {
        .input => |name| _ = try parameterIndex(request.parameters, name),
        .literal => {},
        .nullary => return error.UnsupportedSourceOperation,
        .unary => |op| if (op.op != .bitnot) return error.UnsupportedSourceOperation,
        .binary => |*op| switch (op.op) {
            .add, .sub, .mul, .@"and", .@"or", .xor => {},
            .shl, .shr => std.mem.swap(u32, &op.left, &op.right),
            else => return error.UnsupportedSourceOperation,
        },
        .ternary => return error.UnsupportedSourceOperation,
    };
    return nodes;
}

/// The input stack is parameters in top-to-bottom order and is preserved.
/// The temporary count is derived from the assembler's actual stack deposit.
fn emit(assembly: *Assembly, nodes: []const Graph.Node, root: u32, parameters: []const []const u8) anyerror!void {
    switch (nodes[root]) {
        .input => |name| {
            const position = try parameterIndex(parameters, name);
            const deposit = assembly.deposit();
            if (deposit < parameters.len) return error.InvalidStackDeposit;
            const depth = @as(usize, @intCast(deposit)) - parameters.len + position + 1;
            if (depth > 16) return error.DuplicateDepthLimit;
            _ = try assembly.append(AssemblyItem.initInstruction(Instructions.dupInstruction(@intCast(depth)), .{}));
        },
        .literal => |value| _ = try assembly.append(AssemblyItem.initPush(try Graph.literal(value), .{})),
        .nullary => |op| _ = try assembly.append(AssemblyItem.initInstruction(Graph.nullaryInstruction(op), .{})),
        .unary => |op| {
            try emit(assembly, nodes, op.arg, parameters);
            _ = try assembly.append(AssemblyItem.initInstruction(if (op.op == .bitnot) .NOT else .ISZERO, .{}));
        },
        .binary => |op| {
            // EVM pops the left operand first.
            try emit(assembly, nodes, op.right, parameters);
            try emit(assembly, nodes, op.left, parameters);
            _ = try assembly.append(AssemblyItem.initInstruction(Graph.binaryInstruction(op.op), .{}));
        },
        .ternary => |op| {
            try emit(assembly, nodes, op.third, parameters);
            try emit(assembly, nodes, op.second, parameters);
            try emit(assembly, nodes, op.first, parameters);
            _ = try assembly.append(AssemblyItem.initInstruction(Graph.ternaryInstruction(op.op), .{}));
        },
    }
    if (assembly.deposit() > 1024 or assembly.itemsConst().len > max_code_bytes) return error.OutputLimit;
}

fn compileAlloc(allocator: std.mem.Allocator, bytes: []const u8) ![]u8 {
    if (bytes.len > Graph.max_bytes) return error.InputLimit;
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const request = try std.json.parseFromSliceLeaky(Request, a, bytes, .{});
    const lowered = try lower(a, request);
    const result = try Graph.optimize(&arena, lowered, request.root);
    var assembly = try Assembly.init(a, .{ .version = .Cancun }, false, "compiler-word-verification");
    defer assembly.deinit();
    try assembly.setDeposit(@intCast(request.parameters.len));
    try emit(&assembly, result.nodes, result.root, request.parameters);
    if (assembly.deposit() != request.parameters.len + 1) return error.InvalidStackDeposit;
    const object = try assembly.assemble();
    if (object.link_references.items.len != 0 or object.immutable_references.items.len != 0)
        return error.UnresolvedReferences;
    if (object.bytecode.items.len == 0 or object.bytecode.items.len > max_code_bytes) return error.OutputLimit;
    var hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &hash, .{});
    const digest = std.fmt.bytesToHex(hash, .lower);
    const hex = try a.print("{x}", .{object.bytecode.items});
    const encoded = try std.json.Stringify.valueAlloc(a, Response{
        .schema = "oksolc.compiler-word-response.v1",
        .requestSha256 = &digest,
        .bytecode = hex,
    }, .{});
    return allocator.print("{s}\n", .{encoded});
}

pub fn main(init: std.process.Init) !void {
    var buffer: [4096]u8 = undefined;
    var input = std.Io.File.stdin().readerStreaming(init.io, &buffer);
    const bytes = try input.interface.allocRemaining(init.gpa, .limited(Graph.max_bytes));
    defer init.gpa.free(bytes);
    const output = try compileAlloc(init.gpa, bytes);
    defer init.gpa.free(output);
    try std.Io.File.stdout().writeStreamingAll(init.io, output);
}

const fixture =
    \\{"schema":"oksolc.compiler-word-request.v1","arithmetic":"unchecked","evmVersion":"cancun","parameters":["x","y","frame"],"nodes":[{"input":"x"},{"input":"y"},{"binary":{"op":"shl","left":0,"right":1}}],"root":2}
;

fn allocationFixture(a: std.mem.Allocator) !void {
    const bytes = try compileAlloc(a, fixture);
    defer a.free(bytes);
    const response = try std.json.parseFromSlice(Response, a, bytes, .{});
    defer response.deinit();
    try std.testing.expectEqualStrings("80821b", response.value.bytecode);
    const constant_fixture =
        \\{"schema":"oksolc.compiler-word-request.v1","arithmetic":"unchecked","evmVersion":"cancun","parameters":[],"nodes":[{"literal":"0"},{"unary":{"op":"bitnot","arg":0}}],"root":1}
    ;
    const constant_bytes = try compileAlloc(a, constant_fixture);
    defer a.free(constant_bytes);
    const constant_response = try std.json.parseFromSlice(Response, a, constant_bytes, .{});
    defer constant_response.deinit();
    try std.testing.expectEqualStrings("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", constant_response.value.bytecode);
}

test "word export emits actual assembled shifts and handles allocation failure" {
    try allocationFixture(std.testing.allocator);
    var backing = std.testing.FailingAllocator.init(std.testing.allocator, .{ .resize_fail_index = 0 });
    try std.testing.checkAllAllocationFailures(backing.allocator(), allocationFixture, .{});
}

test "word export rejects unsupported source profiles and stack interfaces" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const original = try std.json.parseFromSliceLeaky(Request, a, fixture, .{});
    var request = original;
    request.arithmetic = "checked";
    try std.testing.expectError(error.UnsupportedArithmetic, lower(a, request));
    request = original;
    request.evmVersion = "osaka";
    try std.testing.expectError(error.UnsupportedFork, lower(a, request));
    request = original;
    request.parameters = &.{ "x", "x" };
    try std.testing.expectError(error.DuplicateParameter, lower(a, request));
    request.parameters = &.{"x"};
    try std.testing.expectError(error.UnknownParameter, lower(a, request));
    request = original;
    request.nodes = &.{ .{ .input = "x" }, .{ .binary = .{ .op = .div, .left = 0, .right = 0 } } };
    request.root = 0;
    try std.testing.expectError(error.UnsupportedSourceOperation, lower(a, request));
    var assembly = try Assembly.init(a, .{ .version = .Cancun }, false, "depth-test");
    defer assembly.deinit();
    try assembly.setDeposit(17);
    try std.testing.expectError(error.DuplicateDepthLimit, emit(&assembly, &.{.{ .input = "x" }}, 0, &.{"x"}));
}
