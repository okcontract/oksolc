// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared admitted graph interface to the actual production `ExpressionClasses` pass
//! over the full pure/environmental EVM opcode set used by `RuleList`.
//! Results are untrusted proof certificates until checked by the Lean validator.
const std = @import("std");
const Classes = @import("../libevmasm/expression_classes.zig").ExpressionClasses;
const Instruction = @import("../libevmasm/instruction.zig").Instruction;

pub const max_bytes = 1024 * 1024;
const max_nodes = 256;
const max_expansion = 4096;

pub const Nullary = enum { address, caller, origin, coinbase };
pub const Unary = enum { bitnot, iszero };
pub const Binary = enum {
    add,
    sub,
    mul,
    div,
    sdiv,
    mod,
    smod,
    exp,
    signextend,
    @"and",
    @"or",
    xor,
    byte,
    shl,
    shr,
    sar,
    lt,
    gt,
    slt,
    sgt,
    eq,
};
pub const Ternary = enum { addmod, mulmod };

pub const Node = union(enum) {
    input: []const u8,
    literal: []const u8,
    nullary: Nullary,
    unary: struct { op: Unary, arg: u32 },
    binary: struct { op: Binary, left: u32, right: u32 },
    ternary: struct { op: Ternary, first: u32, second: u32, third: u32 },
};

pub const Graph = struct { nodes: []const Node, root: u32 };
pub const CacheEntry = struct { key: Node, id: u32 };
pub const Inventory = struct { graph: Graph, result_ids: []const u32, cache: []const CacheEntry };
pub const max_cache_entries = 1024;

pub fn nullaryInstruction(op: Nullary) Instruction {
    return switch (op) {
        .address => .ADDRESS,
        .caller => .CALLER,
        .origin => .ORIGIN,
        .coinbase => .COINBASE,
    };
}

pub fn binaryInstruction(op: Binary) Instruction {
    return switch (op) {
        .add => .ADD,
        .sub => .SUB,
        .mul => .MUL,
        .div => .DIV,
        .sdiv => .SDIV,
        .mod => .MOD,
        .smod => .SMOD,
        .exp => .EXP,
        .signextend => .SIGNEXTEND,
        .@"and" => .AND,
        .@"or" => .OR,
        .xor => .XOR,
        .byte => .BYTE,
        .shl => .SHL,
        .shr => .SHR,
        .sar => .SAR,
        .lt => .LT,
        .gt => .GT,
        .slt => .SLT,
        .sgt => .SGT,
        .eq => .EQ,
    };
}

pub fn ternaryInstruction(op: Ternary) Instruction {
    return switch (op) {
        .addmod => .ADDMOD,
        .mulmod => .MULMOD,
    };
}

fn nullaryFromInstruction(op: Instruction) !Nullary {
    return switch (op) {
        .ADDRESS => .address,
        .CALLER => .caller,
        .ORIGIN => .origin,
        .COINBASE => .coinbase,
        else => error.UnsupportedOutput,
    };
}

fn binaryFromInstruction(op: Instruction) !Binary {
    var name: [32]u8 = undefined;
    const original = std.enums.tagName(Instruction, op) orelse return error.UnsupportedOutput;
    if (original.len > name.len) return error.UnsupportedOutput;
    const tag = std.ascii.lowerString(&name, original);
    return std.meta.stringToEnum(Binary, tag) orelse error.UnsupportedOutput;
}

fn ternaryFromInstruction(op: Instruction) !Ternary {
    return switch (op) {
        .ADDMOD => .addmod,
        .MULMOD => .mulmod,
        else => error.UnsupportedOutput,
    };
}

fn operationNode(op: Instruction, arguments: []const u32) !Node {
    if (op == .ADDRESS or op == .CALLER or op == .ORIGIN or op == .COINBASE) {
        if (arguments.len != 0) return error.InvalidArity;
        return .{ .nullary = try nullaryFromInstruction(op) };
    }
    if (op == .NOT or op == .ISZERO) {
        if (arguments.len != 1) return error.InvalidArity;
        return .{ .unary = .{ .op = if (op == .NOT) .bitnot else .iszero, .arg = arguments[0] } };
    }
    if (op == .ADDMOD or op == .MULMOD) {
        if (arguments.len != 3) return error.InvalidArity;
        return .{ .ternary = .{
            .op = try ternaryFromInstruction(op),
            .first = arguments[0],
            .second = arguments[1],
            .third = arguments[2],
        } };
    }
    if (arguments.len != 2) return error.InvalidArity;
    return .{ .binary = .{ .op = try binaryFromInstruction(op), .left = arguments[0], .right = arguments[1] } };
}

pub fn literal(value: []const u8) !u256 {
    if (value.len == 0 or value.len > 78 or (value.len > 1 and value[0] == '0'))
        return error.InvalidLiteral;
    for (value) |byte| if (!std.ascii.isDigit(byte)) return error.InvalidLiteral;
    return std.fmt.parseInt(u256, value, 10) catch return error.InvalidLiteral;
}

pub fn validName(name: []const u8) bool {
    if (name.len == 0 or name.len > 64 or !(std.ascii.isAlphabetic(name[0]) or name[0] == '_')) return false;
    for (name) |byte| if (!(std.ascii.isAlphanumeric(byte) or byte == '_')) return false;
    return true;
}

pub fn validateNodes(nodes: []const Node, root: u32) !void {
    if (nodes.len == 0 or nodes.len > max_nodes or root >= nodes.len) return error.InvalidGraphSize;
    var expanded: [max_nodes]usize = undefined;
    for (nodes, 0..) |node, index| {
        expanded[index] = switch (node) {
            .input => |name| blk: {
                if (!validName(name)) return error.InvalidInputName;
                break :blk 1;
            },
            .literal => |value| blk: {
                _ = try literal(value);
                break :blk 1;
            },
            .nullary => 1,
            .unary => |op| blk: {
                if (op.arg >= index) return error.InvalidReference;
                break :blk 1 + expanded[op.arg];
            },
            .binary => |op| blk: {
                if (op.left >= index or op.right >= index) return error.InvalidReference;
                break :blk 1 + expanded[op.left] + expanded[op.right];
            },
            .ternary => |op| blk: {
                if (op.first >= index or op.second >= index or op.third >= index) return error.InvalidReference;
                break :blk 1 + expanded[op.first] + expanded[op.second] + expanded[op.third];
            },
        };
        if (expanded[index] > max_expansion) return error.ExpansionLimit;
    }
}

/// The caller's phase arena owns results and temporary allocations, including
/// on error. Input names borrow from input; both must outlive serialization.
pub fn optimize(arena: *std.heap.ArenaAllocator, input: []const Node, input_root: u32) !Graph {
    return optimizeImpl(false, arena, input, input_root);
}

/// Capture all returned IDs and actual cache entries before destroying the
/// interner.
pub fn optimizeInventory(arena: *std.heap.ArenaAllocator, input: []const Node, input_root: u32) !Inventory {
    return optimizeImpl(true, arena, input, input_root);
}

fn optimizeImpl(comptime inventory: bool, arena: *std.heap.ArenaAllocator, input: []const Node, input_root: u32) !(if (inventory) Inventory else Graph) {
    const a = arena.allocator();
    try validateNodes(input, input_root);
    var classes = Classes.init(a);
    defer classes.deinit();
    var driver: Driver = .{ .classes = &classes, .allocator = a, .ids = try a.alloc(u32, input.len) };
    try driver.run(input);
    const nodes = try captureNodes(a, &classes, driver.input_names);
    const root = driver.ids[input_root];
    if (root >= nodes.len) return error.InvalidGraphSize;
    const graph: Graph = .{ .nodes = nodes, .root = root };
    if (!inventory) return graph;
    return .{ .graph = graph, .result_ids = driver.ids, .cache = try captureCache(a, &classes, nodes.len, driver.input_names) };
}

const Driver = struct {
    classes: *Classes,
    allocator: std.mem.Allocator,
    input_ids: std.StringHashMapUnmanaged(u32) = .empty,
    input_names: std.AutoHashMapUnmanaged(u32, []const u8) = .empty,
    ids: []u32,
    completed: usize = 0,

    fn run(self: *Driver, input: []const Node) !void {
        const a = self.allocator;
        const classes = self.classes;
        const ids = self.ids;
        const input_ids = &self.input_ids;
        const input_names = &self.input_names;
        for (input, 0..) |node, index| {
            ids[index] = switch (node) {
                .input => |name| blk: {
                    if (input_ids.get(name)) |existing| break :blk existing;
                    const id = try classes.newClass(.{});
                    try input_ids.put(a, name, id);
                    try input_names.put(a, id, name);
                    break :blk id;
                },
                .literal => |value| try classes.makeConstant(try literal(value), .{}),
                .nullary => |op| try classes.makeOperation(nullaryInstruction(op), &.{}, .{}),
                .unary => |op| try classes.makeOperation(if (op.op == .bitnot) .NOT else .ISZERO, &.{ids[op.arg]}, .{}),
                .binary => |op| try classes.makeOperation(binaryInstruction(op.op), &.{ ids[op.left], ids[op.right] }, .{}),
                .ternary => |op| try classes.makeOperation(ternaryInstruction(op.op), &.{ ids[op.first], ids[op.second], ids[op.third] }, .{}),
            };
            if (classes.size() > max_nodes) return error.OutputLimit;
            self.completed = index + 1;
        }
    }
};

fn captureNodes(a: std.mem.Allocator, classes: *const Classes, input_names: std.AutoHashMapUnmanaged(u32, []const u8)) ![]const Node {
    if (classes.size() > max_nodes) return error.OutputLimit;
    const nodes = try a.alloc(Node, classes.size());
    for (classes.representatives.items, 0..) |representative, index| {
        if (representative.id != index) return error.InvalidRepresentative;
        nodes[index] = switch (representative.item.item_type) {
            .UndefinedItem => .{ .input = input_names.get(representative.id) orelse return error.UnknownInput },
            .Push => .{ .literal = try a.print("{d}", .{representative.item.data_value}) },
            .Operation => blk: {
                const op = representative.item.instruction_value orelse return error.MissingOpcode;
                break :blk try operationNode(op, representative.arguments);
            },
            else => return error.UnsupportedOutput,
        };
    }
    if (nodes.len != 0) try validateNodes(nodes, 0);
    return nodes;
}

fn captureCache(a: std.mem.Allocator, classes: *const Classes, node_count: usize, input_names: std.AutoHashMapUnmanaged(u32, []const u8)) ![]const CacheEntry {
    if (classes.expressions.count() > max_cache_entries) return error.CacheLimit;
    const Record = struct {
        entry: CacheEntry,
        order: []const u8,
        fn less(_: void, left: @This(), right: @This()) bool {
            return std.mem.lessThan(u8, left.order, right.order);
        }
    };
    const records = try a.alloc(Record, classes.expressions.count());
    var iterator = classes.expressions.iterator();
    var count: usize = 0;
    while (iterator.next()) |binding| {
        if (count == records.len) return error.InvalidCacheInventory;
        const key = binding.key_ptr.*;
        if (key.sequence_number != 0 or binding.value_ptr.* >= node_count) return error.InvalidCacheInventory;
        const encoded: Node = switch (key.item_type) {
            .UndefinedItem => blk: {
                const base = @as(u256, 1) << 255;
                if (key.instruction != 0 or key.arguments.len != 0 or key.data < base or key.data - base > std.math.maxInt(u32))
                    return error.InvalidCacheInventory;
                break :blk .{ .input = input_names.get(@intCast(key.data - base)) orelse return error.UnknownInput };
            },
            .Push => blk: {
                if (key.instruction != 0 or key.arguments.len != 0) return error.InvalidCacheInventory;
                break :blk .{ .literal = try a.print("{d}", .{key.data}) };
            },
            .Operation => blk: {
                if (key.data != 0) return error.InvalidCacheInventory;
                for (key.arguments) |argument| if (argument >= node_count) return error.InvalidReference;
                break :blk try operationNode(@fromBackingInt(@intCast(key.instruction)), key.arguments);
            },
            else => return error.UnsupportedOutput,
        };
        const entry: CacheEntry = .{ .key = encoded, .id = binding.value_ptr.* };
        records[count] = .{ .entry = entry, .order = try std.json.Stringify.valueAlloc(a, entry, .{}) };
        count += 1;
    }
    if (count != records.len) return error.InvalidCacheInventory;
    std.mem.sort(Record, records, {}, Record.less);
    const cache = try a.alloc(CacheEntry, count);
    for (records, cache) |record, *entry| entry.* = record.entry;
    return cache;
}

pub const Attempt = struct {
    outcome: enum { complete, outOfMemory },
    nodes: []const Node,
    resultIds: []const u32,
    cache: []const CacheEntry,
};

/// Capture the actual graph before deinit on both success and OOM. Evidence
/// and input bookkeeping use the caller's arena; only Classes uses `compiler`.
pub fn captureAttempt(arena: *std.heap.ArenaAllocator, compiler: std.mem.Allocator, input: []const Node, input_root: u32) !Attempt {
    try validateNodes(input, input_root);
    const a = arena.allocator();
    var classes = Classes.init(compiler);
    defer classes.deinit();
    var driver: Driver = .{ .classes = &classes, .allocator = a, .ids = try a.alloc(u32, input.len) };
    try driver.input_ids.ensureTotalCapacity(a, @intCast(input.len));
    try driver.input_names.ensureTotalCapacity(a, @intCast(input.len));
    const outcome: @FieldType(Attempt, "outcome") = if (driver.run(input)) |_| .complete else |err| switch (err) {
        error.OutOfMemory => .outOfMemory,
        else => return err,
    };
    const nodes = try captureNodes(a, &classes, driver.input_names);
    return .{ .outcome = outcome, .nodes = nodes, .resultIds = driver.ids[0..driver.completed], .cache = try captureCache(a, &classes, nodes.len, driver.input_names) };
}

test "graph export rejects unknown output opcodes" {
    try std.testing.expectError(error.UnsupportedOutput, binaryFromInstruction(@fromBackingInt(@intCast(0xff))));
    try std.testing.expectError(error.UnsupportedOutput, binaryFromInstruction(@fromBackingInt(@intCast(0x0c))));
}
