// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Symbolic stack formatting and the iterative stack-shuffling algorithm used
//! by optimized Yul EVM code generation.

const std = @import("std");
const CFG = @import("control_flow_graph.zig");
const Numeric = @import("../../../libsolutil/numeric.zig");
const Utilities = @import("../../utilities.zig");

pub fn stackSlotToStringAlloc(
    allocator: std.mem.Allocator,
    slot: CFG.StackSlot,
    dialect: @import("../../ast.zig").Dialect,
) ![]u8 {
    return switch (slot) {
        .function_call_return_label => |value| std.fmt.allocPrint(
            allocator,
            "RET[{s}]",
            .{try Utilities.resolveFunctionName(&value.call.function_name, dialect)},
        ),
        .function_return_label => allocator.dupe(u8, "RET"),
        .variable => |value| allocator.dupe(u8, try value.variable.name.str()),
        .literal => |value| Numeric.toCompactHexWithPrefixAlloc(u256, allocator, value.value),
        .temporary => |value| std.fmt.allocPrint(
            allocator,
            "TMP[{s}, {d}]",
            .{ try Utilities.resolveFunctionName(&value.call.function_name, dialect), value.index },
        ),
        .junk => allocator.dupe(u8, "JUNK"),
    };
}

pub fn stackToStringAlloc(
    allocator: std.mem.Allocator,
    stack: []const CFG.StackSlot,
    dialect: @import("../../ast.zig").Dialect,
) ![]u8 {
    var result: std.ArrayList(u8) = .empty;
    errdefer result.deinit(allocator);
    try result.appendSlice(allocator, "[ ");
    for (stack) |slot| {
        const text = try stackSlotToStringAlloc(allocator, slot, dialect);
        defer allocator.free(text);
        try result.appendSlice(allocator, text);
        try result.append(allocator, ' ');
    }
    try result.append(allocator, ']');
    return result.toOwnedSlice(allocator);
}

fn Operations(comptime CallbackType: type) type {
    return struct {
        allocator: std.mem.Allocator,
        current_stack: *CFG.Stack,
        target_stack: []const CFG.StackSlot,
        callbacks: CallbackType,
        reachable_stack_depth: usize,

        const Self = @This();

        fn isCompatible(self: *const Self, source: usize, target: usize) bool {
            return source < self.current_stack.items.len and
                target < self.target_stack.len and
                (self.target_stack[target] == .junk or
                    self.current_stack.items[source].eql(self.target_stack[target]));
        }

        fn sourceIsSame(self: *const Self, left: usize, right: usize) bool {
            return self.current_stack.items[left].eql(self.current_stack.items[right]);
        }

        fn multiplicity(self: *const Self, slot: CFG.StackSlot) i32 {
            var result: i32 = 0;
            for (self.current_stack.items) |current| {
                if (current.eql(slot)) result -= 1;
            }
            for (self.target_stack, 0..) |target, offset| {
                const desired = if (target == .junk and offset < self.current_stack.items.len)
                    self.current_stack.items[offset]
                else
                    target;
                if (desired.eql(slot)) result += 1;
            }
            return result;
        }

        fn sourceMultiplicity(self: *const Self, offset: usize) i32 {
            return self.multiplicity(self.current_stack.items[offset]);
        }

        fn targetMultiplicity(self: *const Self, offset: usize) i32 {
            return self.multiplicity(self.target_stack[offset]);
        }

        fn targetIsArbitrary(self: *const Self, offset: usize) bool {
            return offset < self.target_stack.len and self.target_stack[offset] == .junk;
        }

        fn sourceSize(self: *const Self) usize {
            return self.current_stack.items.len;
        }

        fn targetSize(self: *const Self) usize {
            return self.target_stack.len;
        }

        fn swap(self: *Self, depth: usize) !void {
            try self.callbacks.swap(depth);
            const top = self.current_stack.items.len - 1;
            std.mem.swap(
                CFG.StackSlot,
                &self.current_stack.items[top - depth],
                &self.current_stack.items[top],
            );
        }

        fn pop(self: *Self) !void {
            try self.callbacks.pop();
            _ = self.current_stack.pop();
        }

        fn pushOrDupTarget(self: *Self, offset: usize) !void {
            const target = self.target_stack[offset];
            try self.callbacks.pushOrDup(target);
            try self.current_stack.append(self.allocator, target);
        }
    };
}

fn dupDeepSlotIfRequired(ops: anytype) !bool {
    const reachable = ops.reachable_stack_depth;
    if (reachable <= 1 or ops.sourceSize() < reachable - 1) return false;
    const deep_limit = ops.sourceSize() - (reachable - 1);
    for (0..deep_limit) |source_offset| {
        if (!ops.isCompatible(source_offset, source_offset)) {
            if (ops.isCompatible(ops.sourceSize() - 1, source_offset)) {
                try ops.swap(ops.sourceSize() - source_offset - 1);
                return true;
            }
            if (try bringUpTargetSlot(ops, source_offset)) return true;
            var offset = source_offset + 1;
            while (offset < ops.sourceSize()) : (offset += 1) {
                if (ops.isCompatible(offset, source_offset)) {
                    try ops.swap(ops.sourceSize() - offset - 1);
                    return true;
                }
            }
        } else if (ops.sourceMultiplicity(source_offset) > 0) {
            var occurs_later = false;
            var offset = source_offset + 1;
            while (offset < ops.sourceSize()) : (offset += 1) {
                if (ops.sourceIsSame(source_offset, offset)) {
                    occurs_later = true;
                    break;
                }
            }
            if (occurs_later) continue;
            for (0..ops.targetSize()) |target_offset| {
                if (!ops.targetIsArbitrary(target_offset) and
                    ops.isCompatible(source_offset, target_offset))
                {
                    try ops.pushOrDupTarget(target_offset);
                    return true;
                }
            }
        }
    }
    return false;
}

fn bringUpTargetSlot(ops: anytype, target_offset: usize) !bool {
    var to_visit: std.ArrayList(usize) = .empty;
    defer to_visit.deinit(ops.allocator);
    var visited = std.AutoHashMap(usize, void).init(ops.allocator);
    defer visited.deinit();
    try to_visit.append(ops.allocator, target_offset);
    try visited.put(target_offset, {});
    var cursor: usize = 0;
    while (cursor < to_visit.items.len) : (cursor += 1) {
        const offset = to_visit.items[cursor];
        if (ops.targetMultiplicity(offset) > 0) {
            try ops.pushOrDupTarget(offset);
            return true;
        }
        for (0..@min(ops.sourceSize(), ops.targetSize())) |next_offset| {
            if (!ops.isCompatible(next_offset, next_offset) and
                ops.isCompatible(next_offset, offset))
            {
                const inserted = try visited.getOrPut(next_offset);
                if (!inserted.found_existing) try to_visit.append(ops.allocator, next_offset);
            }
        }
    }
    return false;
}

fn shuffleStep(ops: anytype) !bool {
    var all_final = true;
    for (0..ops.sourceSize()) |index| {
        if (!ops.isCompatible(index, index)) {
            all_final = false;
            break;
        }
    }
    if (all_final) {
        if (ops.sourceSize() < ops.targetSize()) {
            if (!try dupDeepSlotIfRequired(ops) and !try bringUpTargetSlot(ops, ops.sourceSize()))
                return error.InvalidStackLayout;
            return true;
        }
        return false;
    }

    const source_top = ops.sourceSize() - 1;
    if (ops.sourceMultiplicity(source_top) < 0 and !ops.targetIsArbitrary(source_top)) {
        try ops.pop();
        return true;
    }
    if (ops.targetSize() == 0) return error.InvalidStackLayout;

    if (!ops.isCompatible(source_top, source_top) or ops.targetIsArbitrary(source_top)) {
        for (0..@min(ops.sourceSize(), ops.targetSize())) |offset| {
            if (!ops.isCompatible(offset, offset) and
                !ops.sourceIsSame(offset, source_top) and
                ops.isCompatible(source_top, offset))
            {
                const depth = ops.sourceSize() - offset - 1;
                if (depth > ops.reachable_stack_depth) {
                    var swap_depth = ops.reachable_stack_depth;
                    while (swap_depth != 0) : (swap_depth -= 1) {
                        if (ops.sourceMultiplicity(ops.sourceSize() - 1 - swap_depth) < 0) {
                            try ops.swap(swap_depth);
                            if (ops.targetIsArbitrary(source_top)) try ops.pop();
                            return true;
                        }
                    }
                }
                try ops.swap(depth);
                return true;
            }
        }
    }

    if (ops.sourceSize() > ops.targetSize()) return error.InvalidStackLayout;
    for (0..ops.sourceSize()) |offset| {
        if (!ops.isCompatible(offset, offset) and
            ops.sourceMultiplicity(offset) < 0 and
            offset <= ops.targetSize() and
            !ops.targetIsArbitrary(offset))
        {
            if (!try dupDeepSlotIfRequired(ops) and !try bringUpTargetSlot(ops, offset))
                return error.InvalidStackLayout;
            return true;
        }
    }
    for (0..ops.sourceSize()) |index| if (ops.sourceMultiplicity(index) < 0)
        return error.InvalidStackLayout;
    if (ops.sourceSize() > ops.targetSize()) return error.InvalidStackLayout;

    if (!ops.isCompatible(source_top, source_top)) {
        for (0..ops.sourceSize()) |source_offset| {
            if (!ops.isCompatible(source_offset, source_offset) and
                ops.isCompatible(source_offset, source_top))
            {
                try ops.swap(ops.sourceSize() - source_offset - 1);
                return true;
            }
        }
    }
    if (ops.sourceSize() < ops.targetSize()) {
        if (!try dupDeepSlotIfRequired(ops) and !try bringUpTargetSlot(ops, ops.sourceSize()))
            return error.InvalidStackLayout;
        return true;
    }
    if (ops.sourceSize() != ops.targetSize()) return error.InvalidStackLayout;
    for (0..ops.sourceSize()) |index| {
        if (ops.sourceMultiplicity(index) != 0 or
            (!ops.targetIsArbitrary(index) and ops.targetMultiplicity(index) != 0))
            return error.InvalidStackLayout;
    }
    if (!ops.isCompatible(source_top, source_top)) return error.InvalidStackLayout;

    const size = ops.sourceSize();
    const start = if (size > ops.reachable_stack_depth + 1)
        size - (ops.reachable_stack_depth + 1)
    else
        0;
    var offset = start;
    while (offset < size) : (offset += 1) {
        if (!ops.isCompatible(offset, offset) and ops.isCompatible(source_top, offset)) {
            try ops.swap(size - offset - 1);
            return true;
        }
    }
    offset = start;
    while (offset < size) : (offset += 1) {
        if (!ops.isCompatible(offset, offset) and !ops.sourceIsSame(offset, source_top)) {
            try ops.swap(size - offset - 1);
            return true;
        }
    }
    if (ops.targetIsArbitrary(source_top) and ops.sourceMultiplicity(source_top) <= 0) {
        try ops.pop();
        return true;
    }
    offset = start;
    while (offset < size) : (offset += 1) {
        if (ops.targetIsArbitrary(offset) and ops.sourceMultiplicity(offset) <= 0) {
            try ops.swap(size - offset - 1);
            try ops.pop();
            return true;
        }
    }
    for (0..size) |deep_offset| {
        if (!ops.isCompatible(deep_offset, deep_offset) and ops.isCompatible(source_top, deep_offset)) {
            try ops.swap(size - deep_offset - 1);
            return true;
        }
    }
    for (0..size) |deep_offset| {
        if (!ops.isCompatible(deep_offset, deep_offset) and !ops.sourceIsSame(deep_offset, source_top)) {
            try ops.swap(size - deep_offset - 1);
            return true;
        }
    }
    return error.InvalidStackLayout;
}

/// `callbacks` must provide `swap(depth)`, `pushOrDup(slot)`, and `pop()`
/// methods returning an error union. `current_stack` is updated after every
/// callback, exactly like the upstream templated shuffler.
pub fn createStackLayout(
    allocator: std.mem.Allocator,
    current_stack: *CFG.Stack,
    target_stack: []const CFG.StackSlot,
    callbacks: anytype,
    reachable_stack_depth: usize,
) !void {
    if (reachable_stack_depth == 0) return error.InvalidReachableStackDepth;
    var ops = Operations(@TypeOf(callbacks)){
        .allocator = allocator,
        .current_stack = current_stack,
        .target_stack = target_stack,
        .callbacks = callbacks,
        .reachable_stack_depth = reachable_stack_depth,
    };
    try shuffleWithOperations(&ops);
    if (current_stack.items.len != target_stack.len) return error.InvalidStackLayout;
    for (current_stack.items, target_stack) |*current, target| {
        if (target == .junk)
            current.* = .{ .junk = .{} }
        else if (!current.eql(target))
            return error.InvalidStackLayout;
    }
}

/// Runs the generic shuffler against an operation object implementing the
/// interface documented by the upstream `ShuffleOperationConcept`.
pub fn shuffleWithOperations(ops: anytype) !void {
    var needs_more = true;
    var iteration_count: usize = 0;
    while (iteration_count < 1000 and needs_more) : (iteration_count += 1) {
        needs_more = try shuffleStep(ops);
    }
    if (needs_more) return error.StackShuffleIterationLimit;
}

test "stack shuffler creates exact layouts with duplication, swaps, pops, and junk" {
    const allocator = std.testing.allocator;
    const Callbacks = struct {
        operations: *std.ArrayList(u8),
        fn swap(self: @This(), _: usize) !void {
            try self.operations.append(std.testing.allocator, 'S');
        }
        fn pushOrDup(self: @This(), _: CFG.StackSlot) !void {
            try self.operations.append(std.testing.allocator, 'D');
        }
        fn pop(self: @This()) !void {
            try self.operations.append(std.testing.allocator, 'P');
        }
    };
    var current: CFG.Stack = .empty;
    defer current.deinit(allocator);
    try current.appendSlice(allocator, &.{
        .{ .literal = .{ .value = 1 } },
        .{ .literal = .{ .value = 2 } },
        .{ .literal = .{ .value = 3 } },
        .{ .literal = .{ .value = 9 } },
    });
    const target = [_]CFG.StackSlot{
        .{ .literal = .{ .value = 2 } },
        .{ .literal = .{ .value = 1 } },
        .{ .junk = .{} },
        .{ .literal = .{ .value = 2 } },
    };
    var operations: std.ArrayList(u8) = .empty;
    defer operations.deinit(allocator);
    try createStackLayout(allocator, &current, &target, Callbacks{ .operations = &operations }, 16);
    try std.testing.expectEqual(target.len, current.items.len);
    for (current.items, target) |actual, expected| try std.testing.expect(actual.eql(expected));
    try std.testing.expect(operations.items.len != 0);
}
