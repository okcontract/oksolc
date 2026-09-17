// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural, iterative translation of `libsolutil/TarjanSCC.h`.

const std = @import("std");
const cxx_compat = @import("cxx_compat");

pub const ComputeError = std.mem.Allocator.Error || error{
    GraphTooLarge,
    InvalidNodeIndex,
};

pub fn Components(comptime NodeID: type) type {
    return struct {
        const Self = @This();

        allocator: std.mem.Allocator,
        items: [][]NodeID,

        pub fn deinit(self: *Self) void {
            for (self.items) |component| self.allocator.free(component);
            self.allocator.free(self.items);
            self.* = undefined;
        }
    };
}

pub fn computeStronglyConnectedComponents(
    comptime NodeID: type,
    allocator: std.mem.Allocator,
    adjacency: []const []const NodeID,
) ComputeError!Components(NodeID) {
    comptime switch (@typeInfo(NodeID)) {
        .int => |integer| if (integer.signedness != .unsigned)
            @compileError("TarjanSCC node IDs must be unsigned integers"),
        else => @compileError("TarjanSCC node IDs must be unsigned integers"),
    };
    if (adjacency.len != 0 and
        @as(u128, adjacency.len - 1) > @as(u128, std.math.maxInt(NodeID)))
    {
        return error.GraphTooLarge;
    }
    for (adjacency) |successors| {
        for (successors) |successor| {
            if (@as(u128, successor) >= adjacency.len) return error.InvalidNodeIndex;
        }
    }

    const undefined_index = std.math.maxInt(usize);
    const Frame = struct { node: NodeID, child_index: usize };

    const discovery_index = try allocator.alloc(usize, adjacency.len);
    defer allocator.free(discovery_index);
    @memset(discovery_index, undefined_index);
    const lowlink = try allocator.alloc(usize, adjacency.len);
    defer allocator.free(lowlink);
    @memset(lowlink, 0);
    const on_stack = try allocator.alloc(bool, adjacency.len);
    defer allocator.free(on_stack);
    @memset(on_stack, false);

    var node_stack: cxx_compat.Vector(NodeID) = .{};
    defer node_stack.deinit(allocator);
    var work_stack: cxx_compat.Vector(Frame) = .{};
    defer work_stack.deinit(allocator);
    var components: cxx_compat.Vector([]NodeID) = .{};
    errdefer {
        for (components.items()) |component| allocator.free(component);
        components.deinit(allocator);
    }

    var next_index: usize = 0;
    for (0..adjacency.len) |root_index| {
        if (discovery_index[root_index] != undefined_index) continue;
        const root: NodeID = @intCast(root_index);
        try enter(
            NodeID,
            allocator,
            root,
            discovery_index,
            lowlink,
            on_stack,
            &node_stack,
            &work_stack,
            &next_index,
        );

        while (work_stack.len() != 0) {
            const frame = work_stack.last();
            const node = frame.node;
            const node_index: usize = @intCast(node);
            if (frame.child_index < adjacency[node_index].len) {
                const successor = adjacency[node_index][frame.child_index];
                frame.child_index += 1;
                const successor_index: usize = @intCast(successor);
                if (discovery_index[successor_index] == undefined_index) {
                    try enter(
                        NodeID,
                        allocator,
                        successor,
                        discovery_index,
                        lowlink,
                        on_stack,
                        &node_stack,
                        &work_stack,
                        &next_index,
                    );
                } else if (on_stack[successor_index]) {
                    lowlink[node_index] = @min(
                        lowlink[node_index],
                        discovery_index[successor_index],
                    );
                }
            } else {
                if (lowlink[node_index] == discovery_index[node_index]) {
                    var component: cxx_compat.Vector(NodeID) = .{};
                    errdefer component.deinit(allocator);
                    while (true) {
                        const member = node_stack.pop().?;
                        on_stack[@intCast(member)] = false;
                        try component.append(allocator, member);
                        if (member == node) break;
                    }
                    const owned = try component.toOwnedSlice(allocator);
                    errdefer allocator.free(owned);
                    try components.append(allocator, owned);
                }

                _ = work_stack.pop().?;
                if (work_stack.len() != 0) {
                    const parent_index: usize = @intCast(work_stack.last().node);
                    lowlink[parent_index] = @min(lowlink[parent_index], lowlink[node_index]);
                }
            }
        }
    }

    return .{
        .allocator = allocator,
        .items = try components.toOwnedSlice(allocator),
    };
}

fn enter(
    comptime NodeID: type,
    allocator: std.mem.Allocator,
    node: NodeID,
    discovery_index: []usize,
    lowlink: []usize,
    on_stack: []bool,
    node_stack: *cxx_compat.Vector(NodeID),
    work_stack: anytype,
    next_index: *usize,
) std.mem.Allocator.Error!void {
    const index: usize = @intCast(node);
    discovery_index[index] = next_index.*;
    lowlink[index] = next_index.*;
    next_index.* += 1;
    try node_stack.append(allocator, node);
    on_stack[index] = true;
    try work_stack.append(allocator, .{ .node = node, .child_index = 0 });
}

fn canonicalize(components: [][]u32) void {
    for (components) |component| std.sort.block(u32, component, {}, std.sort.asc(u32));
    std.sort.block([]u32, components, {}, struct {
        fn lessThan(_: void, lhs: []u32, rhs: []u32) bool {
            const length = @min(lhs.len, rhs.len);
            for (lhs[0..length], rhs[0..length]) |left, right| {
                if (left != right) return left < right;
            }
            return lhs.len < rhs.len;
        }
    }.lessThan);
}

fn expectPartition(
    adjacency: []const []const u32,
    expected: []const []const u32,
) !void {
    var actual = try computeStronglyConnectedComponents(
        u32,
        std.testing.allocator,
        adjacency,
    );
    defer actual.deinit();
    canonicalize(actual.items);
    try std.testing.expectEqual(expected.len, actual.items.len);
    for (expected, actual.items) |expected_component, actual_component| {
        try std.testing.expectEqualSlices(u32, expected_component, actual_component);
    }
}

test "partitions match the upstream Tarjan corpus" {
    try expectPartition(&.{}, &.{});
    try expectPartition(&.{&.{}}, &.{&.{0}});
    try expectPartition(&.{&.{0}}, &.{&.{0}});
    try expectPartition(&.{ &.{1}, &.{0} }, &.{&.{ 0, 1 }});
    try expectPartition(
        &.{ &.{1}, &.{ 2, 4, 5 }, &.{ 3, 6 }, &.{ 2, 7 }, &.{ 0, 5 }, &.{6}, &.{ 5, 7 }, &.{7} },
        &.{ &.{ 0, 1, 4 }, &.{ 2, 3 }, &.{ 5, 6 }, &.{7} },
    );
    try expectPartition(
        &.{ &.{1}, &.{ 0, 2 }, &.{3}, &.{2} },
        &.{ &.{ 0, 1 }, &.{ 2, 3 } },
    );
}

fn allocationFailureCase(allocator: std.mem.Allocator) !void {
    var result = try computeStronglyConnectedComponents(
        u32,
        allocator,
        &.{ &.{1}, &.{2}, &.{0} },
    );
    defer result.deinit();
}

test "Tarjan allocation failures release all partial state" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        allocationFailureCase,
        .{},
    );
}

test "invalid dense node IDs are rejected" {
    try std.testing.expectError(
        error.InvalidNodeIndex,
        computeStronglyConnectedComponents(u32, std.testing.allocator, &.{&.{1}}),
    );
}
