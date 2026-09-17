// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Graph traversal helpers translated from `Algorithms.h`.

const std = @import("std");

pub fn CycleDetector(comptime Vertex: type, comptime Context: type) type {
    return struct {
        const Self = @This();
        pub const Visitor = *const fn (*Context, *const Vertex, *Self, usize) anyerror!void;

        allocator: std.mem.Allocator,
        context: *Context,
        visitor: Visitor,
        processing: std.AutoHashMapUnmanaged(*const Vertex, void) = .empty,
        processed: std.AutoHashMapUnmanaged(*const Vertex, void) = .empty,
        depth: usize = 0,
        first_cycle_vertex: ?*const Vertex = null,

        pub fn init(
            allocator: std.mem.Allocator,
            context: *Context,
            visitor: Visitor,
        ) Self {
            return .{ .allocator = allocator, .context = context, .visitor = visitor };
        }

        pub fn deinit(self: *Self) void {
            self.processing.deinit(self.allocator);
            self.processed.deinit(self.allocator);
            self.* = undefined;
        }

        pub fn run(self: *Self, vertex: *const Vertex) anyerror!?*const Vertex {
            if (self.first_cycle_vertex != null) return self.first_cycle_vertex;
            if (self.processed.contains(vertex)) return null;
            if (self.processing.contains(vertex)) {
                self.first_cycle_vertex = vertex;
                return vertex;
            }
            try self.processing.put(self.allocator, vertex, {});
            errdefer _ = self.processing.remove(vertex);

            self.depth += 1;
            try self.visitor(self.context, vertex, self, self.depth);
            self.depth -= 1;
            if (self.first_cycle_vertex != null and self.depth == 1) {
                self.first_cycle_vertex = vertex;
            }

            _ = self.processing.remove(vertex);
            try self.processed.put(self.allocator, vertex, {});
            return self.first_cycle_vertex;
        }
    };
}

pub fn BreadthFirstSearch(comptime Vertex: type) type {
    return struct {
        const Self = @This();

        allocator: std.mem.Allocator,
        vertices_to_traverse: std.ArrayList(Vertex) = .empty,
        queue_head: usize = 0,
        visited_set: std.AutoHashMapUnmanaged(Vertex, void) = .empty,
        visited: std.ArrayList(Vertex) = .empty,

        pub fn init(allocator: std.mem.Allocator) Self {
            return .{ .allocator = allocator };
        }

        pub fn deinit(self: *Self) void {
            self.vertices_to_traverse.deinit(self.allocator);
            self.visited_set.deinit(self.allocator);
            self.visited.deinit(self.allocator);
            self.* = undefined;
        }

        pub fn add(self: *Self, vertex: Vertex) !void {
            try self.vertices_to_traverse.append(self.allocator, vertex);
        }

        pub fn abort(self: *Self) void {
            self.vertices_to_traverse.clearRetainingCapacity();
            self.queue_head = 0;
        }

        pub fn run(self: *Self, context: anytype, for_each_child: anytype) !void {
            while (self.queue_head < self.vertices_to_traverse.items.len) {
                const vertex = self.vertices_to_traverse.items[self.queue_head];
                self.queue_head += 1;
                const result = try self.visited_set.getOrPut(self.allocator, vertex);
                if (result.found_existing) continue;
                try self.visited.append(self.allocator, vertex);
                try for_each_child(context, vertex, self);
            }
        }
    };
}

test "breadth-first search visits each value once in queue order" {
    const Helpers = struct {
        fn children(_: void, vertex: u32, search: anytype) !void {
            if (vertex < 3) {
                try search.add(vertex + 1);
                try search.add(vertex + 1);
            }
        }
    };
    var search = BreadthFirstSearch(u32).init(std.testing.allocator);
    defer search.deinit();
    try search.add(0);
    try search.run({}, Helpers.children);
    try std.testing.expectEqualSlices(u32, &.{ 0, 1, 2, 3 }, search.visited.items);
}
