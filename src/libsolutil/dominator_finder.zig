// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Lengauer-Tarjan dominator analysis translated from `DominatorFinder.h`.

const std = @import("std");

pub fn DominatorFinder(
    comptime Vertex: type,
    comptime VertexId: type,
    comptime Context: type,
) type {
    return struct {
        const Self = @This();
        pub const DfsIndex = usize;
        pub const ForEachSuccessor = *const fn (
            *Context,
            *const Vertex,
            *const fn (*anyopaque, *const Vertex) anyerror!void,
            *anyopaque,
        ) anyerror!void;

        allocator: std.mem.Allocator,
        context: *Context,
        for_each_successor: ForEachSuccessor,
        vertices: std.ArrayList(VertexId) = .empty,
        dfs_indices: std.AutoHashMapUnmanaged(VertexId, DfsIndex) = .empty,
        immediate_dominators: std.ArrayList(?DfsIndex) = .empty,
        dominator_children: std.ArrayList(std.ArrayList(VertexId)) = .empty,
        predecessors: std.ArrayList(std.ArrayList(DfsIndex)) = .empty,

        pub fn init(
            allocator: std.mem.Allocator,
            entry: *const Vertex,
            context: *Context,
            for_each_successor: ForEachSuccessor,
        ) anyerror!Self {
            var self: Self = .{
                .allocator = allocator,
                .context = context,
                .for_each_successor = for_each_successor,
            };
            errdefer self.deinit();
            try self.findDominators(entry);
            try self.buildDominatorTree();
            return self;
        }

        pub fn deinit(self: *Self) void {
            for (self.predecessors.items) |*list| list.deinit(self.allocator);
            self.predecessors.deinit(self.allocator);
            for (self.dominator_children.items) |*list| list.deinit(self.allocator);
            self.dominator_children.deinit(self.allocator);
            self.immediate_dominators.deinit(self.allocator);
            self.dfs_indices.deinit(self.allocator);
            self.vertices.deinit(self.allocator);
            self.* = undefined;
        }

        pub fn verticesIdsInDFSOrder(self: *const Self) []const VertexId {
            return self.vertices.items;
        }

        pub fn dfsIndexById(self: *const Self, id: VertexId) ?DfsIndex {
            return self.dfs_indices.get(id);
        }

        pub fn immediateDominatorsByDfsIndex(self: *const Self) []const ?DfsIndex {
            return self.immediate_dominators.items;
        }

        pub fn immediateDominator(self: *const Self, id: VertexId) ?VertexId {
            const index = self.dfs_indices.get(id) orelse return null;
            const dominator_index = self.immediate_dominators.items[index] orelse return null;
            return self.vertices.items[dominator_index];
        }

        pub fn dominatorTreeChildren(self: *const Self, id: VertexId) []const VertexId {
            const index = self.dfs_indices.get(id) orelse return &.{};
            return self.dominator_children.items[index].items;
        }

        pub fn dominates(self: *const Self, dominator_id: VertexId, dominated_id: VertexId) bool {
            const dominator_index = self.dfs_indices.get(dominator_id) orelse return false;
            var dominated_index = self.dfs_indices.get(dominated_id) orelse return false;
            if (dominator_index == dominated_index) return true;
            while (dominated_index != 0) {
                dominated_index = self.immediate_dominators.items[dominated_index] orelse 0;
                if (dominated_index == dominator_index) return true;
            }
            return dominator_index == 0;
        }

        /// Returns immediate-to-root order and omits the vertex itself.
        pub fn dominatorsOfAlloc(
            self: *const Self,
            allocator: std.mem.Allocator,
            id: VertexId,
        ) std.mem.Allocator.Error![]VertexId {
            var index = self.dfs_indices.get(id) orelse return allocator.alloc(VertexId, 0);
            var result: std.ArrayList(VertexId) = .empty;
            errdefer result.deinit(allocator);
            if (index == 0) return result.toOwnedSlice(allocator);
            index = self.immediate_dominators.items[index] orelse 0;
            while (index != 0) {
                try result.append(allocator, self.vertices.items[index]);
                index = self.immediate_dominators.items[index].?;
            }
            try result.append(allocator, self.vertices.items[0]);
            return result.toOwnedSlice(allocator);
        }

        fn appendPredecessor(list: *std.ArrayList(DfsIndex), allocator: std.mem.Allocator, value: DfsIndex) !void {
            for (list.items) |existing| if (existing == value) return;
            try list.append(allocator, value);
        }

        fn walkKnown(self: *Self, vertex: *const Vertex, parent: *std.ArrayList(DfsIndex)) anyerror!void {
            const current_index = self.dfs_indices.get(vertex.id).?;
            const WalkState = struct {
                finder: *Self,
                parent: *std.ArrayList(DfsIndex),
                source_index: DfsIndex,

                fn call(raw: *anyopaque, successor: *const Vertex) anyerror!void {
                    const state: *@This() = @ptrCast(@alignCast(raw));
                    if (state.finder.dfs_indices.get(successor.id)) |successor_index| {
                        try appendPredecessor(
                            &state.finder.predecessors.items[successor_index],
                            state.finder.allocator,
                            state.source_index,
                        );
                        return;
                    }

                    try state.parent.append(state.finder.allocator, state.source_index);
                    const next_index = state.finder.vertices.items.len;
                    try state.finder.vertices.append(state.finder.allocator, successor.id);
                    try state.finder.dfs_indices.put(state.finder.allocator, successor.id, next_index);
                    var predecessors: std.ArrayList(DfsIndex) = .empty;
                    errdefer predecessors.deinit(state.finder.allocator);
                    try predecessors.append(state.finder.allocator, state.source_index);
                    try state.finder.predecessors.append(state.finder.allocator, predecessors);
                    predecessors = .empty;
                    try state.finder.walkKnown(successor, state.parent);
                }
            };
            var state: WalkState = .{ .finder = self, .parent = parent, .source_index = current_index };
            try self.for_each_successor(self.context, vertex, WalkState.call, &state);
        }

        fn findDominators(self: *Self, entry: *const Vertex) anyerror!void {
            var parent: std.ArrayList(DfsIndex) = .empty;
            defer parent.deinit(self.allocator);
            try parent.append(self.allocator, std.math.maxInt(DfsIndex));

            const entry_index: DfsIndex = 0;
            try self.vertices.append(self.allocator, entry.id);
            try self.dfs_indices.put(self.allocator, entry.id, entry_index);
            try self.predecessors.append(self.allocator, .empty);
            try self.walkKnown(entry, &parent);

            const count = self.vertices.items.len;
            std.debug.assert(parent.items.len == count);
            var ancestor = try self.allocator.alloc(DfsIndex, count);
            defer self.allocator.free(ancestor);
            @memset(ancestor, std.math.maxInt(DfsIndex));
            const label = try self.allocator.alloc(DfsIndex, count);
            defer self.allocator.free(label);
            const semi = try self.allocator.alloc(DfsIndex, count);
            defer self.allocator.free(semi);
            var buckets = try self.allocator.alloc(std.ArrayList(DfsIndex), count);
            defer {
                for (buckets) |*bucket| bucket.deinit(self.allocator);
                self.allocator.free(buckets);
            }
            for (0..count) |index| {
                label[index] = index;
                semi[index] = index;
                buckets[index] = .empty;
                try self.immediate_dominators.append(self.allocator, null);
            }

            var reverse = count;
            while (reverse != 0) {
                reverse -= 1;
                const w = reverse;
                for (buckets[w].items) |vertex_index| {
                    const evaluated = compressAndEval(ancestor, label, semi, vertex_index);
                    self.immediate_dominators.items[vertex_index] = if (semi[evaluated] < semi[vertex_index])
                        evaluated
                    else
                        w;
                }
                for (self.predecessors.items[w].items) |predecessor| {
                    const evaluated = compressAndEval(ancestor, label, semi, predecessor);
                    if (semi[evaluated] < semi[w]) semi[w] = semi[evaluated];
                }
                try buckets[semi[w]].append(self.allocator, w);
                ancestor[w] = parent.items[w];
            }

            for (1..count) |w| {
                const immediate = self.immediate_dominators.items[w].?;
                if (immediate != semi[w]) {
                    self.immediate_dominators.items[w] = self.immediate_dominators.items[immediate];
                }
                std.debug.assert(self.immediate_dominators.items[w].? < w);
            }
        }

        fn compressAndEval(
            ancestor: []DfsIndex,
            label: []DfsIndex,
            semi: []const DfsIndex,
            vertex: DfsIndex,
        ) DfsIndex {
            if (ancestor[vertex] == std.math.maxInt(DfsIndex)) return vertex;
            compressPath(ancestor, label, semi, vertex);
            return label[vertex];
        }

        fn compressPath(
            ancestor: []DfsIndex,
            label: []DfsIndex,
            semi: []const DfsIndex,
            vertex: DfsIndex,
        ) void {
            const parent = ancestor[vertex];
            if (parent == std.math.maxInt(DfsIndex)) return;
            if (ancestor[parent] != std.math.maxInt(DfsIndex)) {
                compressPath(ancestor, label, semi, parent);
                if (semi[label[parent]] < semi[label[vertex]]) label[vertex] = label[parent];
                ancestor[vertex] = ancestor[parent];
            }
        }

        fn buildDominatorTree(self: *Self) std.mem.Allocator.Error!void {
            try self.dominator_children.resize(self.allocator, self.vertices.items.len);
            for (self.dominator_children.items) |*children| children.* = .empty;
            for (1..self.vertices.items.len) |dominated_index| {
                const dominator_index = self.immediate_dominators.items[dominated_index].?;
                try self.dominator_children.items[dominator_index].append(
                    self.allocator,
                    self.vertices.items[dominated_index],
                );
            }
        }
    };
}

test "diamond and loop dominators match the upstream relations" {
    const Vertex = struct {
        id: u32,
        successors: []const u32,
    };
    const Context = struct {
        vertices: []const Vertex,
    };
    const Helpers = struct {
        fn each(
            context: *Context,
            vertex: *const Vertex,
            visit: *const fn (*anyopaque, *const Vertex) anyerror!void,
            raw: *anyopaque,
        ) anyerror!void {
            for (vertex.successors) |successor| try visit(raw, &context.vertices[successor]);
        }
    };
    const vertices = [_]Vertex{
        .{ .id = 0, .successors = &.{ 1, 2 } },
        .{ .id = 1, .successors = &.{3} },
        .{ .id = 2, .successors = &.{3} },
        .{ .id = 3, .successors = &.{4} },
        .{ .id = 4, .successors = &.{3} },
    };
    var context: Context = .{ .vertices = &vertices };
    var finder = try DominatorFinder(Vertex, u32, Context).init(
        std.testing.allocator,
        &vertices[0],
        &context,
        Helpers.each,
    );
    defer finder.deinit();
    try std.testing.expectEqualSlices(u32, &.{ 0, 1, 3, 4, 2 }, finder.verticesIdsInDFSOrder());
    try std.testing.expect(finder.dominates(0, 4));
    try std.testing.expect(finder.dominates(3, 4));
    try std.testing.expect(!finder.dominates(1, 3));
    try std.testing.expectEqual(@as(?u32, 0), finder.immediateDominator(3));
}
