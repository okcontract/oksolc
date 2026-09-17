// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Contiguous union-find with path halving and the upstream representative
//! selection rules.

const std = @import("std");

pub fn ContiguousDisjointSet(comptime Value: type) type {
    const value_info = @typeInfo(Value);
    if (value_info != .int or value_info.int.signedness != .unsigned) {
        @compileError("ContiguousDisjointSet requires an unsigned integer value type");
    }
    return struct {
        const Self = @This();

        allocator: std.mem.Allocator,
        parents: []Value,
        neighbors: []Value,
        sizes: []Value,
        num_sets: usize,

        pub fn init(allocator: std.mem.Allocator, node_count: usize) !Self {
            if (node_count > std.math.maxInt(Value)) return error.TooManyNodes;
            const parents = try allocator.alloc(Value, node_count);
            errdefer allocator.free(parents);
            const neighbors = try allocator.alloc(Value, node_count);
            errdefer allocator.free(neighbors);
            const sizes = try allocator.alloc(Value, node_count);
            errdefer allocator.free(sizes);
            for (parents, neighbors, sizes, 0..) |*parent, *neighbor, *size, index| {
                parent.* = @intCast(index);
                neighbor.* = @intCast(index);
                size.* = 1;
            }
            return .{
                .allocator = allocator,
                .parents = parents,
                .neighbors = neighbors,
                .sizes = sizes,
                .num_sets = node_count,
            };
        }

        pub fn deinit(self: *Self) void {
            self.allocator.free(self.parents);
            self.allocator.free(self.neighbors);
            self.allocator.free(self.sizes);
            self.* = undefined;
        }

        pub fn numSets(self: *const Self) usize {
            return self.num_sets;
        }

        pub fn find(self: *Self, element: Value) Value {
            std.debug.assert(element < self.parents.len);
            var root = element;
            while (root != self.parents[root]) {
                self.parents[root] = self.parents[self.parents[root]];
                root = self.parents[root];
            }
            return root;
        }

        pub fn merge(self: *Self, x: Value, y: Value, merge_by_size: bool) void {
            var x_root = self.find(x);
            var y_root = self.find(y);
            if (x_root == y_root) return;
            if (merge_by_size and self.sizes[x_root] < self.sizes[y_root]) {
                std.mem.swap(Value, &x_root, &y_root);
            }
            self.parents[y_root] = x_root;
            self.sizes[x_root] += self.sizes[y_root];
            std.mem.swap(Value, &self.neighbors[x_root], &self.neighbors[y_root]);
            self.num_sets -= 1;
        }

        pub fn sameSubset(self: *Self, x: Value, y: Value) bool {
            return self.find(x) == self.find(y);
        }

        pub fn sizeOfSubset(self: *Self, x: Value) usize {
            return self.sizes[self.find(x)];
        }

        /// Returns members in the ascending order imposed by `std::set`.
        pub fn subsetAlloc(self: *Self, allocator: std.mem.Allocator, x: Value) ![]Value {
            const root = self.find(x);
            var result: std.ArrayList(Value) = .empty;
            errdefer result.deinit(allocator);
            for (0..self.parents.len) |index| {
                const value: Value = @intCast(index);
                if (self.find(value) == root) try result.append(allocator, value);
            }
            return result.toOwnedSlice(allocator);
        }

        pub fn subsetsAlloc(self: *Self, allocator: std.mem.Allocator) ![][]Value {
            var result: std.ArrayList([]Value) = .empty;
            errdefer {
                for (result.items) |subset| allocator.free(subset);
                result.deinit(allocator);
            }
            var emitted = try allocator.alloc(bool, self.parents.len);
            defer allocator.free(emitted);
            @memset(emitted, false);
            for (0..self.parents.len) |index| {
                const value: Value = @intCast(index);
                const root: usize = self.find(value);
                if (!emitted[root]) {
                    try result.append(allocator, try self.subsetAlloc(allocator, value));
                    emitted[root] = true;
                }
            }
            return result.toOwnedSlice(allocator);
        }
    };
}

test "disjoint set representatives, sizes, and ordered subsets" {
    var sets = try ContiguousDisjointSet(u32).init(std.testing.allocator, 6);
    defer sets.deinit();
    sets.merge(1, 2, true);
    sets.merge(4, 5, true);
    sets.merge(2, 5, true);
    try std.testing.expectEqual(@as(usize, 3), sets.numSets());
    try std.testing.expect(sets.sameSubset(1, 4));
    try std.testing.expectEqual(@as(usize, 4), sets.sizeOfSubset(2));
    const subset = try sets.subsetAlloc(std.testing.allocator, 5);
    defer std.testing.allocator.free(subset);
    try std.testing.expectEqualSlices(u32, &.{ 1, 2, 4, 5 }, subset);
}
