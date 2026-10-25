// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Phase-local memoization of resolved source dependencies. The revision owns
//! masks in the frozen graph's CSR edge order; this marker only borrows them.

const std = @import("std");
const builtin = @import("builtin");
const GraphModule = @import("source_graph.zig");
const SourceGraph = GraphModule.SourceGraph;
const SourceId = GraphModule.SourceId;
const Fingerprint = @import("semantic_fingerprint.zig");

pub const DependencyMaskMarker = struct {
    allocator: std.mem.Allocator,
    graph: *const SourceGraph,
    masks: []Fingerprint.DependencyMaskEntry,
    importer: ?SourceId = null,
    seen: std.bit_set.Dynamic,
    failed: std.bit_set.Dynamic,
    // Deterministic scaling assertions without production counter overhead.
    edge_visits: if (builtin.is_test) usize else void = if (builtin.is_test) 0 else {},

    /// Graph topology and mask keys must stay frozen until deinit. Only this
    /// marker may mutate categories, monotonically widening them to `.all`.
    pub fn init(
        allocator: std.mem.Allocator,
        graph: *const SourceGraph,
        masks: []Fingerprint.DependencyMaskEntry,
    ) !DependencyMaskMarker {
        std.debug.assert(masks.len == graph.edgeCount());
        var seen = try std.bit_set.Dynamic.initEmpty(allocator, graph.activeSourceCount());
        errdefer seen.deinit(allocator);
        return .{
            .allocator = allocator,
            .graph = graph,
            .masks = masks,
            .seen = seen,
            .failed = try .initEmpty(allocator, graph.activeSourceCount()),
        };
    }

    pub fn deinit(self: *DependencyMaskMarker) void {
        self.failed.deinit(self.allocator);
        self.seen.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn mark(self: *DependencyMaskMarker, importer: SourceId, referenced: SourceId) void {
        if (importer == referenced) return;
        const target_index = self.graph.activeIndex(referenced) orelse return;
        const source_index = self.graph.activeIndex(importer) orelse return;
        if (self.importer != importer) {
            self.seen.unsetAll();
            self.importer = importer;
        }
        // Each pair selects the same path in a frozen graph. Repeating its
        // writes only assigns `.all` again; categories never narrow here.
        if (self.seen.isSet(target_index)) return;
        self.seen.set(target_index);
        // Negative results belong to this target search. Key by source node,
        // not SCC: intra-SCC edges are skipped, so members can differ in their
        // reachable outgoing paths. Successful paths still perform every mask
        // write in the original deterministic traversal order.
        self.failed.unsetAll();
        if (self.markPath(source_index, self.graph.scc_by_active_index[target_index])) return;
        // Preserve the original active-but-unreachable fallback exactly.
        for (self.masks[self.graph.forward_offsets[source_index]..self.graph.forward_offsets[source_index + 1]]) |*entry|
            entry.categories = .all;
    }

    fn markPath(self: *DependencyMaskMarker, source_index: usize, target_scc: GraphModule.SourceSccId) bool {
        const source_scc = self.graph.scc_by_active_index[source_index];
        if (source_scc == target_scc) return true;
        if (self.failed.isSet(source_index)) return false;
        const begin = self.graph.forward_offsets[source_index];
        const end = self.graph.forward_offsets[source_index + 1];
        for (self.graph.forward_edges[begin..end], begin..) |imported, edge_index| {
            if (builtin.is_test) self.edge_visits += 1;
            const imported_index = self.graph.activeIndex(imported).?;
            if (self.graph.scc_by_active_index[imported_index] == source_scc) continue;
            if (!self.markPath(imported_index, target_scc)) continue;
            // initializeDependencyMasks uses the same sorted CSR edge order.
            const entry = &self.masks[edge_index];
            std.debug.assert(entry.importer == self.graph.active_ids[source_index]);
            std.debug.assert(entry.imported == imported);
            entry.categories = .all;
            return true;
        }
        self.failed.set(source_index);
        return false;
    }
};

/// Independent reference retaining the previous stable-ID traversal and
/// linear mask searches. This deliberately does not use CSR indices or memoization.
const Reference = struct {
    fn mark(graph: *const SourceGraph, masks: []Fingerprint.DependencyMaskEntry, importer: SourceId, target: SourceId) void {
        if (importer == target or path(graph, masks, importer, target)) return;
        if (!graph.isActive(target)) return;
        for (masks) |*entry| if (entry.importer == importer) {
            entry.categories = .all;
        };
    }

    fn path(graph: *const SourceGraph, masks: []Fingerprint.DependencyMaskEntry, current: SourceId, target: SourceId) bool {
        const current_scc = graph.sourceScc(current) orelse return false;
        const target_scc = graph.sourceScc(target) orelse return false;
        if (current_scc == target_scc) return true;
        for (graph.imports(current)) |imported| {
            if (graph.sourceScc(imported).? == current_scc) continue;
            if (!path(graph, masks, imported, target)) continue;
            for (masks) |*entry| if (entry.importer == current and entry.imported == imported) {
                entry.categories = .all;
                return true;
            };
            return false;
        }
        return false;
    }
};

fn masksAlloc(allocator: std.mem.Allocator, graph: *const SourceGraph) ![]Fingerprint.DependencyMaskEntry {
    const masks = try allocator.alloc(Fingerprint.DependencyMaskEntry, graph.edgeCount());
    var index: usize = 0;
    for (graph.activeSources()) |importer| for (graph.imports(importer)) |imported| {
        masks[index] = .{ .importer = importer, .imported = imported };
        index += 1;
    };
    return masks;
}

test "dependency mask marker matches reference after every query on all three-source graphs" {
    const allocator = std.testing.allocator;
    var registry = GraphModule.SourceRegistry.init(allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const ids = [_]SourceId{
        (try registry.upsert("a.sol", "")).id,
        (try registry.upsert("b.sol", "")).id,
        (try registry.upsert("c.sol", "")).id,
    };
    _ = try registry.finishRevision();
    registry.commitRevision();
    const unknown = SourceId.init(1000);
    for (0..512) |bits| {
        var edges: std.ArrayList(GraphModule.SourceEdge) = .empty;
        defer edges.deinit(allocator);
        for (ids, 0..) |from, i| for (ids, 0..) |to, j| {
            if (bits & (@as(usize, 1) << @intCast(i * 3 + j)) != 0)
                try edges.append(allocator, .{ .importer = from, .imported = to });
        };
        var graph = try SourceGraph.initAlloc(allocator, &registry, edges.items);
        defer graph.deinit();
        const actual = try masksAlloc(allocator, &graph);
        defer allocator.free(actual);
        const expected = try allocator.dupe(Fingerprint.DependencyMaskEntry, actual);
        defer allocator.free(expected);
        var marker = try DependencyMaskMarker.init(allocator, &graph, actual);
        defer marker.deinit();
        // Query each pair from an untouched mask set, then repeat it, visit
        // another importer, and return. Compare the full ordered masks each time.
        for (0..4) |from| for (0..4) |to| {
            for (actual) |*entry| entry.categories = .exported_only;
            for (expected) |*entry| entry.categories = .exported_only;
            marker.importer = null;
            const importer = if (from < 3) ids[from] else unknown;
            const target = if (to < 3) ids[to] else unknown;
            const queries = [_][2]SourceId{
                .{ importer, target },            .{ importer, target },
                .{ ids[(from + 1) % 3], target }, .{ importer, target },
            };
            for (queries) |query| {
                Reference.mark(&graph, expected, query[0], query[1]);
                marker.mark(query[0], query[1]);
                try std.testing.expectEqualDeep(expected, actual);
            }
        };
    }
}

test "dependency mask marker preserves the first diamond path with sparse source identities and OOM" {
    const allocator = std.testing.allocator;
    var registry = GraphModule.SourceRegistry.init(allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const tombstone = (try registry.upsert("removed.sol", "")).id;
    const a = (try registry.upsert("a.sol", "")).id;
    const b = (try registry.upsert("b.sol", "")).id;
    const c = (try registry.upsert("c.sol", "")).id;
    const d = (try registry.upsert("d.sol", "")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();
    _ = try registry.beginRevision();
    for ([_][]const u8{ "a.sol", "b.sol", "c.sol", "d.sol" }) |name| _ = try registry.upsert(name, "");
    _ = try registry.finishRevision();
    registry.commitRevision();
    var graph = try SourceGraph.initAlloc(allocator, &registry, &.{
        .{ .importer = c, .imported = d }, .{ .importer = a, .imported = c },
        .{ .importer = b, .imported = d }, .{ .importer = a, .imported = b },
    });
    defer graph.deinit();
    const Check = struct {
        fn run(failing: std.mem.Allocator, input: *const SourceGraph, from: SourceId, to: SourceId, inactive: SourceId) !void {
            const masks = try masksAlloc(failing, input);
            defer failing.free(masks);
            var marker = try DependencyMaskMarker.init(failing, input, masks);
            defer marker.deinit();
            try std.testing.expectEqual(@as(usize, 4), marker.seen.capacity());
            marker.mark(from, inactive);
            marker.mark(inactive, to);
            for (masks) |entry| try std.testing.expectEqual(Fingerprint.CategoryMask.exported_only, entry.categories);
            marker.mark(from, to);
            marker.mark(from, to);
            try std.testing.expectEqual(Fingerprint.CategoryMask.all, masks[0].categories);
            try std.testing.expectEqual(Fingerprint.CategoryMask.exported_only, masks[1].categories);
            try std.testing.expectEqual(Fingerprint.CategoryMask.all, masks[2].categories);
            try std.testing.expectEqual(Fingerprint.CategoryMask.exported_only, masks[3].categories);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ &graph, a, d, tombstone });
}

test "dependency mask marker visits shared unsuccessful subgraphs linearly" {
    const allocator = std.testing.allocator;
    for ([_]usize{ 4, 8, 12 }) |layers| {
        var registry = GraphModule.SourceRegistry.init(allocator);
        defer registry.deinit();
        _ = try registry.beginRevision();
        var ids: std.ArrayList(SourceId) = .empty;
        defer ids.deinit(allocator);
        for (0..2 * layers + 2) |i| {
            const name = try allocator.print("source-{d}.sol", .{i});
            defer allocator.free(name);
            try ids.append(allocator, (try registry.upsert(name, "")).id);
        }
        _ = try registry.finishRevision();
        registry.commitRevision();
        var edges: std.ArrayList(GraphModule.SourceEdge) = .empty;
        defer edges.deinit(allocator);
        for (ids.items[1..3]) |imported|
            try edges.append(allocator, .{ .importer = ids.items[0], .imported = imported });
        for (0..layers - 1) |layer| {
            for (ids.items[1 + 2 * layer ..][0..2]) |from|
                for (ids.items[3 + 2 * layer ..][0..2]) |to| {
                    try edges.append(allocator, .{ .importer = from, .imported = to });
                };
        }
        const target = ids.items[ids.items.len - 1];
        try edges.append(allocator, .{ .importer = ids.items[0], .imported = target });
        var graph = try SourceGraph.initAlloc(allocator, &registry, edges.items);
        defer graph.deinit();
        const masks = try masksAlloc(allocator, &graph);
        defer allocator.free(masks);
        var marker = try DependencyMaskMarker.init(allocator, &graph, masks);
        defer marker.deinit();
        marker.mark(ids.items[0], target);
        try std.testing.expect(marker.edge_visits <= graph.edgeCount());
        for (masks) |mask| {
            const expected: Fingerprint.CategoryMask = if (mask.imported == target) .all else .exported_only;
            try std.testing.expectEqual(expected, mask.categories);
        }
        const first_visits = marker.edge_visits;
        marker.mark(ids.items[0], target);
        try std.testing.expectEqual(first_visits, marker.edge_visits);
        // A different target must not inherit negative results from the first.
        marker.mark(ids.items[0], ids.items[ids.items.len - 2]);
        try std.testing.expect(marker.edge_visits - first_visits <= graph.edgeCount());
        try std.testing.expectEqual(Fingerprint.CategoryMask.all, masks[0].categories);
    }
}

test "dependency mask marker keeps negative results distinct within an SCC" {
    const allocator = std.testing.allocator;
    var registry = GraphModule.SourceRegistry.init(allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const root = (try registry.upsert("root.sol", "")).id;
    const a = (try registry.upsert("a.sol", "")).id;
    const b = (try registry.upsert("b.sol", "")).id;
    const target = (try registry.upsert("target.sol", "")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();
    var graph = try SourceGraph.initAlloc(allocator, &registry, &.{
        .{ .importer = root, .imported = a },
        .{ .importer = root, .imported = b },
        .{ .importer = a, .imported = b },
        .{ .importer = b, .imported = a },
        .{ .importer = b, .imported = target },
    });
    defer graph.deinit();
    const masks = try masksAlloc(allocator, &graph);
    defer allocator.free(masks);
    const expected = try allocator.dupe(Fingerprint.DependencyMaskEntry, masks);
    defer allocator.free(expected);
    var marker = try DependencyMaskMarker.init(allocator, &graph, masks);
    defer marker.deinit();
    Reference.mark(&graph, expected, root, target);
    marker.mark(root, target);
    try std.testing.expectEqualDeep(expected, masks);
    try std.testing.expectEqual(Fingerprint.CategoryMask.exported_only, masks[0].categories);
    try std.testing.expectEqual(Fingerprint.CategoryMask.all, masks[1].categories);
    try std.testing.expectEqual(Fingerprint.CategoryMask.all, masks[4].categories);
}
