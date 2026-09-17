// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic, compact dependency state for source revisions.
//!
//! Import edges are accumulated in any order and frozen into sorted,
//! deduplicated CSR adjacency in both directions. Stable source IDs may contain
//! tombstones, but adjacency and SCC storage use a compact active-index
//! projection so historical rename churn does not increase graph work.

const std = @import("std");
const SourceRegistryModule = @import("source_registry.zig");
const SemanticFingerprint = @import("semantic_fingerprint.zig");
const TarjanSCC = @import("../libsolutil/tarjan_scc.zig");

pub const SourceId = SourceRegistryModule.SourceId;
pub const SourceRegistry = SourceRegistryModule.SourceRegistry;

pub const SourceEdge = struct {
    importer: SourceId,
    imported: SourceId,

    fn eql(left: SourceEdge, right: SourceEdge) bool {
        return left.importer == right.importer and left.imported == right.imported;
    }
};

pub const SourceSccId = enum(u32) {
    _,

    pub fn init(raw_index: u32) SourceSccId {
        return @enumFromInt(raw_index);
    }

    pub fn index(self: SourceSccId) u32 {
        return @intFromEnum(self);
    }
};

pub const BuildError = std.mem.Allocator.Error || TarjanSCC.ComputeError || error{
    InactiveSource,
    SourceSccOverflow,
    UnknownSource,
};

pub const SourceGraph = struct {
    allocator: std.mem.Allocator,
    source_id_capacity: usize,
    active_ids: []SourceId,
    active_indices: std.AutoHashMapUnmanaged(SourceId, u32),
    forward_offsets: []usize,
    forward_edges: []SourceId,
    reverse_offsets: []usize,
    reverse_edges: []SourceId,
    scc_by_active_index: []SourceSccId,
    scc_offsets: []usize,
    scc_members: []SourceId,

    pub fn initAlloc(
        allocator: std.mem.Allocator,
        registry: *const SourceRegistry,
        edges: []const SourceEdge,
    ) BuildError!SourceGraph {
        const source_id_capacity = registry.knownCount();
        const active_ids = try allocator.dupe(SourceId, registry.activeIds());
        errdefer allocator.free(active_ids);
        std.mem.sort(SourceId, active_ids, {}, lessSourceId);
        const active_count = std.math.cast(u32, active_ids.len) orelse
            return error.SourceSccOverflow;
        var active_indices: std.AutoHashMapUnmanaged(SourceId, u32) = .empty;
        errdefer active_indices.deinit(allocator);
        try active_indices.ensureTotalCapacity(allocator, active_count);
        for (active_ids, 0..) |source, active_index|
            active_indices.putAssumeCapacityNoClobber(source, @intCast(active_index));

        const sorted_edges = try allocator.dupe(SourceEdge, edges);
        defer allocator.free(sorted_edges);
        for (sorted_edges) |edge| {
            const importer_index: usize = @intCast(edge.importer.index());
            const imported_index: usize = @intCast(edge.imported.index());
            if (importer_index >= source_id_capacity or
                imported_index >= source_id_capacity)
                return error.UnknownSource;
            if (!active_indices.contains(edge.importer) or
                !active_indices.contains(edge.imported))
                return error.InactiveSource;
        }
        std.mem.sort(SourceEdge, sorted_edges, {}, lessForward);

        const unique_edge_count = countUniqueEdges(sorted_edges);
        const forward_offsets = try allocator.alloc(usize, active_ids.len + 1);
        errdefer allocator.free(forward_offsets);
        @memset(forward_offsets, 0);
        const forward_edges = try allocator.alloc(SourceId, unique_edge_count);
        errdefer allocator.free(forward_edges);
        freezeForward(sorted_edges, &active_indices, forward_offsets, forward_edges);

        std.mem.sort(SourceEdge, sorted_edges, {}, lessReverse);
        const reverse_offsets = try allocator.alloc(usize, active_ids.len + 1);
        errdefer allocator.free(reverse_offsets);
        @memset(reverse_offsets, 0);
        const reverse_edges = try allocator.alloc(SourceId, unique_edge_count);
        errdefer allocator.free(reverse_edges);
        freezeReverse(sorted_edges, &active_indices, reverse_offsets, reverse_edges);

        const scc_state = try computeSccsAlloc(
            allocator,
            active_ids,
            &active_indices,
            forward_offsets,
            forward_edges,
        );
        errdefer {
            allocator.free(scc_state.members);
            allocator.free(scc_state.offsets);
            allocator.free(scc_state.by_active_index);
        }

        return .{
            .allocator = allocator,
            .source_id_capacity = source_id_capacity,
            .active_ids = active_ids,
            .active_indices = active_indices,
            .forward_offsets = forward_offsets,
            .forward_edges = forward_edges,
            .reverse_offsets = reverse_offsets,
            .reverse_edges = reverse_edges,
            .scc_by_active_index = scc_state.by_active_index,
            .scc_offsets = scc_state.offsets,
            .scc_members = scc_state.members,
        };
    }

    pub fn deinit(self: *SourceGraph) void {
        self.allocator.free(self.scc_members);
        self.allocator.free(self.scc_offsets);
        self.allocator.free(self.scc_by_active_index);
        self.allocator.free(self.reverse_edges);
        self.allocator.free(self.reverse_offsets);
        self.allocator.free(self.forward_edges);
        self.allocator.free(self.forward_offsets);
        self.active_indices.deinit(self.allocator);
        self.allocator.free(self.active_ids);
        self.* = undefined;
    }

    pub fn sourceCapacity(self: *const SourceGraph) usize {
        return self.source_id_capacity;
    }

    pub fn activeSourceCount(self: *const SourceGraph) usize {
        return self.active_ids.len;
    }

    pub fn storageNodeCount(self: *const SourceGraph) usize {
        return self.active_ids.len;
    }

    pub fn edgeCount(self: *const SourceGraph) usize {
        return self.forward_edges.len;
    }

    /// Active stable IDs in ascending order.
    pub fn activeSources(self: *const SourceGraph) []const SourceId {
        return self.active_ids;
    }

    pub fn isActive(self: *const SourceGraph, source: SourceId) bool {
        return self.active_indices.contains(source);
    }

    pub fn activeIndex(self: *const SourceGraph, source: SourceId) ?usize {
        return @intCast(self.active_indices.get(source) orelse return null);
    }

    /// Sources imported directly by `source`, sorted by stable source ID.
    pub fn imports(self: *const SourceGraph, source: SourceId) []const SourceId {
        const index = self.activeIndex(source) orelse return &.{};
        return self.forward_edges[self.forward_offsets[index]..self.forward_offsets[index + 1]];
    }

    /// Sources that directly import `source`, sorted by stable source ID.
    pub fn importers(self: *const SourceGraph, source: SourceId) []const SourceId {
        const index = self.activeIndex(source) orelse return &.{};
        return self.reverse_edges[self.reverse_offsets[index]..self.reverse_offsets[index + 1]];
    }

    pub fn sourceScc(self: *const SourceGraph, source: SourceId) ?SourceSccId {
        const index = self.activeIndex(source) orelse return null;
        return self.scc_by_active_index[index];
    }

    pub fn sccCount(self: *const SourceGraph) usize {
        return self.scc_offsets.len - 1;
    }

    /// SCC members are sorted by stable source ID. SCC IDs are assigned by the
    /// lexicographic order of those member lists.
    pub fn sccMembers(self: *const SourceGraph, scc: SourceSccId) []const SourceId {
        const index: usize = @intCast(scc.index());
        if (index >= self.sccCount()) return &.{};
        return self.scc_members[self.scc_offsets[index]..self.scc_offsets[index + 1]];
    }
};

const SccState = struct {
    by_active_index: []SourceSccId,
    offsets: []usize,
    members: []SourceId,
};

fn computeSccsAlloc(
    allocator: std.mem.Allocator,
    active_ids: []const SourceId,
    active_indices: *const std.AutoHashMapUnmanaged(SourceId, u32),
    forward_offsets: []const usize,
    forward_edges: []const SourceId,
) BuildError!SccState {
    const tarjan_edges = try allocator.alloc(u32, forward_edges.len);
    defer allocator.free(tarjan_edges);
    for (forward_edges, tarjan_edges) |source, *raw|
        raw.* = active_indices.get(source).?;

    const adjacency = try allocator.alloc([]const u32, active_ids.len);
    defer allocator.free(adjacency);
    for (adjacency, 0..) |*neighbors, source_index|
        neighbors.* = tarjan_edges[forward_offsets[source_index]..forward_offsets[source_index + 1]];

    var components = try TarjanSCC.computeStronglyConnectedComponents(
        u32,
        allocator,
        adjacency,
    );
    defer components.deinit();
    for (components.items) |component|
        std.mem.sort(u32, component, {}, std.sort.asc(u32));
    std.mem.sort([]u32, components.items, {}, lessComponent);

    if (components.items.len > std.math.maxInt(u32))
        return error.SourceSccOverflow;

    const by_active_index = try allocator.alloc(SourceSccId, active_ids.len);
    errdefer allocator.free(by_active_index);
    const offsets = try allocator.alloc(usize, components.items.len + 1);
    errdefer allocator.free(offsets);
    const members = try allocator.alloc(SourceId, active_ids.len);
    errdefer allocator.free(members);

    var component_index: usize = 0;
    var member_index: usize = 0;
    offsets[0] = 0;
    for (components.items) |component| {
        const scc = SourceSccId.init(@intCast(component_index));
        for (component) |active_index| {
            const source = active_ids[active_index];
            by_active_index[active_index] = scc;
            members[member_index] = source;
            member_index += 1;
        }
        component_index += 1;
        offsets[component_index] = member_index;
    }
    std.debug.assert(component_index == components.items.len);
    std.debug.assert(member_index == members.len);
    return .{
        .by_active_index = by_active_index,
        .offsets = offsets,
        .members = members,
    };
}

fn countUniqueEdges(sorted_edges: []const SourceEdge) usize {
    var count: usize = 0;
    var previous: ?SourceEdge = null;
    for (sorted_edges) |edge| {
        if (previous) |value| if (SourceEdge.eql(value, edge)) continue;
        count += 1;
        previous = edge;
    }
    return count;
}

fn freezeForward(
    sorted_edges: []const SourceEdge,
    active_indices: *const std.AutoHashMapUnmanaged(SourceId, u32),
    offsets: []usize,
    frozen_edges: []SourceId,
) void {
    var edge_index: usize = 0;
    var previous: ?SourceEdge = null;
    for (sorted_edges) |edge| {
        if (previous) |value| if (SourceEdge.eql(value, edge)) continue;
        offsets[@as(usize, @intCast(active_indices.get(edge.importer).?)) + 1] += 1;
        frozen_edges[edge_index] = edge.imported;
        edge_index += 1;
        previous = edge;
    }
    prefixSum(offsets);
    std.debug.assert(edge_index == frozen_edges.len);
}

fn freezeReverse(
    sorted_edges: []const SourceEdge,
    active_indices: *const std.AutoHashMapUnmanaged(SourceId, u32),
    offsets: []usize,
    frozen_edges: []SourceId,
) void {
    var edge_index: usize = 0;
    var previous: ?SourceEdge = null;
    for (sorted_edges) |edge| {
        if (previous) |value| if (SourceEdge.eql(value, edge)) continue;
        offsets[@as(usize, @intCast(active_indices.get(edge.imported).?)) + 1] += 1;
        frozen_edges[edge_index] = edge.importer;
        edge_index += 1;
        previous = edge;
    }
    prefixSum(offsets);
    std.debug.assert(edge_index == frozen_edges.len);
}

fn prefixSum(offsets: []usize) void {
    for (offsets[1..], 1..) |*offset, index| offset.* += offsets[index - 1];
}

fn lessForward(_: void, left: SourceEdge, right: SourceEdge) bool {
    if (left.importer != right.importer)
        return left.importer.index() < right.importer.index();
    return left.imported.index() < right.imported.index();
}

fn lessReverse(_: void, left: SourceEdge, right: SourceEdge) bool {
    if (left.imported != right.imported)
        return left.imported.index() < right.imported.index();
    return left.importer.index() < right.importer.index();
}

fn lessComponent(_: void, left: []u32, right: []u32) bool {
    const shared_length = @min(left.len, right.len);
    for (left[0..shared_length], right[0..shared_length]) |left_id, right_id| {
        if (left_id != right_id) return left_id < right_id;
    }
    return left.len < right.len;
}

fn lessSourceId(_: void, left: SourceId, right: SourceId) bool {
    return left.index() < right.index();
}

/// Revision-local dirty membership with O(dirty) epoch changes and a dense
/// bitset for constant-time membership and deterministic ascending snapshots.
pub const DirtySourceSet = struct {
    allocator: std.mem.Allocator,
    bits: std.DynamicBitSetUnmanaged,
    epochs: []u64,
    members: std.ArrayList(SourceId) = .empty,
    epoch: u64 = 1,
    source_count: usize,

    pub fn init(
        allocator: std.mem.Allocator,
        source_count: usize,
    ) std.mem.Allocator.Error!DirtySourceSet {
        var bits = try std.DynamicBitSetUnmanaged.initEmpty(allocator, source_count);
        errdefer bits.deinit(allocator);
        const epochs = try allocator.alloc(u64, source_count);
        @memset(epochs, 0);
        return .{
            .allocator = allocator,
            .bits = bits,
            .epochs = epochs,
            .source_count = source_count,
        };
    }

    pub fn deinit(self: *DirtySourceSet) void {
        self.members.deinit(self.allocator);
        self.allocator.free(self.epochs);
        self.bits.deinit(self.allocator);
        self.* = undefined;
    }

    /// Stable source IDs only grow. If either allocation fails, the previous
    /// logical capacity remains usable and a later call can resume the growth.
    pub fn ensureSourceCapacity(
        self: *DirtySourceSet,
        source_count: usize,
    ) std.mem.Allocator.Error!void {
        if (source_count <= self.source_count) return;
        if (source_count > self.epochs.len) {
            const previous_length = self.epochs.len;
            self.epochs = try self.allocator.realloc(self.epochs, source_count);
            @memset(self.epochs[previous_length..], 0);
        }
        if (source_count > self.bits.capacity())
            try self.bits.resize(self.allocator, source_count, false);
        self.source_count = source_count;
    }

    /// Starts a new logical dirty epoch without clearing all dense storage.
    pub fn beginEpoch(self: *DirtySourceSet) void {
        for (self.members.items) |source|
            self.bits.unset(@intCast(source.index()));
        self.members.clearRetainingCapacity();
        if (self.epoch == std.math.maxInt(u64)) {
            @memset(self.epochs, 0);
            self.epoch = 1;
        } else {
            self.epoch += 1;
        }
    }

    pub fn contains(self: *const DirtySourceSet, source: SourceId) bool {
        const index: usize = @intCast(source.index());
        return index < self.source_count and self.epochs[index] == self.epoch;
    }

    pub fn count(self: *const DirtySourceSet) usize {
        return self.members.items.len;
    }

    pub fn mark(
        self: *DirtySourceSet,
        graph: *const SourceGraph,
        source: SourceId,
    ) (std.mem.Allocator.Error || error{InactiveSource})!bool {
        if (!graph.isActive(source)) return error.InactiveSource;
        try self.ensureSourceCapacity(graph.sourceCapacity());
        return self.markKnown(source);
    }

    /// Marks every active source without traversing edges. This is the
    /// conservative invalidation path for settings that affect the frontend.
    pub fn markAll(
        self: *DirtySourceSet,
        graph: *const SourceGraph,
    ) std.mem.Allocator.Error!void {
        try self.ensureSourceCapacity(graph.sourceCapacity());
        try self.members.ensureUnusedCapacity(self.allocator, graph.active_ids.len);
        for (graph.active_ids) |source| {
            const index: usize = @intCast(source.index());
            if (self.epochs[index] == self.epoch) continue;
            self.members.appendAssumeCapacity(source);
            self.epochs[index] = self.epoch;
            self.bits.set(index);
        }
    }

    /// Marks changed sources and every reverse-transitive importer. Cycles are
    /// naturally collapsed by membership checks and agree with source SCCs.
    pub fn markReverseClosure(
        self: *DirtySourceSet,
        graph: *const SourceGraph,
        changed: []const SourceId,
    ) (std.mem.Allocator.Error || error{InactiveSource})!void {
        try self.ensureSourceCapacity(graph.sourceCapacity());
        for (changed) |source|
            if (!graph.isActive(source)) return error.InactiveSource;
        for (changed) |source| _ = try self.markKnown(source);

        var cursor: usize = 0;
        while (cursor < self.members.items.len) : (cursor += 1) {
            const source = self.members.items[cursor];
            for (graph.importers(source)) |importer|
                _ = try self.markKnown(importer);
        }
    }

    pub const ChangedSource = struct {
        source: SourceId,
        categories: SemanticFingerprint.CategoryMask,
    };

    /// Marks changed SCCs atomically and follows only dependency edges whose
    /// recorded consumption categories intersect the changed surface. Once an
    /// importer is invalidated, every category is propagated onward because
    /// its derived semantic surfaces are not known until analysis completes.
    pub fn markSelectiveClosure(
        self: *DirtySourceSet,
        graph: *const SourceGraph,
        changed: []const ChangedSource,
        dependency_masks: []const SemanticFingerprint.DependencyMaskEntry,
    ) (std.mem.Allocator.Error || error{InactiveSource})!void {
        try self.ensureSourceCapacity(graph.sourceCapacity());
        const seen = try self.allocator.alloc(
            SemanticFingerprint.CategoryMask,
            graph.sourceCapacity(),
        );
        defer self.allocator.free(seen);
        @memset(seen, SemanticFingerprint.CategoryMask.none);
        const propagated = try self.allocator.alloc(
            SemanticFingerprint.CategoryMask,
            graph.sourceCapacity(),
        );
        defer self.allocator.free(propagated);
        @memset(propagated, SemanticFingerprint.CategoryMask.none);
        var queue: std.ArrayList(SourceId) = .empty;
        defer queue.deinit(self.allocator);

        for (changed) |seed| {
            if (!graph.isActive(seed.source)) return error.InactiveSource;
            try self.enqueueScc(
                graph,
                seed.source,
                seed.categories,
                seen,
                &queue,
            );
        }

        var cursor: usize = 0;
        while (cursor < queue.items.len) : (cursor += 1) {
            const source = queue.items[cursor];
            const index: usize = @intCast(source.index());
            const pending: SemanticFingerprint.CategoryMask = .{
                .bits = seen[index].bits & ~propagated[index].bits,
            };
            if (pending.bits == 0) continue;
            _ = propagated[index].merge(pending);
            for (graph.importers(source)) |importer| {
                const consumed = SemanticFingerprint.dependencyMask(
                    dependency_masks,
                    importer,
                    source,
                );
                if (!pending.intersects(consumed)) continue;
                try self.enqueueScc(
                    graph,
                    importer,
                    .all,
                    seen,
                    &queue,
                );
            }
        }
    }

    pub fn sortedIdsAlloc(
        self: *const DirtySourceSet,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]SourceId {
        const result = try allocator.alloc(SourceId, self.bits.count());
        var iterator = self.bits.iterator(.{});
        var index: usize = 0;
        while (iterator.next()) |source_index| : (index += 1)
            result[index] = SourceId.init(@intCast(source_index));
        std.debug.assert(index == result.len);
        return result;
    }

    fn markKnown(self: *DirtySourceSet, source: SourceId) std.mem.Allocator.Error!bool {
        const index: usize = @intCast(source.index());
        std.debug.assert(index < self.source_count);
        if (self.epochs[index] == self.epoch) return false;
        try self.members.append(self.allocator, source);
        self.epochs[index] = self.epoch;
        self.bits.set(index);
        return true;
    }

    fn enqueueScc(
        self: *DirtySourceSet,
        graph: *const SourceGraph,
        source: SourceId,
        categories: SemanticFingerprint.CategoryMask,
        seen: []SemanticFingerprint.CategoryMask,
        queue: *std.ArrayList(SourceId),
    ) std.mem.Allocator.Error!void {
        const scc = graph.sourceScc(source).?;
        const members = graph.sccMembers(scc);
        const propagated_categories = if (members.len > 1)
            SemanticFingerprint.CategoryMask.all
        else
            categories;
        for (members) |member| {
            _ = try self.markKnown(member);
            const index: usize = @intCast(member.index());
            if (seen[index].merge(propagated_categories))
                try queue.append(self.allocator, member);
        }
    }
};

test "source graph freezes sorted bidirectional adjacency and deterministic SCCs" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const a = (try registry.upsert("A.sol", "a")).id;
    const b = (try registry.upsert("B.sol", "b")).id;
    const c = (try registry.upsert("C.sol", "c")).id;
    const d = (try registry.upsert("D.sol", "d")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();

    var graph = try SourceGraph.initAlloc(std.testing.allocator, &registry, &.{
        .{ .importer = c, .imported = b },
        .{ .importer = b, .imported = a },
        .{ .importer = a, .imported = b },
        .{ .importer = d, .imported = d },
        .{ .importer = c, .imported = a },
        .{ .importer = c, .imported = b },
    });
    defer graph.deinit();

    try std.testing.expectEqual(@as(usize, 5), graph.edgeCount());
    try std.testing.expectEqualSlices(SourceId, &.{b}, graph.imports(a));
    try std.testing.expectEqualSlices(SourceId, &.{a}, graph.imports(b));
    try std.testing.expectEqualSlices(SourceId, &.{ a, b }, graph.imports(c));
    try std.testing.expectEqualSlices(SourceId, &.{ a, c }, graph.importers(b));
    try std.testing.expectEqual(@as(usize, 3), graph.sccCount());
    try std.testing.expectEqualSlices(
        SourceId,
        &.{ a, b },
        graph.sccMembers(graph.sourceScc(a).?),
    );
    try std.testing.expectEqual(graph.sourceScc(a), graph.sourceScc(b));
    try std.testing.expect(graph.sourceScc(c) != graph.sourceScc(a));
}

test "inactive tombstones do not consume graph storage or SCC work" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const active = (try registry.upsert("A.sol", "a")).id;
    const removed = (try registry.upsert("B.sol", "b")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();
    _ = try registry.beginRevision();
    _ = try registry.upsert("A.sol", "a");
    _ = try registry.finishRevision();
    registry.commitRevision();

    var graph = try SourceGraph.initAlloc(std.testing.allocator, &registry, &.{});
    defer graph.deinit();
    try std.testing.expectEqual(@as(usize, 2), graph.sourceCapacity());
    try std.testing.expectEqual(@as(usize, 1), graph.activeSourceCount());
    try std.testing.expectEqual(@as(usize, 1), graph.storageNodeCount());
    try std.testing.expect(graph.sourceScc(active) != null);
    try std.testing.expect(graph.sourceScc(removed) == null);
}

test "rename churn keeps the frozen graph proportional to active sources" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    for (0..64) |revision| {
        var name_buffer: [32]u8 = undefined;
        const name = try std.fmt.bufPrint(&name_buffer, "Generated-{d}.sol", .{revision});
        _ = try registry.beginRevision();
        _ = try registry.upsert(name, "contract Generated {}");
        _ = try registry.finishRevision();
        registry.commitRevision();
    }

    var graph = try SourceGraph.initAlloc(std.testing.allocator, &registry, &.{});
    defer graph.deinit();
    try std.testing.expectEqual(@as(usize, 64), graph.sourceCapacity());
    try std.testing.expectEqual(@as(usize, 1), graph.storageNodeCount());
    try std.testing.expectEqual(@as(usize, 1), graph.sccCount());
}

test "dirty source set propagates reverse closure and resets by epoch" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const a = (try registry.upsert("A.sol", "a")).id;
    const b = (try registry.upsert("B.sol", "b")).id;
    const c = (try registry.upsert("C.sol", "c")).id;
    const d = (try registry.upsert("D.sol", "d")).id;
    const e = (try registry.upsert("E.sol", "e")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();
    var graph = try SourceGraph.initAlloc(std.testing.allocator, &registry, &.{
        .{ .importer = a, .imported = b },
        .{ .importer = b, .imported = a },
        .{ .importer = c, .imported = a },
        .{ .importer = d, .imported = b },
    });
    defer graph.deinit();

    var dirty = try DirtySourceSet.init(std.testing.allocator, 0);
    defer dirty.deinit();
    try dirty.markReverseClosure(&graph, &.{a});
    try std.testing.expectEqual(@as(usize, 4), dirty.count());
    const sorted = try dirty.sortedIdsAlloc(std.testing.allocator);
    defer std.testing.allocator.free(sorted);
    try std.testing.expectEqualSlices(SourceId, &.{ a, b, c, d }, sorted);
    try std.testing.expect(!dirty.contains(e));

    dirty.beginEpoch();
    try std.testing.expectEqual(@as(usize, 0), dirty.count());
    try std.testing.expect(!dirty.contains(a));
    _ = try dirty.mark(&graph, e);
    try std.testing.expect(dirty.contains(e));

    dirty.epoch = std.math.maxInt(u64);
    dirty.beginEpoch();
    try std.testing.expectEqual(@as(u64, 1), dirty.epoch);
    try std.testing.expect(!dirty.contains(e));
}

test "selective dirty propagation filters unused imports and remains transitive" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const dependency = (try registry.upsert("Dependency.sol", "dependency")).id;
    const unused = (try registry.upsert("Unused.sol", "unused")).id;
    const used = (try registry.upsert("Used.sol", "used")).id;
    const downstream = (try registry.upsert("Downstream.sol", "downstream")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();
    var graph = try SourceGraph.initAlloc(std.testing.allocator, &registry, &.{
        .{ .importer = unused, .imported = dependency },
        .{ .importer = used, .imported = dependency },
        .{ .importer = downstream, .imported = unused },
    });
    defer graph.deinit();
    const masks = [_]SemanticFingerprint.DependencyMaskEntry{
        .{ .importer = unused, .imported = dependency },
        .{ .importer = used, .imported = dependency, .categories = .all },
        .{ .importer = downstream, .imported = unused },
    };

    var dirty = try DirtySourceSet.init(std.testing.allocator, registry.knownCount());
    defer dirty.deinit();
    try dirty.markSelectiveClosure(&graph, &.{.{
        .source = dependency,
        .categories = .{ .bits = SemanticFingerprint.CategoryMask.from(.call_dependencies).bits |
            SemanticFingerprint.CategoryMask.from(.codegen_inputs).bits },
    }}, &masks);
    try std.testing.expect(dirty.contains(dependency));
    try std.testing.expect(dirty.contains(used));
    try std.testing.expect(!dirty.contains(unused));
    try std.testing.expect(!dirty.contains(downstream));

    dirty.beginEpoch();
    try dirty.markSelectiveClosure(&graph, &.{.{
        .source = dependency,
        .categories = .from(.exported_symbols),
    }}, &masks);
    try std.testing.expectEqual(@as(usize, 4), dirty.count());
}

test "selective invalidation keeps source SCCs atomic" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const a = (try registry.upsert("A.sol", "a")).id;
    const b = (try registry.upsert("B.sol", "b")).id;
    const c = (try registry.upsert("C.sol", "c")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();
    var graph = try SourceGraph.initAlloc(std.testing.allocator, &registry, &.{
        .{ .importer = a, .imported = b },
        .{ .importer = b, .imported = a },
        .{ .importer = c, .imported = b },
    });
    defer graph.deinit();
    const masks = [_]SemanticFingerprint.DependencyMaskEntry{
        .{ .importer = a, .imported = b },
        .{ .importer = b, .imported = a },
        .{ .importer = c, .imported = b },
    };
    var dirty = try DirtySourceSet.init(std.testing.allocator, registry.knownCount());
    defer dirty.deinit();
    try dirty.markSelectiveClosure(&graph, &.{.{
        .source = a,
        .categories = .from(.codegen_inputs),
    }}, &masks);
    try std.testing.expectEqual(@as(usize, 3), dirty.count());
}

fn exerciseAllocationFailures(allocator: std.mem.Allocator) !void {
    var registry = SourceRegistry.init(allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const a = (try registry.upsert("A.sol", "a")).id;
    const b = (try registry.upsert("B.sol", "b")).id;
    const c = (try registry.upsert("C.sol", "c")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();
    var graph = try SourceGraph.initAlloc(allocator, &registry, &.{
        .{ .importer = a, .imported = b },
        .{ .importer = b, .imported = a },
        .{ .importer = c, .imported = a },
    });
    defer graph.deinit();
    var dirty = try DirtySourceSet.init(allocator, 0);
    defer dirty.deinit();
    try dirty.markReverseClosure(&graph, &.{b});
    dirty.beginEpoch();
    try dirty.markSelectiveClosure(&graph, &.{.{
        .source = b,
        .categories = .from(.codegen_inputs),
    }}, &.{});
    const sorted = try dirty.sortedIdsAlloc(allocator);
    defer allocator.free(sorted);
}

test "source graph and dirty set release all allocation-failure state" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        exerciseAllocationFailures,
        .{},
    );
}
