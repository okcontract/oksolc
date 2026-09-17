// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic projection from stable source-local node references to the
//! compilation-wide AST IDs exposed by Solidity compatibility outputs.

const std = @import("std");
const Identity = @import("identity.zig");

pub const SourceId = Identity.SourceId;
pub const NodeRef = Identity.NodeRef;

pub const SourceNodeCount = struct {
    source: SourceId,
    node_count: u32,
};

const SourceSpan = struct {
    source: SourceId,
    preceding_node_count: i64,
    node_count: u32,

    fn lessThan(_: void, left: SourceSpan, right: SourceSpan) bool {
        return left.source.index() < right.source.index();
    }
};

pub const BuildError = std.mem.Allocator.Error || error{
    CompatibilityIdOverflow,
    DuplicateSource,
};

/// Allocator-owned compact lookup containing active sources only. Input order
/// is the parser's compatibility order; lookup storage is sorted by stable ID.
pub const CompatibilityIdProjection = struct {
    allocator: std.mem.Allocator,
    spans: []SourceSpan,
    last_id: i64,

    pub fn initAlloc(
        allocator: std.mem.Allocator,
        sources_in_parse_order: []const SourceNodeCount,
    ) BuildError!CompatibilityIdProjection {
        const spans = try allocator.alloc(SourceSpan, sources_in_parse_order.len);
        errdefer allocator.free(spans);

        var preceding_node_count: i64 = 0;
        for (sources_in_parse_order, spans) |source, *target_span| {
            target_span.* = .{
                .source = source.source,
                .preceding_node_count = preceding_node_count,
                .node_count = source.node_count,
            };
            preceding_node_count = std.math.add(
                i64,
                preceding_node_count,
                @as(i64, source.node_count),
            ) catch return error.CompatibilityIdOverflow;
        }
        std.mem.sort(SourceSpan, spans, {}, SourceSpan.lessThan);
        if (spans.len > 1)
            for (spans[1..], spans[0 .. spans.len - 1]) |current, previous|
                if (current.source == previous.source) return error.DuplicateSource;

        return .{
            .allocator = allocator,
            .spans = spans,
            .last_id = preceding_node_count,
        };
    }

    pub fn deinit(self: *CompatibilityIdProjection) void {
        self.allocator.free(self.spans);
        self.* = undefined;
    }

    pub fn id(self: *const CompatibilityIdProjection, node: NodeRef) ?i64 {
        const target_span = self.sourceSpan(node.source) orelse return null;
        const local_index = node.local_node.index();
        if (local_index >= target_span.node_count) return null;
        return target_span.preceding_node_count + @as(i64, local_index) + 1;
    }

    pub fn containsSource(self: *const CompatibilityIdProjection, source: SourceId) bool {
        return self.sourceSpan(source) != null;
    }

    /// Returns whether a candidate parser order would reproduce this exact
    /// compatibility-ID mapping. Node counts matter because changing an
    /// earlier span shifts every later source even when their relative order
    /// is unchanged.
    pub fn matches(
        self: *const CompatibilityIdProjection,
        sources_in_parse_order: []const SourceNodeCount,
    ) bool {
        if (sources_in_parse_order.len != self.spans.len) return false;
        var preceding_node_count: i64 = 0;
        for (sources_in_parse_order) |source| {
            const span = self.sourceSpan(source.source) orelse return false;
            if (span.preceding_node_count != preceding_node_count or
                span.node_count != source.node_count)
                return false;
            preceding_node_count = std.math.add(
                i64,
                preceding_node_count,
                @as(i64, source.node_count),
            ) catch return false;
        }
        return preceding_node_count == self.last_id;
    }

    fn sourceSpan(self: *const CompatibilityIdProjection, source: SourceId) ?SourceSpan {
        var low: usize = 0;
        var high = self.spans.len;
        while (low < high) {
            const middle = low + (high - low) / 2;
            const candidate = self.spans[middle];
            if (candidate.source == source) return candidate;
            if (candidate.source.index() < source.index())
                low = middle + 1
            else
                high = middle;
        }
        return null;
    }
};

test "compatibility IDs follow parse order without expanding tombstone space" {
    const first = SourceId.init(1000);
    const second = SourceId.init(7);
    var projection = try CompatibilityIdProjection.initAlloc(std.testing.allocator, &.{
        .{ .source = first, .node_count = 2 },
        .{ .source = second, .node_count = 3 },
    });
    defer projection.deinit();

    try std.testing.expectEqual(@as(usize, 2), projection.spans.len);
    try std.testing.expectEqual(@as(i64, 5), projection.last_id);
    try std.testing.expectEqual(@as(?i64, 1), projection.id(.{
        .source = first,
        .local_node = .init(0),
    }));
    try std.testing.expectEqual(@as(?i64, 2), projection.id(.{
        .source = first,
        .local_node = .init(1),
    }));
    try std.testing.expectEqual(@as(?i64, 3), projection.id(.{
        .source = second,
        .local_node = .init(0),
    }));
    try std.testing.expectEqual(@as(?i64, null), projection.id(.{
        .source = second,
        .local_node = .init(3),
    }));
    try std.testing.expect(!projection.containsSource(SourceId.init(8)));
}

test "compatibility projection rejects duplicate active sources" {
    const source = SourceId.init(1);
    try std.testing.expectError(
        error.DuplicateSource,
        CompatibilityIdProjection.initAlloc(std.testing.allocator, &.{
            .{ .source = source, .node_count = 1 },
            .{ .source = source, .node_count = 1 },
        }),
    );
}

test "compatibility projection matching includes order and span sizes" {
    const first = SourceId.init(3);
    const second = SourceId.init(8);
    var projection = try CompatibilityIdProjection.initAlloc(std.testing.allocator, &.{
        .{ .source = first, .node_count = 2 },
        .{ .source = second, .node_count = 4 },
    });
    defer projection.deinit();

    try std.testing.expect(projection.matches(&.{
        .{ .source = first, .node_count = 2 },
        .{ .source = second, .node_count = 4 },
    }));
    try std.testing.expect(!projection.matches(&.{
        .{ .source = second, .node_count = 4 },
        .{ .source = first, .node_count = 2 },
    }));
    try std.testing.expect(!projection.matches(&.{
        .{ .source = first, .node_count = 3 },
        .{ .source = second, .node_count = 4 },
    }));
}
