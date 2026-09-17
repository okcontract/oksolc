// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic Solidity callable graph storage from `CallGraph.cpp`.

const std = @import("std");
const AST = @import("ast.zig");
const CompatibilityIdResolver = @import("compatibility_id_resolver.zig").CompatibilityIdResolver;
const CompatibilityIds = @import("../../incremental/compatibility_ids.zig");

pub const SpecialNode = enum(c_int) {
    InternalDispatch,
    Entry,
};

pub const Node = union(enum) {
    callable: *const AST.Node,
    special: SpecialNode,

    pub fn eql(left: Node, right: Node) bool {
        return switch (left) {
            .callable => |value| switch (right) {
                .callable => |other| value == other,
                else => false,
            },
            .special => |value| switch (right) {
                .special => |other| value == other,
                else => false,
            },
        };
    }

    pub fn lessThan(
        compatibility_ids: CompatibilityIdResolver,
        left: Node,
        right: Node,
    ) bool {
        const left_tag = std.meta.activeTag(left);
        const right_tag = std.meta.activeTag(right);
        if (left_tag != right_tag)
            return @intFromEnum(left_tag) < @intFromEnum(right_tag);
        return switch (left) {
            .callable => |value| compatibility_ids.id(value).? <
                compatibility_ids.id(right.callable).?,
            .special => |value| @intFromEnum(value) < @intFromEnum(right.special),
        };
    }
};

pub const Edge = struct {
    caller: Node,
    callee: Node,
};

pub const BytecodeDependency = struct {
    contract: *const AST.Node,
    referencing_node: *const AST.Node,
    caller: Node,
};

pub const CallGraph = struct {
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    callers: std.ArrayList(Node) = .empty,
    edges: std.ArrayList(Edge) = .empty,
    bytecode_dependencies: std.ArrayList(BytecodeDependency) = .empty,
    emitted_events: std.ArrayList(*const AST.Node) = .empty,
    used_errors: std.ArrayList(*const AST.Node) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        compatibility_ids: CompatibilityIdResolver,
    ) CallGraph {
        return .{
            .allocator = allocator,
            .compatibility_ids = compatibility_ids,
        };
    }

    pub fn deinit(self: *CallGraph) void {
        self.used_errors.deinit(self.allocator);
        self.emitted_events.deinit(self.allocator);
        self.bytecode_dependencies.deinit(self.allocator);
        self.edges.deinit(self.allocator);
        self.callers.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn ensureCaller(self: *CallGraph, caller: Node) std.mem.Allocator.Error!void {
        if (self.hasCaller(caller)) return;
        try self.callers.append(self.allocator, caller);
        std.sort.insertion(
            Node,
            self.callers.items,
            self.compatibility_ids,
            Node.lessThan,
        );
    }

    pub fn hasCaller(self: *const CallGraph, caller: Node) bool {
        for (self.callers.items) |existing| if (Node.eql(existing, caller)) return true;
        return false;
    }

    pub fn addEdge(
        self: *CallGraph,
        caller: Node,
        callee: Node,
    ) std.mem.Allocator.Error!void {
        try self.ensureCaller(caller);
        for (self.edges.items) |edge|
            if (Node.eql(edge.caller, caller) and Node.eql(edge.callee, callee)) return;
        try self.edges.append(self.allocator, .{ .caller = caller, .callee = callee });
        std.sort.insertion(
            Edge,
            self.edges.items,
            self.compatibility_ids,
            edgeLessThan,
        );
    }

    pub fn addBytecodeDependency(
        self: *CallGraph,
        contract: *const AST.Node,
        referencing_node: *const AST.Node,
        caller: Node,
    ) std.mem.Allocator.Error!void {
        for (self.bytecode_dependencies.items) |entry|
            if (entry.contract == contract and
                entry.referencing_node == referencing_node) return;
        try self.bytecode_dependencies.append(self.allocator, .{
            .contract = contract,
            .referencing_node = referencing_node,
            .caller = caller,
        });
        std.sort.insertion(
            BytecodeDependency,
            self.bytecode_dependencies.items,
            self.compatibility_ids,
            dependencyLessThan,
        );
    }

    pub fn addEmittedEvent(
        self: *CallGraph,
        declaration: *const AST.Node,
    ) std.mem.Allocator.Error!void {
        try appendUniqueNode(
            self.allocator,
            self.compatibility_ids,
            &self.emitted_events,
            declaration,
        );
    }

    pub fn addUsedError(
        self: *CallGraph,
        declaration: *const AST.Node,
    ) std.mem.Allocator.Error!void {
        try appendUniqueNode(
            self.allocator,
            self.compatibility_ids,
            &self.used_errors,
            declaration,
        );
    }

    pub fn hasEdge(self: *const CallGraph, caller: Node, callee: Node) bool {
        for (self.edges.items) |edge|
            if (Node.eql(edge.caller, caller) and Node.eql(edge.callee, callee)) return true;
        return false;
    }
};

fn edgeLessThan(
    compatibility_ids: CompatibilityIdResolver,
    left: Edge,
    right: Edge,
) bool {
    if (Node.eql(left.caller, right.caller))
        return Node.lessThan(compatibility_ids, left.callee, right.callee);
    return Node.lessThan(compatibility_ids, left.caller, right.caller);
}

fn dependencyLessThan(
    compatibility_ids: CompatibilityIdResolver,
    left: BytecodeDependency,
    right: BytecodeDependency,
) bool {
    const left_contract = compatibility_ids.id(left.contract).?;
    const right_contract = compatibility_ids.id(right.contract).?;
    if (left_contract != right_contract) return left_contract < right_contract;
    return compatibility_ids.id(left.referencing_node).? <
        compatibility_ids.id(right.referencing_node).?;
}

fn appendUniqueNode(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    output: *std.ArrayList(*const AST.Node),
    node: *const AST.Node,
) std.mem.Allocator.Error!void {
    for (output.items) |existing| if (existing == node) return;
    try output.append(allocator, node);
    std.sort.insertion(*const AST.Node, output.items, compatibility_ids, struct {
        fn lessThan(
            resolver: CompatibilityIdResolver,
            left: *const AST.Node,
            right: *const AST.Node,
        ) bool {
            return resolver.id(left).? < resolver.id(right).?;
        }
    }.lessThan);
}

test "call graph keeps deterministic unique callers, edges, and side sets" {
    var graph = CallGraph.init(
        std.testing.allocator,
        CompatibilityIdResolver.legacyNodeIds(),
    );
    defer graph.deinit();
    const first: AST.Node = .{ .id = 2, .location = .{}, .payload = .{ .function_definition = undefined } };
    const second: AST.Node = .{ .id = 1, .location = .{}, .payload = .{ .function_definition = undefined } };
    try graph.addEdge(.{ .special = .Entry }, .{ .callable = &first });
    try graph.addEdge(.{ .special = .Entry }, .{ .callable = &first });
    try graph.addEdge(.{ .callable = &first }, .{ .callable = &second });
    try graph.addBytecodeDependency(&first, &first, .{ .special = .Entry });
    try graph.addBytecodeDependency(&first, &first, .{ .special = .Entry });
    try graph.addBytecodeDependency(&first, &second, .{ .callable = &first });
    try graph.addEmittedEvent(&first);
    try graph.addEmittedEvent(&first);
    try std.testing.expectEqual(@as(usize, 2), graph.edges.items.len);
    try std.testing.expectEqual(@as(usize, 2), graph.bytecode_dependencies.items.len);
    try std.testing.expectEqual(@as(usize, 1), graph.emitted_events.items.len);
}

test "call graph order follows the revision compatibility projection" {
    const late_source = AST.SourceId.init(10);
    const early_source = AST.SourceId.init(20);
    var projection = try CompatibilityIds.CompatibilityIdProjection.initAlloc(
        std.testing.allocator,
        &.{
            .{ .source = early_source, .node_count = 1 },
            .{ .source = late_source, .node_count = 1 },
        },
    );
    defer projection.deinit();

    var graph = CallGraph.init(
        std.testing.allocator,
        CompatibilityIdResolver.init(&projection),
    );
    defer graph.deinit();
    const late: AST.Node = .{
        .id = 1,
        .node_ref = .{ .source = late_source, .local_node = .init(0) },
        .location = .{},
        .payload = .{ .function_definition = undefined },
    };
    const early: AST.Node = .{
        .id = 2,
        .node_ref = .{ .source = early_source, .local_node = .init(0) },
        .location = .{},
        .payload = .{ .function_definition = undefined },
    };
    try graph.addEdge(.{ .callable = &late }, .{ .callable = &early });
    try graph.addEdge(.{ .callable = &early }, .{ .callable = &late });

    try std.testing.expectEqual(early.node_ref, graph.callers.items[0].callable.node_ref);
    try std.testing.expectEqual(late.node_ref, graph.callers.items[1].callable.node_ref);
}
