// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Solidity CFG discovery translated from `ControlFlowGraph.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const Graph = @This();
const Builder = @import("control_flow_builder.zig");

pub const ConstructError = std.mem.Allocator.Error || error{InvalidAst};

pub fn constructFlow(cfg: *Graph.CFG, ast_root: *const AST.Node) ConstructError!bool {
    if (ast_root.nodeKind() != .source_unit) return error.InvalidAst;
    for (ast_root.payload.source_unit.nodes) |node| switch (node.nodeKind()) {
        .function_definition => {
            const function = node.payload.function_definition;
            if (function.implemented() and function.free)
                try appendFunction(cfg, node, null);
        },
        .contract_definition => try appendContractFunctions(cfg, node),
        else => {},
    };
    return !cfg.reporter.hasErrors();
}

fn appendContractFunctions(
    cfg: *Graph.CFG,
    most_derived_contract: *const AST.Node,
) ConstructError!void {
    const annotation = ASTAnnotations.annotationConst(most_derived_contract) orelse
        return error.InvalidAst;
    const contracts = switch (annotation.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => return error.InvalidAst,
    };
    if (contracts.len == 0) {
        try appendDefinedFunctions(cfg, most_derived_contract, most_derived_contract);
        return;
    }
    for (contracts) |contract|
        try appendDefinedFunctions(cfg, most_derived_contract, contract);
}

fn appendDefinedFunctions(
    cfg: *Graph.CFG,
    most_derived_contract: *const AST.Node,
    declaring_contract: *const AST.Node,
) ConstructError!void {
    if (declaring_contract.nodeKind() != .contract_definition)
        return error.InvalidAst;
    for (declaring_contract.payload.contract_definition.sub_nodes) |member| {
        if (member.nodeKind() != .function_definition) continue;
        if (!member.payload.function_definition.implemented()) continue;
        try appendFunction(cfg, member, most_derived_contract);
    }
}

fn appendFunction(
    cfg: *Graph.CFG,
    function: *const AST.Node,
    contract: ?*const AST.Node,
) ConstructError!void {
    const key: Graph.FunctionContractTuple = .{
        .contract = contract,
        .function = function,
    };
    if (cfg.functionFlow(function, contract) != null) return;
    const flow = try Builder.createFunctionFlow(&cfg.node_container, function, contract);
    try cfg.function_flows.append(cfg.allocator, .{ .key = key, .flow = flow });
}

const Diagnostics = @import("../../liblangutil/diagnostics.zig");

const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;

pub const VariableOccurrence = struct {
    pub const Kind = enum(c_int) {
        Declaration,
        Access,
        Return,
        Assignment,
        InlineAssembly,
    };

    declaration: *const AST.Node,
    kind: Kind = .Access,
    occurrence: ?SourceLocation = null,

    pub fn lessThan(_: void, lhs: VariableOccurrence, rhs: VariableOccurrence) bool {
        if (lhs.occurrence) |left_location| {
            if (rhs.occurrence) |right_location| {
                if (left_location.lessThan(right_location)) return true;
                if (right_location.lessThan(left_location)) return false;
            } else return false;
        } else if (rhs.occurrence != null) return true;
        const lhs_id = ASTAnnotations.compatibilityId(lhs.declaration);
        const rhs_id = ASTAnnotations.compatibilityId(rhs.declaration);
        if (lhs_id != rhs_id) return lhs_id < rhs_id;
        return @intFromEnum(lhs.kind) < @intFromEnum(rhs.kind);
    }
};

pub const CFGNode = struct {
    entries: std.ArrayList(*CFGNode) = .empty,
    exits: std.ArrayList(*CFGNode) = .empty,
    function_definition: ?*const AST.Node = null,
    variable_occurrences: std.ArrayList(VariableOccurrence) = .empty,
    location: SourceLocation = .{},

    fn deinit(self: *CFGNode, allocator: std.mem.Allocator) void {
        self.variable_occurrences.deinit(allocator);
        self.exits.deinit(allocator);
        self.entries.deinit(allocator);
        self.* = undefined;
    }
};

pub const FunctionFlow = struct {
    entry: *CFGNode,
    exit: *CFGNode,
    revert: *CFGNode,
    transaction_return: *CFGNode,
};

pub const FunctionContractTuple = struct {
    contract: ?*const AST.Node = null,
    function: *const AST.Node,

    pub fn eql(self: FunctionContractTuple, other: FunctionContractTuple) bool {
        return self.contract == other.contract and self.function == other.function;
    }
};

pub const FlowEntry = struct {
    key: FunctionContractTuple,
    flow: FunctionFlow,
};

pub const NodeContainer = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*CFGNode) = .empty,

    pub fn init(allocator: std.mem.Allocator) NodeContainer {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *NodeContainer) void {
        for (self.nodes.items) |node| {
            node.deinit(self.allocator);
            self.allocator.destroy(node);
        }
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn newNode(self: *NodeContainer) std.mem.Allocator.Error!*CFGNode {
        const node = try self.allocator.create(CFGNode);
        errdefer self.allocator.destroy(node);
        node.* = .{};
        try self.nodes.append(self.allocator, node);
        return node;
    }
};

pub const CFG = struct {
    allocator: std.mem.Allocator,
    reporter: *Diagnostics.ErrorReporter,
    node_container: NodeContainer,
    function_flows: std.ArrayList(FlowEntry) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        reporter: *Diagnostics.ErrorReporter,
    ) CFG {
        return .{
            .allocator = allocator,
            .reporter = reporter,
            .node_container = NodeContainer.init(allocator),
        };
    }

    pub fn deinit(self: *CFG) void {
        self.function_flows.deinit(self.allocator);
        self.node_container.deinit();
        self.* = undefined;
    }

    pub fn functionFlow(
        self: *CFG,
        function: *const AST.Node,
        contract: ?*const AST.Node,
    ) ?*FunctionFlow {
        for (self.function_flows.items) |*entry|
            if (entry.key.function == function and entry.key.contract == contract)
                return &entry.flow;
        return null;
    }

    pub fn functionFlowConst(
        self: *const CFG,
        function: *const AST.Node,
        contract: ?*const AST.Node,
    ) ?*const FunctionFlow {
        return @constCast(self).functionFlow(function, contract);
    }
};

test "CFG nodes own bidirectional arcs and variable occurrences" {
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var cfg = CFG.init(std.testing.allocator, &reporter);
    defer cfg.deinit();
    const first = try cfg.node_container.newNode();
    const second = try cfg.node_container.newNode();
    try first.exits.append(cfg.allocator, second);
    try second.entries.append(cfg.allocator, first);
    try std.testing.expect(first.exits.items[0] == second);
    try std.testing.expect(second.entries.items[0] == first);
}
