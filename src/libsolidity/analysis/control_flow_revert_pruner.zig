// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Interprocedural always-reverting edge pruning translated from
//! `ControlFlowRevertPruner.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Graph = @import("control_flow_graph.zig");

pub const PruneError = std.mem.Allocator.Error || error{InvalidAst};

const RevertState = enum { Unknown, AllPathsRevert, HasNonRevertingPath };

pub const ControlFlowRevertPruner = struct {
    allocator: std.mem.Allocator,
    cfg: *Graph.CFG,
    states: std.ArrayList(RevertState) = .empty,

    pub fn init(allocator: std.mem.Allocator, cfg: *Graph.CFG) ControlFlowRevertPruner {
        return .{ .allocator = allocator, .cfg = cfg };
    }

    pub fn deinit(self: *ControlFlowRevertPruner) void {
        self.states.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn run(self: *ControlFlowRevertPruner) PruneError!void {
        try self.states.resize(self.allocator, self.cfg.function_flows.items.len);
        @memset(self.states.items, .Unknown);
        var changed = true;
        while (changed) {
            changed = false;
            for (self.cfg.function_flows.items, 0..) |*entry, index| {
                if (self.states.items[index] != .Unknown) continue;
                const result = try self.evaluate(entry.key, &entry.flow);
                if (result != .Unknown) {
                    self.states.items[index] = result;
                    changed = true;
                }
            }
        }
        for (self.states.items) |*state| {
            if (state.* == .Unknown) state.* = .AllPathsRevert;
        }
        try self.modifyFlows();
    }

    fn evaluate(
        self: *ControlFlowRevertPruner,
        key: Graph.FunctionContractTuple,
        flow: *const Graph.FunctionFlow,
    ) PruneError!RevertState {
        var visited = std.AutoHashMap(*const Graph.CFGNode, void).init(self.allocator);
        defer visited.deinit();
        var queue: std.ArrayList(*const Graph.CFGNode) = .empty;
        defer queue.deinit(self.allocator);
        try queue.append(self.allocator, flow.entry);
        var found_exit = false;
        var found_unknown = false;
        var index: usize = 0;
        while (index < queue.items.len) : (index += 1) {
            const node = queue.items[index];
            const inserted = try visited.getOrPut(node);
            if (inserted.found_existing) continue;
            if (node == flow.exit) found_exit = true;
            if (node.function_definition) |function| {
                if (function.nodeKind() != .function_definition) return error.InvalidAst;
                if (function.payload.function_definition.implemented()) {
                    if (self.calledState(function, key.contract)) |state| switch (state) {
                        .Unknown => {
                            found_unknown = true;
                            continue;
                        },
                        .AllPathsRevert => continue,
                        .HasNonRevertingPath => {},
                    };
                }
            }
            for (node.exits.items) |next| try queue.append(self.allocator, next);
        }
        if (found_exit) return .HasNonRevertingPath;
        return if (found_unknown) .Unknown else .AllPathsRevert;
    }

    fn calledState(
        self: *const ControlFlowRevertPruner,
        function: *const AST.Node,
        calling_contract: ?*const AST.Node,
    ) ?RevertState {
        const contract = findScopeContract(function, calling_contract) catch return null;
        for (self.cfg.function_flows.items, 0..) |entry, index|
            if (entry.key.function == function and entry.key.contract == contract)
                return self.states.items[index];
        return null;
    }

    fn modifyFlows(self: *ControlFlowRevertPruner) PruneError!void {
        for (self.cfg.function_flows.items) |*entry| {
            var visited = std.AutoHashMap(*Graph.CFGNode, void).init(self.allocator);
            defer visited.deinit();
            var queue: std.ArrayList(*Graph.CFGNode) = .empty;
            defer queue.deinit(self.allocator);
            try queue.append(self.allocator, entry.flow.entry);
            var index: usize = 0;
            while (index < queue.items.len) : (index += 1) {
                const node = queue.items[index];
                const inserted = try visited.getOrPut(node);
                if (inserted.found_existing) continue;
                var pruned = false;
                if (node.function_definition) |function|
                    if (function.payload.function_definition.implemented())
                        if (self.calledState(function, entry.key.contract)) |state|
                            if (state != .HasNonRevertingPath) {
                                for (node.exits.items) |old_exit| removeEntry(old_exit, node);
                                node.exits.clearRetainingCapacity();
                                try node.exits.append(self.allocator, entry.flow.revert);
                                try entry.flow.revert.entries.append(self.allocator, node);
                                pruned = true;
                            };
                if (!pruned)
                    for (node.exits.items) |next| try queue.append(self.allocator, next);
            }
        }
    }
};

fn findScopeContract(
    function: *const AST.Node,
    calling_contract: ?*const AST.Node,
) PruneError!?*const AST.Node {
    const function_contract = ASTImplementation.scope(function);
    if (function_contract == null or function_contract.?.nodeKind() != .contract_definition)
        return null;
    if (calling_contract) |calling|
        if (try derivesFrom(calling, function_contract.?)) return calling;
    return function_contract;
}

fn derivesFrom(contract: *const AST.Node, base: *const AST.Node) PruneError!bool {
    const annotation = ASTAnnotations.annotationConst(contract) orelse return error.InvalidAst;
    const linearized = switch (annotation.*) {
        .contract_definition => |value| value.linearized_base_contracts,
        else => return error.InvalidAst,
    };
    for (linearized) |candidate| if (candidate == base) return true;
    return contract == base;
}

fn removeEntry(node: *Graph.CFGNode, entry: *Graph.CFGNode) void {
    var index: usize = 0;
    while (index < node.entries.items.len) {
        if (node.entries.items[index] == entry) {
            _ = node.entries.orderedRemove(index);
        } else index += 1;
    }
}
