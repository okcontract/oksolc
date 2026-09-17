// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Syntactic-scope assignment translated from `Scoper.cpp`.
//!
//! Upstream performs this pass through the recursive AST visitor. The Zig
//! translation keeps the same enter/leave ordering with an explicit work
//! stack, propagates allocation failure, and stores annotations in the AST
//! tree's arena.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");

pub const ScopeError = std.mem.Allocator.Error || error{InvalidScopeTree};

const Phase = enum { enter, leave };

const Frame = struct {
    node: *AST.Node,
    phase: Phase,
};

const Scoper = struct {
    tree: *AST.Tree,
    transient_allocator: std.mem.Allocator,
    contract: ?*const AST.Node = null,
    scopes: std.ArrayList(*const AST.Node) = .empty,
    frames: std.ArrayList(Frame) = .empty,

    fn deinit(self: *Scoper) void {
        self.frames.deinit(self.transient_allocator);
        self.scopes.deinit(self.transient_allocator);
        self.* = undefined;
    }

    fn run(self: *Scoper, root: *AST.Node) ScopeError!void {
        try self.frames.append(self.transient_allocator, .{
            .node = root,
            .phase = .enter,
        });

        while (self.frames.pop()) |frame| switch (frame.phase) {
            .enter => try self.enter(frame.node),
            .leave => try self.leave(frame.node),
        };
    }

    fn enter(self: *Scoper, node: *AST.Node) ScopeError!void {
        const is_contract = node.nodeKind() == .contract_definition;
        if (is_contract) {
            if (self.contract != null) return error.InvalidScopeTree;
            self.contract = node;
        }

        const value = try ASTAnnotations.ensure(self.tree, node);
        if (ASTAnnotations.scopable(value)) |scopable| {
            scopable.scope = if (self.scopes.items.len == 0)
                null
            else
                self.scopes.items[self.scopes.items.len - 1];
            scopable.contract = self.contract;
        }

        if (isScopeOpener(node.nodeKind()))
            try self.scopes.append(self.transient_allocator, node);

        try self.frames.append(self.transient_allocator, .{
            .node = node,
            .phase = .leave,
        });

        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.transient_allocator);
        try ASTImplementation.appendChildren(self.transient_allocator, &children, node);
        var index = children.items.len;
        while (index != 0) {
            index -= 1;
            try self.frames.append(self.transient_allocator, .{
                .node = @constCast(children.items[index]),
                .phase = .enter,
            });
        }
    }

    fn leave(self: *Scoper, node: *AST.Node) ScopeError!void {
        if (isScopeOpener(node.nodeKind())) {
            const active = self.scopes.pop() orelse return error.InvalidScopeTree;
            if (active != node) return error.InvalidScopeTree;
        }
        if (node.nodeKind() == .contract_definition) {
            if (self.contract != node) return error.InvalidScopeTree;
            self.contract = null;
        }
    }
};

/// Assigns `scope` and enclosing `contract` to every upstream `Scopable` node.
/// Re-running the pass is supported and deterministically replaces both fields.
pub fn assignScopes(tree: *AST.Tree, root: *AST.Node) ScopeError!void {
    var scoper: Scoper = .{
        .tree = tree,
        .transient_allocator = tree.backing_allocator,
    };
    defer scoper.deinit();
    try scoper.run(root);
}

pub fn isScopeOpener(kind: AST.Kind) bool {
    return switch (kind) {
        .source_unit,
        .contract_definition,
        .struct_definition,
        .enum_definition,
        .function_definition,
        .modifier_definition,
        .event_definition,
        .error_definition,
        .function_type_name,
        .block,
        .try_catch_clause,
        .for_statement,
        .type_class_definition,
        .type_class_instantiation,
        .type_definition,
        .for_all_quantifier,
        => true,
        else => false,
    };
}

fn nodeScopable(node: *AST.Node) *ASTAnnotations.ScopableAnnotation {
    return ASTAnnotations.scopableForNode(node).?;
}

test "scope assignment preserves source, contract, callable, and block nesting" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../parsing/parser.zig");

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "uint fileValue; " ++
        "contract C { " ++
        "function f(uint parameter) external { " ++
        "uint localValue; { uint nestedValue; } " ++
        "} }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Scopes.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    try std.testing.expect(!reporter.hasErrors());

    const root = parsed.tree.root.?;
    try assignScopes(&parsed.tree, root);

    const file_value = root.payload.source_unit.nodes[0];
    const contract = root.payload.source_unit.nodes[1];
    const function = contract.payload.contract_definition.sub_nodes[0];
    const parameter = function.payload.function_definition.callable.parameters
        .payload.parameter_list.parameters[0];
    const body = function.payload.function_definition.body.?;
    const local_value = body.payload.block.statements[0]
        .payload.variable_declaration_statement.declarations[0].?;
    const nested_block = body.payload.block.statements[1];
    const nested_value = nested_block.payload.block.statements[0]
        .payload.variable_declaration_statement.declarations[0].?;

    try std.testing.expect(nodeScopable(file_value).scope == root);
    try std.testing.expect(nodeScopable(file_value).contract == null);
    try std.testing.expect(nodeScopable(contract).scope == root);
    try std.testing.expect(nodeScopable(contract).contract == contract);
    try std.testing.expect(nodeScopable(function).scope == contract);
    try std.testing.expect(nodeScopable(function).contract == contract);
    try std.testing.expect(nodeScopable(parameter).scope == function);
    try std.testing.expect(nodeScopable(body).scope == function);
    try std.testing.expect(nodeScopable(local_value).scope == body);
    try std.testing.expect(nodeScopable(nested_block).scope == body);
    try std.testing.expect(nodeScopable(nested_value).scope == nested_block);

    // The pass is deliberately idempotent because the upstream stack may
    // rebuild analysis after settings or source changes.
    try assignScopes(&parsed.tree, root);
    try std.testing.expect(nodeScopable(nested_value).scope == nested_block);
}
