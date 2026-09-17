// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Override validation translated from `OverrideChecker.cpp`.
//!
//! Node-backed proxies represent functions, modifiers, and variables.
//! Temporary inherited-callable collections use the checker's allocator;
//! base-function lists use the syntax tree's arena.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Enums = @import("../ast/ast_enums.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");

pub const CheckError = TypeProviderModule.ProviderError ||
    TypeBehavior.BehaviorError ||
    Diagnostics.ReportError ||
    std.mem.Allocator.Error ||
    error{InvalidAst};

const ProxyKind = enum { function, modifier, variable };

pub const OverrideProxy = struct {
    node: *AST.Node,

    pub fn init(node: *AST.Node) error{InvalidAst}!OverrideProxy {
        return switch (node.nodeKind()) {
            .function_definition, .modifier_definition, .variable_declaration => .{ .node = node },
            else => error.InvalidAst,
        };
    }

    fn kind(self: OverrideProxy) ProxyKind {
        return switch (self.node.nodeKind()) {
            .function_definition => .function,
            .modifier_definition => .modifier,
            .variable_declaration => .variable,
            else => unreachable,
        };
    }

    fn name(self: OverrideProxy) []const u8 {
        return self.node.declarationConst().?.name;
    }

    fn overrides(self: OverrideProxy) ?*AST.Node {
        return switch (self.node.payload) {
            .function_definition => |value| value.callable.overrides,
            .modifier_definition => |value| value.callable.overrides,
            .variable_declaration => |value| value.overrides,
            else => unreachable,
        };
    }

    fn functionKind(self: OverrideProxy) AST.Token {
        return switch (self.node.payload) {
            .function_definition => |value| value.kind,
            .modifier_definition, .variable_declaration => .Function,
            else => unreachable,
        };
    }

    fn visibility(self: OverrideProxy) AST.Visibility {
        if (self.kind() == .variable) return .External;
        return ASTImplementation.effectiveVisibility(self.node).?;
    }

    fn stateMutability(self: OverrideProxy) AST.StateMutability {
        return switch (self.node.payload) {
            .function_definition => |value| value.state_mutability,
            .variable_declaration => |value| if (value.mutability == .Constant) .Pure else .View,
            else => unreachable,
        };
    }

    fn unimplemented(self: OverrideProxy) bool {
        return switch (self.node.payload) {
            .function_definition => |value| !value.implemented(),
            .modifier_definition => |value| !value.implemented(),
            .variable_declaration => false,
            else => unreachable,
        };
    }

    fn nodeName(self: OverrideProxy) []const u8 {
        return switch (self.kind()) {
            .function => "function",
            .modifier => "modifier",
            .variable => "public state variable",
        };
    }

    fn capitalizedNodeName(self: OverrideProxy) []const u8 {
        return switch (self.kind()) {
            .function => "Function",
            .modifier => "Modifier",
            .variable => "Public state variable",
        };
    }

    fn distinguishingProperty(self: OverrideProxy) []const u8 {
        return if (self.kind() == .modifier) "name" else "name and parameter types";
    }
};

/// Undirected override graph used by the articulation-point check. Node zero
/// represents the current contract and node one is the artificial terminal
/// joined to every callable without a base declaration, matching upstream.
const OverrideGraph = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    proxies: std.ArrayList(OverrideProxy) = .empty,
    edges: std.ArrayList(std.ArrayList(usize)) = .empty,

    fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
    ) std.mem.Allocator.Error!OverrideGraph {
        var result = OverrideGraph{ .allocator = allocator, .tree = tree };
        errdefer result.deinit();
        try result.edges.append(allocator, .empty);
        try result.edges.append(allocator, .empty);
        return result;
    }

    fn deinit(self: *OverrideGraph) void {
        for (self.edges.items) |*neighbors| neighbors.deinit(self.allocator);
        self.edges.deinit(self.allocator);
        self.proxies.deinit(self.allocator);
        self.* = undefined;
    }

    fn addRoots(
        self: *OverrideGraph,
        roots: []const OverrideProxy,
    ) CheckError!void {
        const sorted = try self.allocator.dupe(OverrideProxy, roots);
        defer self.allocator.free(sorted);
        sortProxiesById(sorted);
        for (sorted) |root| try self.addEdge(0, try self.visit(root, 0));
        for (self.edges.items) |*neighbors| sortIndices(neighbors.items);
    }

    fn visit(
        self: *OverrideGraph,
        proxy: OverrideProxy,
        depth: usize,
    ) CheckError!usize {
        if (depth >= 256) return error.InvalidAst;
        for (self.proxies.items, 0..) |existing, index|
            if (existing.node == proxy.node) return index + 2;

        const node_index = self.edges.items.len;
        try self.proxies.append(self.allocator, proxy);
        try self.edges.append(self.allocator, .empty);

        const raw_bases = try baseFunctions(self.tree, proxy.node);
        if (raw_bases.len == 0) {
            try self.addEdge(node_index, 1);
            return node_index;
        }
        const bases = try self.allocator.alloc(OverrideProxy, raw_bases.len);
        defer self.allocator.free(bases);
        for (raw_bases, bases) |base, *target|
            target.* = try OverrideProxy.init(@constCast(base));
        sortProxiesById(bases);
        for (bases) |base|
            try self.addEdge(node_index, try self.visit(base, depth + 1));
        return node_index;
    }

    fn addEdge(self: *OverrideGraph, left: usize, right: usize) std.mem.Allocator.Error!void {
        if (!containsIndex(self.edges.items[left].items, right))
            try self.edges.items[left].append(self.allocator, right);
        if (!containsIndex(self.edges.items[right].items, left))
            try self.edges.items[right].append(self.allocator, left);
    }
};

const CutVertexTraversal = struct {
    graph: *const OverrideGraph,
    visited: []bool,
    depths: []isize,
    low: []isize,
    parents: []?usize,
    cuts: []bool,

    fn run(self: *CutVertexTraversal, node: usize, depth: usize) void {
        self.visited[node] = true;
        self.depths[node] = @intCast(depth);
        self.low[node] = @intCast(depth);
        for (self.graph.edges.items[node].items) |neighbor| {
            if (!self.visited[neighbor]) {
                self.parents[neighbor] = node;
                self.run(neighbor, depth + 1);
                if (self.low[neighbor] >= self.depths[node] and self.parents[node] != null)
                    self.cuts[node] = true;
                self.low[node] = @min(self.low[node], self.low[neighbor]);
            } else if (self.parents[node] == null or neighbor != self.parents[node].?) {
                self.low[node] = @min(self.low[node], self.depths[neighbor]);
            }
        }
    }
};

pub const OverrideChecker = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    type_provider: *TypeProviderModule.TypeProvider,
    reporter: *Diagnostics.ErrorReporter,
    compatibility_ids: CompatibilityIdResolver,

    pub fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
        type_provider: *TypeProviderModule.TypeProvider,
        reporter: *Diagnostics.ErrorReporter,
    ) OverrideChecker {
        return .{
            .allocator = allocator,
            .tree = tree,
            .type_provider = type_provider,
            .reporter = reporter,
            .compatibility_ids = .legacyNodeIds(),
        };
    }

    pub fn setCompatibilityIds(
        self: *OverrideChecker,
        compatibility_ids: CompatibilityIdResolver,
    ) void {
        self.compatibility_ids = compatibility_ids;
    }

    pub fn check(self: *OverrideChecker, contract: *AST.Node) CheckError!void {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        try self.checkIllegalOverrides(contract);
        try self.checkAmbiguousOverrides(contract);
    }

    fn checkIllegalOverrides(self: *OverrideChecker, contract: *AST.Node) CheckError!void {
        const inherited_functions = try self.inheritedCallablesAlloc(contract, .function, 0);
        defer self.allocator.free(inherited_functions);
        const inherited_modifiers = try self.inheritedCallablesAlloc(contract, .modifier, 0);
        defer self.allocator.free(inherited_modifiers);

        for (contract.payload.contract_definition.sub_nodes) |member| switch (member.nodeKind()) {
            .modifier_definition => {
                const proxy = try OverrideProxy.init(member);
                if (containsName(inherited_functions, proxy.name()))
                    try self.reporter.typeError(
                        errorId(5631),
                        member.location,
                        "Override changes function or public state variable to modifier.",
                    );
                try self.checkOverrideList(proxy, inherited_modifiers);
            },
            .function_definition => {
                if (member.payload.function_definition.kind == .Constructor) continue;
                const proxy = try OverrideProxy.init(member);
                if (containsName(inherited_modifiers, proxy.name()))
                    try self.reporter.typeError(
                        errorId(1469),
                        member.location,
                        "Override changes modifier to function.",
                    );
                try self.checkOverrideList(proxy, inherited_functions);
            },
            .variable_declaration => {
                if (!ASTImplementation.isStateVariable(member)) continue;
                const proxy = try OverrideProxy.init(member);
                if (!ASTImplementation.isPublic(member)) {
                    if (proxy.overrides() != null)
                        try self.reporter.typeError(
                            errorId(8022),
                            member.location,
                            "Override can only be used with public state variables.",
                        );
                    continue;
                }
                if (containsName(inherited_modifiers, proxy.name()))
                    try self.reporter.typeError(
                        errorId(1456),
                        member.location,
                        "Override changes modifier to public state variable.",
                    );
                try self.checkOverrideList(proxy, inherited_functions);
            },
            else => {},
        };
    }

    fn checkOverrideList(
        self: *OverrideChecker,
        item: OverrideProxy,
        inherited: []const OverrideProxy,
    ) CheckError!void {
        var specified: std.ArrayList(*AST.Node) = .empty;
        defer specified.deinit(self.allocator);
        try self.resolveOverrideList(item, &specified);

        var expected: std.ArrayList(*AST.Node) = .empty;
        defer expected.deinit(self.allocator);
        for (inherited) |super| {
            if (!(try self.signatureEqual(item, super))) continue;
            try self.checkOverride(item, super);
            const super_contract = try proxyContract(super);
            if (!containsNode(expected.items, super_contract))
                try expected.append(self.allocator, super_contract);
        }

        if (item.overrides()) |specifier| {
            if (expected.items.len == 0)
                try self.reporter.typeError(
                    errorId(7792),
                    specifier.location,
                    try self.formatTemporary(
                        "{s} has override specified but does not override anything.",
                        .{item.capitalizedNodeName()},
                    ),
                );
        }

        if (expected.items.len > 1) {
            var missing: std.ArrayList(*AST.Node) = .empty;
            defer missing.deinit(self.allocator);
            for (expected.items) |contract|
                if (!containsNode(specified.items, contract))
                    try missing.append(self.allocator, contract);
            if (missing.items.len != 0)
                try self.overrideListError(
                    item,
                    missing.items,
                    errorId(4327),
                    try self.formatTemporary(
                        "{s} needs to specify overridden ",
                        .{item.capitalizedNodeName()},
                    ),
                    "",
                );
        }

        var surplus: std.ArrayList(*AST.Node) = .empty;
        defer surplus.deinit(self.allocator);
        for (specified.items) |contract|
            if (!containsNode(expected.items, contract))
                try surplus.append(self.allocator, contract);
        if (surplus.items.len != 0)
            try self.overrideListError(
                item,
                surplus.items,
                errorId(2353),
                "Invalid ",
                "specified in override list: ",
            );
    }

    fn resolveOverrideList(
        self: *OverrideChecker,
        item: OverrideProxy,
        result: *std.ArrayList(*AST.Node),
    ) CheckError!void {
        const specifier = item.overrides() orelse return;
        if (specifier.nodeKind() != .override_specifier) return error.InvalidAst;
        const paths = specifier.payload.override_specifier.overrides;
        for (paths) |path| {
            const declaration = try referencedDeclaration(self.tree, path);
            if (declaration.nodeKind() != .contract_definition) continue;
            if (!containsNode(result.items, declaration))
                try result.append(self.allocator, declaration);
        }
        sortNodesById(result.items);

        const sorted_paths = try self.allocator.dupe(*AST.Node, paths);
        defer self.allocator.free(sorted_paths);
        try self.sortOverridePathsByContractId(sorted_paths);
        if (sorted_paths.len < 2) return;
        for (sorted_paths[1..], sorted_paths[0 .. sorted_paths.len - 1]) |path, previous| {
            const declaration = try referencedDeclaration(self.tree, path);
            const previous_declaration = try referencedDeclaration(self.tree, previous);
            if (declaration.nodeKind() == .contract_definition and
                declaration == previous_declaration)
            {
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(
                    self.allocator,
                    "First occurrence here: ",
                    previous.location,
                );
                const dotted = try std.mem.join(
                    self.allocator,
                    ".",
                    path.payload.identifier_path.path,
                );
                defer self.allocator.free(dotted);
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Duplicate contract \"{s}\" found in override list of \"{s}\".",
                    .{ dotted, item.name() },
                );
                defer self.allocator.free(message);
                try self.reporter.reportWithSecondary(
                    errorId(4520),
                    .TypeError,
                    path.location,
                    &secondary,
                    message,
                );
            }
        }
    }

    fn sortOverridePathsByContractId(
        self: *OverrideChecker,
        paths: []*AST.Node,
    ) CheckError!void {
        if (paths.len < 2) return;
        for (1..paths.len) |index| {
            const selected = paths[index];
            const selected_declaration = try referencedDeclaration(self.tree, selected);
            var position = index;
            while (position != 0) {
                const previous_declaration = try referencedDeclaration(
                    self.tree,
                    paths[position - 1],
                );
                if (ASTAnnotations.compatibilityId(selected_declaration) >=
                    ASTAnnotations.compatibilityId(previous_declaration)) break;
                paths[position] = paths[position - 1];
                position -= 1;
            }
            paths[position] = selected;
        }
    }

    fn checkOverride(
        self: *OverrideChecker,
        overriding: OverrideProxy,
        super: OverrideProxy,
    ) CheckError!void {
        if ((super.kind() == .modifier) != (overriding.kind() == .modifier))
            return error.InvalidAst;

        if (super.kind() != .variable) try self.storeBaseFunction(overriding, super);

        if (overriding.kind() == .modifier and
            !(try self.exactParametersEqual(overriding, super)))
            try self.reporter.typeError(
                errorId(1078),
                overriding.node.location,
                "Override changes modifier signature.",
            );

        if (overriding.overrides() == null and
            !(super.kind() == .function and
                (try proxyContract(super)).payload.contract_definition.contract_kind == .Interface))
        {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Overriding {s} is missing \"override\" specifier.",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(message);
            const secondary = try std.fmt.allocPrint(
                self.allocator,
                "Overridden {s} is here:",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(secondary);
            try self.overrideError(overriding, super, errorId(9456), message, secondary);
        }

        if (super.kind() == .variable) {
            const secondary = try std.fmt.allocPrint(
                self.allocator,
                "Overriding {s} is here:",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(secondary);
            try self.overrideError(
                super,
                overriding,
                errorId(1452),
                "Cannot override public state variable.",
                secondary,
            );
        } else if (!(try virtualSemantics(super))) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Trying to override non-virtual {s}. Did you forget to add \"virtual\"?",
                .{super.nodeName()},
            );
            defer self.allocator.free(message);
            const secondary = try std.fmt.allocPrint(
                self.allocator,
                "Overriding {s} is here:",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(secondary);
            try self.overrideError(super, overriding, errorId(4334), message, secondary);
        }

        if (overriding.kind() == .variable) {
            if (super.visibility() != .External)
                try self.overrideError(
                    overriding,
                    super,
                    errorId(5225),
                    "Public state variables can only override functions with external visibility.",
                    "Overridden function is here:",
                );
        } else if (overriding.visibility() != super.visibility() and
            !(super.visibility() == .External and overriding.visibility() == .Public))
        {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Overriding {s} visibility differs.",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(message);
            const secondary = try std.fmt.allocPrint(
                self.allocator,
                "Overridden {s} is here:",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(secondary);
            try self.overrideError(overriding, super, errorId(9098), message, secondary);
        }

        if (overriding.unimplemented() and !super.unimplemented()) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Overriding an implemented {s} with an unimplemented {s} is not allowed.",
                .{ super.nodeName(), overriding.nodeName() },
            );
            defer self.allocator.free(message);
            try self.overrideError(overriding, super, errorId(4593), message, null);
        }

        if (super.kind() != .function) return;
        var returns_differ = false;
        if (overriding.functionKind() != .Fallback and
            !(try self.externalReturnsEqual(overriding, super)))
        {
            returns_differ = true;
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Overriding {s} return types differ.",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(message);
            const secondary = try std.fmt.allocPrint(
                self.allocator,
                "Overridden {s} is here:",
                .{overriding.nodeName()},
            );
            defer self.allocator.free(secondary);
            try self.overrideError(overriding, super, errorId(4822), message, secondary);
        }

        if (overriding.kind() == .function and !returns_differ and
            super.visibility() != .External and overriding.functionKind() != .Fallback)
        {
            if (!(try self.exactParametersEqual(overriding, super)))
                try self.overrideError(
                    overriding,
                    super,
                    errorId(7723),
                    "Data locations of parameters have to be the same when overriding non-external functions, but they differ.",
                    try self.overriddenHereTemporary(overriding),
                );
            if (!(try self.exactReturnsEqual(overriding, super)))
                try self.overrideError(
                    overriding,
                    super,
                    errorId(1443),
                    "Data locations of return variables have to be the same when overriding non-external functions, but they differ.",
                    try self.overriddenHereTemporary(overriding),
                );
        }

        const overriding_mutability = overriding.stateMutability();
        const super_mutability = super.stateMutability();
        if ((@intFromEnum(overriding_mutability) > @intFromEnum(super_mutability) or
            super_mutability == .Payable) and overriding_mutability != super_mutability)
        {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "Overriding {s} changes state mutability from \"{s}\" to \"{s}\".",
                .{
                    overriding.nodeName(),
                    Enums.stateMutabilityToString(super_mutability),
                    Enums.stateMutabilityToString(overriding_mutability),
                },
            );
            defer self.allocator.free(message);
            try self.overrideError(overriding, super, errorId(6959), message, null);
        }
    }

    fn overrideError(
        self: *OverrideChecker,
        primary: OverrideProxy,
        secondary_proxy: OverrideProxy,
        id: Diagnostics.ErrorId,
        message: []const u8,
        secondary_message: ?[]const u8,
    ) CheckError!void {
        var secondary: Diagnostics.SecondarySourceLocation = .{};
        defer secondary.deinit(self.allocator);
        var allocated: ?[]u8 = null;
        defer if (allocated) |value| self.allocator.free(value);
        const label = secondary_message orelse blk: {
            allocated = try std.fmt.allocPrint(
                self.allocator,
                "Overridden {s} is here:",
                .{secondary_proxy.nodeName()},
            );
            break :blk allocated.?;
        };
        try secondary.append(self.allocator, label, secondary_proxy.node.location);
        try self.reporter.reportWithSecondary(
            id,
            .TypeError,
            primary.node.location,
            &secondary,
            message,
        );
    }

    fn overrideListError(
        self: *OverrideChecker,
        item: OverrideProxy,
        contracts: []const *AST.Node,
        id: Diagnostics.ErrorId,
        prefix: []const u8,
        qualifier: []const u8,
    ) CheckError!void {
        const sorted = try self.allocator.dupe(*AST.Node, contracts);
        defer self.allocator.free(sorted);
        sortNodesById(sorted);
        var secondary: Diagnostics.SecondarySourceLocation = .{};
        defer secondary.deinit(self.allocator);
        var quoted: std.ArrayList([]const u8) = .empty;
        defer {
            for (quoted.items) |name| self.allocator.free(name);
            quoted.deinit(self.allocator);
        }
        for (sorted) |contract| {
            try secondary.append(self.allocator, "This contract: ", contract.location);
            try quoted.append(
                self.allocator,
                try std.fmt.allocPrint(
                    self.allocator,
                    "\"{s}\"",
                    .{contract.payload.contract_definition.declaration.name},
                ),
            );
        }
        const names = try joinHumanReadable(self.allocator, quoted.items);
        defer self.allocator.free(names);
        const noun = if (sorted.len == 1) "contract " else "contracts ";
        const message = try std.fmt.allocPrint(
            self.allocator,
            "{s}{s}{s}{s}.",
            .{ prefix, noun, qualifier, names },
        );
        defer self.allocator.free(message);
        try self.reporter.reportWithSecondary(
            id,
            .TypeError,
            if (item.overrides()) |value| value.location else item.node.location,
            &secondary,
            message,
        );
    }

    fn checkAmbiguousOverrides(self: *OverrideChecker, contract: *AST.Node) CheckError!void {
        const functions = try self.inheritedCallablesAlloc(contract, .function, 0);
        defer self.allocator.free(functions);
        try self.checkAmbiguousGroups(contract, functions, .function);
        const modifiers = try self.inheritedCallablesAlloc(contract, .modifier, 0);
        defer self.allocator.free(modifiers);
        try self.checkAmbiguousGroups(contract, modifiers, .modifier);
    }

    fn checkAmbiguousGroups(
        self: *OverrideChecker,
        contract: *AST.Node,
        inherited: []const OverrideProxy,
        kind: ProxyKind,
    ) CheckError!void {
        const consumed = try self.allocator.alloc(bool, inherited.len);
        defer self.allocator.free(consumed);
        @memset(consumed, false);
        for (inherited, 0..) |first, first_index| {
            if (consumed[first_index] or self.contractDefinesSignature(contract, first, kind)) continue;
            var group: std.ArrayList(OverrideProxy) = .empty;
            defer group.deinit(self.allocator);
            for (inherited[first_index..], first_index..) |candidate, candidate_index| {
                if (consumed[candidate_index] or !(try self.signatureEqual(first, candidate))) continue;
                consumed[candidate_index] = true;
                if (!containsProxyNode(group.items, candidate.node))
                    try group.append(self.allocator, candidate);
            }
            if (group.items.len <= 1) continue;
            try self.pruneCutVertexAncestors(&group);
            if (group.items.len <= 1) continue;
            try self.reportAmbiguous(contract, group.items);
        }
    }

    fn pruneCutVertexAncestors(
        self: *OverrideChecker,
        callables: *std.ArrayList(OverrideProxy),
    ) CheckError!void {
        var graph = try OverrideGraph.init(self.allocator, self.tree);
        defer graph.deinit();
        try graph.addRoots(callables.items);

        const node_count = graph.edges.items.len;
        const visited = try self.allocator.alloc(bool, node_count);
        defer self.allocator.free(visited);
        @memset(visited, false);
        const depths = try self.allocator.alloc(isize, node_count);
        defer self.allocator.free(depths);
        @memset(depths, -1);
        const low = try self.allocator.alloc(isize, node_count);
        defer self.allocator.free(low);
        @memset(low, -1);
        const parents = try self.allocator.alloc(?usize, node_count);
        defer self.allocator.free(parents);
        @memset(parents, null);
        const cuts = try self.allocator.alloc(bool, node_count);
        defer self.allocator.free(cuts);
        @memset(cuts, false);

        var traversal = CutVertexTraversal{
            .graph = &graph,
            .visited = visited,
            .depths = depths,
            .low = low,
            .parents = parents,
            .cuts = cuts,
        };
        traversal.run(0, 0);

        const remove = try self.allocator.alloc(bool, callables.items.len);
        defer self.allocator.free(remove);
        @memset(remove, false);
        for (graph.proxies.items, 0..) |cut, proxy_index| {
            if (!cuts[proxy_index + 2]) continue;
            for (callables.items, 0..) |candidate, candidate_index| {
                if (try self.isBaseFunctionOf(candidate.node, cut.node, 0))
                    remove[candidate_index] = true;
            }
            if (cut.unimplemented()) {
                for (callables.items, 0..) |candidate, candidate_index| {
                    if (candidate.node == cut.node) remove[candidate_index] = true;
                }
            }
        }

        var target: usize = 0;
        for (callables.items, remove) |candidate, discard| {
            if (discard) continue;
            callables.items[target] = candidate;
            target += 1;
        }
        callables.shrinkRetainingCapacity(target);
    }

    fn reportAmbiguous(
        self: *OverrideChecker,
        contract: *AST.Node,
        proxies: []const OverrideProxy,
    ) CheckError!void {
        const sorted = try self.allocator.dupe(OverrideProxy, proxies);
        defer self.allocator.free(sorted);
        sortProxiesById(sorted);
        var secondary: Diagnostics.SecondarySourceLocation = .{};
        defer secondary.deinit(self.allocator);
        for (sorted) |proxy| {
            const owner = try proxyContract(proxy);
            const label = try std.fmt.allocPrint(
                self.allocator,
                "Definition in \"{s}\": ",
                .{owner.payload.contract_definition.declaration.name},
            );
            defer self.allocator.free(label);
            try secondary.append(self.allocator, label, proxy.node.location);
        }
        const first = sorted[0];
        const callable_name = if (first.kind() == .variable) "function" else first.nodeName();
        var message = try std.fmt.allocPrint(
            self.allocator,
            "Derived contract must override {s} \"{s}\". Two or more base classes define {s} with same {s}.",
            .{ callable_name, first.name(), callable_name, first.distinguishingProperty() },
        );
        defer self.allocator.free(message);
        var found_variable = false;
        for (sorted) |proxy| if (proxy.kind() == .variable) {
            found_variable = true;
            break;
        };
        if (found_variable) {
            const extended = try std.fmt.allocPrint(
                self.allocator,
                "{s} Since one of the bases defines a public state variable which cannot be overridden, you have to change the inheritance layout or the names of the functions.",
                .{message},
            );
            self.allocator.free(message);
            message = extended;
        }
        try self.reporter.reportWithSecondary(
            errorId(6480),
            .TypeError,
            contract.location,
            &secondary,
            message,
        );
    }

    fn inheritedCallablesAlloc(
        self: *OverrideChecker,
        contract: *AST.Node,
        kind: ProxyKind,
        depth: usize,
    ) CheckError![]OverrideProxy {
        if (depth >= 256 or contract.nodeKind() != .contract_definition)
            return error.InvalidAst;
        var result: std.ArrayList(OverrideProxy) = .empty;
        errdefer result.deinit(self.allocator);
        for (contract.payload.contract_definition.base_contracts) |specifier| {
            const base = try referencedDeclaration(
                self.tree,
                specifier.payload.inheritance_specifier.base_name,
            );
            var direct: std.ArrayList(OverrideProxy) = .empty;
            defer direct.deinit(self.allocator);
            for (base.payload.contract_definition.sub_nodes) |member| {
                if (!memberMatchesProxyKind(member, kind)) continue;
                const proxy = try OverrideProxy.init(member);
                if (!containsSignature(self, direct.items, proxy))
                    try direct.append(self.allocator, proxy);
            }
            const inherited = try self.inheritedCallablesAlloc(base, kind, depth + 1);
            defer self.allocator.free(inherited);
            if (kind == .modifier) {
                // Upstream builds one signature-set per direct-base branch for
                // modifiers, so inherited duplicates in that branch collapse.
                for (inherited) |proxy|
                    if (!containsSignature(self, direct.items, proxy))
                        try direct.append(self.allocator, proxy);
                try result.appendSlice(self.allocator, direct.items);
            } else {
                try result.appendSlice(self.allocator, direct.items);
                for (inherited) |proxy|
                    if (!containsSignature(self, direct.items, proxy))
                        try result.append(self.allocator, proxy);
            }
        }
        return result.toOwnedSlice(self.allocator);
    }

    pub fn signatureEqual(
        self: *OverrideChecker,
        left: OverrideProxy,
        right: OverrideProxy,
    ) CheckError!bool {
        return try self.signatureOrder(left, right) == .eq;
    }

    /// Mirrors `OverrideProxy::CompareBySignature`. The comparator deliberately
    /// has equivalence classes rather than a total order: modifiers only use
    /// their name, and receive/fallback declarations ignore parameters.
    pub fn signatureOrder(
        self: *OverrideChecker,
        left: OverrideProxy,
        right: OverrideProxy,
    ) CheckError!std.math.Order {
        const name_order = std.mem.order(u8, left.name(), right.name());
        if (name_order != .eq) return name_order;

        if (left.kind() == .modifier or right.kind() == .modifier) return .eq;
        const left_kind = left.functionKind();
        const right_kind = right.functionKind();
        if (left_kind != right_kind)
            return std.math.order(
                @intFromEnum(left_kind),
                @intFromEnum(right_kind),
            );
        if (left_kind != .Function) return .eq;

        const left_function = (try self.externalFunctionType(left)).payload.Function;
        const right_function = (try self.externalFunctionType(right)).payload.Function;
        const common_length = @min(
            left_function.parameter_types.len,
            right_function.parameter_types.len,
        );
        for (
            left_function.parameter_types[0..common_length],
            right_function.parameter_types[0..common_length],
        ) |left_type, right_type| {
            if (TypeBehavior.equals(left_type, right_type)) continue;
            const left_identifier = try TypeBehavior.compatibilityRichIdentifierAlloc(
                self.allocator,
                self.compatibility_ids,
                left_type,
            );
            defer self.allocator.free(left_identifier);
            const right_identifier = try TypeBehavior.compatibilityRichIdentifierAlloc(
                self.allocator,
                self.compatibility_ids,
                right_type,
            );
            defer self.allocator.free(right_identifier);
            var parameter_order = std.mem.order(
                u8,
                left_identifier,
                right_identifier,
            );
            if (parameter_order == .eq) {
                const left_stable = try TypeBehavior.richIdentifierAlloc(
                    self.allocator,
                    left_type,
                );
                defer self.allocator.free(left_stable);
                const right_stable = try TypeBehavior.richIdentifierAlloc(
                    self.allocator,
                    right_type,
                );
                defer self.allocator.free(right_stable);
                parameter_order = std.mem.order(u8, left_stable, right_stable);
            }
            if (parameter_order != .eq) return parameter_order;
        }
        return std.math.order(
            left_function.parameter_types.len,
            right_function.parameter_types.len,
        );
    }

    fn externalFunctionType(
        self: *OverrideChecker,
        proxy: OverrideProxy,
    ) CheckError!*const Types.Type {
        const function_type = switch (proxy.kind()) {
            .function => try self.type_provider.functionFromDefinition(
                proxy.node,
                .Declaration,
            ),
            .variable => try self.type_provider.functionFromVariable(proxy.node),
            .modifier => return error.InvalidAst,
        };
        return TypeBehavior.asExternallyCallableFunction(
            self.type_provider,
            function_type.payload.Function,
            false,
        );
    }

    fn externalReturnsEqual(
        self: *OverrideChecker,
        left: OverrideProxy,
        right: OverrideProxy,
    ) CheckError!bool {
        const left_function = (try self.externalFunctionType(left)).payload.Function;
        const right_function = (try self.externalFunctionType(right)).payload.Function;
        return typeSlicesEqual(
            left_function.return_parameter_types,
            right_function.return_parameter_types,
        );
    }

    fn exactParametersEqual(
        self: *OverrideChecker,
        left: OverrideProxy,
        right: OverrideProxy,
    ) CheckError!bool {
        return self.exactNodeListsEqual(callableParameters(left.node), callableParameters(right.node));
    }

    fn exactReturnsEqual(
        self: *OverrideChecker,
        left: OverrideProxy,
        right: OverrideProxy,
    ) CheckError!bool {
        return self.exactNodeListsEqual(callableReturns(left.node), callableReturns(right.node));
    }

    fn exactNodeListsEqual(
        self: *OverrideChecker,
        left: AST.NodeList,
        right: AST.NodeList,
    ) CheckError!bool {
        if (left.len != right.len) return false;
        for (left, right) |left_node, right_node| {
            const left_type = (try variableAnnotation(self.tree, left_node)).type_ref orelse
                return error.InvalidAst;
            const right_type = (try variableAnnotation(self.tree, right_node)).type_ref orelse
                return error.InvalidAst;
            if (!TypeBehavior.equals(left_type, right_type)) return false;
        }
        return true;
    }

    fn virtualSemantics(proxy: OverrideProxy) CheckError!bool {
        return switch (proxy.node.payload) {
            .function_definition => |value| value.callable.marked_virtual or
                (try proxyContract(proxy)).payload.contract_definition.contract_kind == .Interface,
            .modifier_definition => |value| value.callable.marked_virtual,
            .variable_declaration => false,
            else => error.InvalidAst,
        };
    }

    fn storeBaseFunction(
        self: *OverrideChecker,
        overriding: OverrideProxy,
        super: OverrideProxy,
    ) CheckError!void {
        const list = switch ((try ASTAnnotations.ensure(self.tree, overriding.node)).*) {
            .documented_callable => |*value| &value.callable.base_functions,
            .variable_declaration => |*value| &value.base_functions,
            else => return error.InvalidAst,
        };
        if (!containsConstNode(list.items, super.node))
            try list.append(self.tree.allocator(), super.node);
    }

    fn isBaseFunctionOf(
        self: *OverrideChecker,
        candidate: *const AST.Node,
        descendant: *AST.Node,
        depth: usize,
    ) CheckError!bool {
        if (depth >= 256) return error.InvalidAst;
        const bases = try baseFunctions(self.tree, descendant);
        for (bases) |base| {
            if (base == candidate) return true;
            if (try self.isBaseFunctionOf(candidate, @constCast(base), depth + 1)) return true;
        }
        return false;
    }

    fn contractDefinesSignature(
        self: *OverrideChecker,
        contract: *AST.Node,
        inherited: OverrideProxy,
        kind: ProxyKind,
    ) bool {
        for (contract.payload.contract_definition.sub_nodes) |member| {
            if (!memberMatchesProxyKind(member, kind)) continue;
            const candidate = OverrideProxy.init(member) catch continue;
            if (self.signatureEqual(candidate, inherited) catch false) return true;
        }
        return false;
    }

    fn formatTemporary(
        self: *OverrideChecker,
        comptime format: []const u8,
        args: anytype,
    ) CheckError![]const u8 {
        const value = try std.fmt.allocPrint(self.allocator, format, args);
        defer self.allocator.free(value);
        return try self.tree.ownString(value);
    }

    fn overriddenHereTemporary(self: *OverrideChecker, proxy: OverrideProxy) CheckError![]const u8 {
        return self.formatTemporary("Overridden {s} is here:", .{proxy.nodeName()});
    }
};

fn memberMatchesProxyKind(node: *AST.Node, kind: ProxyKind) bool {
    return switch (kind) {
        .function => node.nodeKind() == .function_definition and
            node.payload.function_definition.kind != .Constructor or
            (node.nodeKind() == .variable_declaration and
                ASTImplementation.isStateVariable(node) and ASTImplementation.isPublic(node)),
        .modifier => node.nodeKind() == .modifier_definition,
        .variable => false,
    };
}

fn containsName(proxies: []const OverrideProxy, name: []const u8) bool {
    for (proxies) |proxy| if (std.mem.eql(u8, proxy.name(), name)) return true;
    return false;
}

fn containsNode(nodes: []const *AST.Node, wanted: *const AST.Node) bool {
    for (nodes) |node| if (node == wanted) return true;
    return false;
}

fn containsConstNode(nodes: []const *const AST.Node, wanted: *const AST.Node) bool {
    for (nodes) |node| if (node == wanted) return true;
    return false;
}

fn containsProxyNode(proxies: []const OverrideProxy, wanted: *const AST.Node) bool {
    for (proxies) |proxy| if (proxy.node == wanted) return true;
    return false;
}

fn containsIndex(indices: []const usize, wanted: usize) bool {
    for (indices) |index| if (index == wanted) return true;
    return false;
}

fn containsSignature(
    checker: *OverrideChecker,
    proxies: []const OverrideProxy,
    wanted: OverrideProxy,
) bool {
    for (proxies) |proxy| if (checker.signatureEqual(proxy, wanted) catch false) return true;
    return false;
}

fn callableParameters(node: *const AST.Node) AST.NodeList {
    const list = switch (node.payload) {
        .function_definition => |value| value.callable.parameters,
        .modifier_definition => |value| value.callable.parameters,
        else => return &.{},
    };
    return list.payload.parameter_list.parameters;
}

fn callableReturns(node: *const AST.Node) AST.NodeList {
    const list = switch (node.payload) {
        .function_definition => |value| value.callable.return_parameters,
        else => null,
    } orelse return &.{};
    return list.payload.parameter_list.parameters;
}

fn typeSlicesEqual(
    left: []const *const Types.Type,
    right: []const *const Types.Type,
) bool {
    if (left.len != right.len) return false;
    for (left, right) |left_type, right_type|
        if (!TypeBehavior.equals(left_type, right_type)) return false;
    return true;
}

fn proxyContract(proxy: OverrideProxy) CheckError!*AST.Node {
    const scope = ASTImplementation.scope(proxy.node) orelse return error.InvalidAst;
    if (scope.nodeKind() != .contract_definition) return error.InvalidAst;
    return @constCast(scope);
}

fn referencedDeclaration(tree: *AST.Tree, node: *AST.Node) CheckError!*AST.Node {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .identifier_path => |value| @constCast(value.referenced_declaration orelse
            return error.InvalidAst),
        .identifier => |value| @constCast(value.referenced_declaration orelse
            return error.InvalidAst),
        else => error.InvalidAst,
    };
}

fn variableAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.VariableDeclarationAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .variable_declaration => |*value| value,
        else => error.InvalidAst,
    };
}

fn baseFunctions(tree: *AST.Tree, node: *AST.Node) CheckError![]const *const AST.Node {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .documented_callable => |*value| value.callable.base_functions.items,
        .variable_declaration => |*value| value.base_functions.items,
        else => error.InvalidAst,
    };
}

fn sortNodesById(nodes: []*AST.Node) void {
    if (nodes.len < 2) return;
    for (1..nodes.len) |index| {
        const selected = nodes[index];
        var position = index;
        while (position != 0 and
            ASTAnnotations.compatibilityId(selected) <
                ASTAnnotations.compatibilityId(nodes[position - 1]))
        {
            nodes[position] = nodes[position - 1];
            position -= 1;
        }
        nodes[position] = selected;
    }
}

fn sortProxiesById(proxies: []OverrideProxy) void {
    if (proxies.len < 2) return;
    for (1..proxies.len) |index| {
        const selected = proxies[index];
        var position = index;
        while (position != 0 and
            ASTAnnotations.compatibilityId(selected.node) <
                ASTAnnotations.compatibilityId(proxies[position - 1].node))
        {
            proxies[position] = proxies[position - 1];
            position -= 1;
        }
        proxies[position] = selected;
    }
}

fn sortIndices(indices: []usize) void {
    if (indices.len < 2) return;
    for (1..indices.len) |index| {
        const selected = indices[index];
        var position = index;
        while (position != 0 and selected < indices[position - 1]) {
            indices[position] = indices[position - 1];
            position -= 1;
        }
        indices[position] = selected;
    }
}

fn joinHumanReadable(
    allocator: std.mem.Allocator,
    values: []const []const u8,
) std.mem.Allocator.Error![]u8 {
    if (values.len == 0) return allocator.dupe(u8, "");
    if (values.len == 1) return allocator.dupe(u8, values[0]);
    var result: std.ArrayList(u8) = .empty;
    errdefer result.deinit(allocator);
    for (values, 0..) |value, index| {
        if (index != 0)
            try result.appendSlice(allocator, if (index + 1 == values.len) " and " else ", ");
        try result.appendSlice(allocator, value);
    }
    return result.toOwnedSlice(allocator);
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}
