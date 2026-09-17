// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Borrowed constructor argument syntax and its compiler-defined evaluation
//! order. The sealed C3 hierarchy supplies dense scope IDs; no new inheritance
//! graph or mutable annotation is created. Values and effects belong to each
//! consumer, while this plan preserves the source expression and binding site.

const std = @import("std");
const AST = @import("ast.zig");

pub const Supplied = struct {
    target: *const AST.Node,
    origin: *const AST.Node,
    values: AST.NodeList,
};

/// Header order followed by constructor-invocation order, for syntax audits.
/// Plan sorts these groups by target hierarchy position for evaluation.
pub const Iterator = struct {
    contract: *const AST.Node,
    header: usize = 0,
    modifier: usize = 0,

    pub fn next(self: *Iterator) error{InvalidAst}!?Supplied {
        if (self.contract.nodeKind() != .contract_definition) return error.InvalidAst;
        const headers = self.contract.payload.contract_definition.base_contracts;
        while (self.header < headers.len) {
            const origin = headers[self.header];
            self.header += 1;
            if (origin.nodeKind() != .inheritance_specifier) return error.InvalidAst;
            const specifier = origin.payload.inheritance_specifier;
            const values = specifier.arguments orelse continue;
            if (values.len == 0) continue;
            const target = AST.referencedDeclaration(specifier.base_name) orelse return error.InvalidAst;
            if (target.nodeKind() != .contract_definition) return error.InvalidAst;
            return .{ .target = target, .origin = origin, .values = values };
        }
        const constructor = AST.contractConstructor(self.contract) orelse return null;
        const modifiers = constructor.payload.function_definition.modifiers;
        while (self.modifier < modifiers.len) {
            const origin = modifiers[self.modifier];
            self.modifier += 1;
            if (origin.nodeKind() != .modifier_invocation) return error.InvalidAst;
            const invocation = origin.payload.modifier_invocation;
            const target = AST.referencedDeclaration(invocation.modifier_name) orelse return error.InvalidAst;
            if (target.nodeKind() == .modifier_definition) continue;
            if (target.nodeKind() != .contract_definition) return error.InvalidAst;
            const values = invocation.arguments orelse return error.InvalidAst;
            if (values.len == 0) continue;
            return .{ .target = target, .origin = origin, .values = values };
        }
        return null;
    }
};

pub const Binding = struct {
    target_index: usize,
    supplied: Supplied,
};

pub const Plan = struct {
    allocator: std.mem.Allocator,
    /// Most-derived first. Borrowed for exactly the lifetime of this plan.
    hierarchy: []const *AST.Node,
    bindings: []Binding,
    offsets: []usize,

    pub fn initAlloc(allocator: std.mem.Allocator, hierarchy: []const *AST.Node) !Plan {
        if (hierarchy.len == 0) return error.InvalidAst;
        var indices: std.AutoHashMapUnmanaged(*const AST.Node, usize) = .empty;
        defer indices.deinit(allocator);
        for (hierarchy, 0..) |contract, index| {
            if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
            const inserted = try indices.getOrPut(allocator, contract);
            if (inserted.found_existing) return error.InvalidAst;
            inserted.value_ptr.* = index;
        }
        const seen = try allocator.alloc(bool, hierarchy.len);
        defer allocator.free(seen);
        @memset(seen, false);
        const offsets = try allocator.alloc(usize, std.math.add(usize, hierarchy.len, 1) catch return error.InvalidAst);
        errdefer allocator.free(offsets);
        var bindings: std.ArrayList(Binding) = .empty;
        defer bindings.deinit(allocator);
        for (hierarchy, 0..) |contract, scope| {
            offsets[scope] = bindings.items.len;
            var arguments: Iterator = .{ .contract = contract };
            while (try arguments.next()) |supplied| {
                const target = indices.get(supplied.target) orelse return error.InvalidAst;
                if (target <= scope or seen[target]) return error.InvalidAst;
                const constructor = AST.contractConstructor(supplied.target) orelse return error.InvalidAst;
                const parameters = constructor.payload.function_definition.callable.parameters;
                if (parameters.nodeKind() != .parameter_list or parameters.payload.parameter_list.parameters.len != supplied.values.len) return error.InvalidAst;
                seen[target] = true;
                try bindings.append(allocator, .{ .target_index = target, .supplied = supplied });
            }
            std.mem.sort(Binding, bindings.items[offsets[scope]..], {}, struct {
                fn lessThan(_: void, left: Binding, right: Binding) bool {
                    return left.target_index < right.target_index;
                }
            }.lessThan);
        }
        offsets[hierarchy.len] = bindings.items.len;
        return .{ .allocator = allocator, .hierarchy = hierarchy, .bindings = try bindings.toOwnedSlice(allocator), .offsets = offsets };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.offsets);
        self.allocator.free(self.bindings);
        self.* = undefined;
    }

    pub fn forScope(self: Plan, index: usize) []const Binding {
        return self.bindings[self.offsets[index]..self.offsets[index + 1]];
    }
};

const Fixture = struct {
    hierarchy: [4]*AST.Node,
    header: *AST.Node,
    invocation: *AST.Node,
    deep: *AST.Node,
};

fn named(tree: *AST.Tree, target: *AST.Node) !*AST.Node {
    const node = try tree.createNode(.{}, .{ .identifier = .{ .name = "Base" } });
    (try @import("ast_annotations.zig").ensure(tree, node)).identifier.referenced_declaration = target;
    return node;
}

fn fixture(tree: *AST.Tree) !Fixture {
    var hierarchy: [4]*AST.Node = undefined;
    for (&hierarchy) |*contract| {
        const parameter = try tree.createNode(.{}, .{ .variable_declaration = .{ .declaration = .{ .name = "value" } } });
        const parameters = try tree.createNode(.{}, .{ .parameter_list = .{ .parameters = try tree.ownSlice(*AST.Node, &.{parameter}) } });
        const body = try tree.createNode(.{}, .{ .block = .{} });
        const constructor = try tree.createNode(.{}, .{ .function_definition = .{ .kind = .Constructor, .callable = .{ .declaration = .{}, .parameters = parameters }, .body = body } });
        contract.* = try tree.createNode(.{}, .{ .contract_definition = .{ .declaration = .{}, .sub_nodes = try tree.ownSlice(*AST.Node, &.{constructor}) } });
    }
    const literal = try tree.createNode(.{}, .{ .literal = .{ .token = .Number, .value = "7" } });
    // Source order deliberately differs from target linearization order.
    const header = try tree.createNode(.{}, .{ .inheritance_specifier = .{ .base_name = try named(tree, hierarchy[2]), .arguments = try tree.ownSlice(*AST.Node, &.{literal}) } });
    const invocation = try tree.createNode(.{}, .{ .modifier_invocation = .{ .modifier_name = try named(tree, hierarchy[1]), .arguments = try tree.ownSlice(*AST.Node, &.{literal}) } });
    hierarchy[0].payload.contract_definition.base_contracts = try tree.ownSlice(*AST.Node, &.{header});
    @constCast(AST.contractConstructor(hierarchy[0]).?).payload.function_definition.modifiers = try tree.ownSlice(*AST.Node, &.{invocation});
    const deep = try tree.createNode(.{}, .{ .inheritance_specifier = .{ .base_name = try named(tree, hierarchy[3]), .arguments = try tree.ownSlice(*AST.Node, &.{literal}) } });
    hierarchy[2].payload.contract_definition.base_contracts = try tree.ownSlice(*AST.Node, &.{deep});
    return .{ .hierarchy = hierarchy, .header = header, .invocation = invocation, .deep = deep };
}

fn exercisePlan(allocator: std.mem.Allocator, input: *const Fixture) !void {
    var plan = try Plan.initAlloc(allocator, &input.hierarchy);
    defer plan.deinit();
    try std.testing.expect(plan.hierarchy.ptr == &input.hierarchy);
    const first = plan.forScope(0);
    try std.testing.expectEqual(@as(usize, 2), first.len);
    try std.testing.expectEqual(@as(usize, 1), first[0].target_index);
    try std.testing.expectEqual(@as(usize, 2), first[1].target_index);
    try std.testing.expect(first[0].supplied.origin == input.invocation);
    try std.testing.expect(first[1].supplied.origin == input.header);
    try std.testing.expect(first[0].supplied.values.ptr == input.invocation.payload.modifier_invocation.arguments.?.ptr);
    try std.testing.expectEqual(@as(usize, 0), plan.forScope(1).len);
    try std.testing.expectEqual(@as(usize, 1), plan.forScope(2).len);
    try std.testing.expect(plan.forScope(2)[0].supplied.origin == input.deep);
    try std.testing.expectEqual(@as(usize, 0), plan.forScope(3).len);
}

test "construction argument plan preserves scopes source bindings and compiler order with allocation failures" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Construction.sol");
    defer tree.deinit();
    const input = try fixture(&tree);
    try exercisePlan(std.testing.allocator, &input);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exercisePlan, .{&input});
}

test "construction argument plan rejects duplicate backward missing and malformed bindings" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Construction.sol");
    defer tree.deinit();
    const input = try fixture(&tree);
    try std.testing.expectError(error.InvalidAst, Plan.initAlloc(std.testing.allocator, &.{}));
    try std.testing.expectError(error.InvalidAst, Plan.initAlloc(std.testing.allocator, &.{ input.hierarchy[0], input.hierarchy[0] }));
    try std.testing.expectError(error.InvalidAst, Plan.initAlloc(std.testing.allocator, input.hierarchy[0..3]));
    const invocation = &input.invocation.payload.modifier_invocation;
    const saved_name = invocation.modifier_name;
    invocation.modifier_name = input.header.payload.inheritance_specifier.base_name;
    try std.testing.expectError(error.InvalidAst, Plan.initAlloc(std.testing.allocator, &input.hierarchy));
    invocation.modifier_name = try named(&tree, input.hierarchy[0]);
    try std.testing.expectError(error.InvalidAst, Plan.initAlloc(std.testing.allocator, &input.hierarchy));
    invocation.modifier_name = saved_name;
    const values = invocation.arguments.?;
    invocation.arguments = try tree.ownSlice(*AST.Node, &.{ values[0], values[0] });
    try std.testing.expectError(error.InvalidAst, Plan.initAlloc(std.testing.allocator, &input.hierarchy));
    invocation.arguments = values;
    input.hierarchy[1].payload.contract_definition.sub_nodes = &.{};
    try std.testing.expectError(error.InvalidAst, Plan.initAlloc(std.testing.allocator, &input.hierarchy));
}

test "construction argument syntax distinguishes absent arguments and real modifiers" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Construction.sol");
    defer tree.deinit();
    const input = try fixture(&tree);
    input.header.payload.inheritance_specifier.arguments = null;
    var supplied: Iterator = .{ .contract = input.hierarchy[0] };
    try std.testing.expect((try supplied.next()).?.origin == input.invocation);
    try std.testing.expect(try supplied.next() == null);
    input.header.payload.inheritance_specifier.arguments = &.{};
    input.invocation.payload.modifier_invocation.arguments = &.{};
    supplied = .{ .contract = input.hierarchy[0] };
    try std.testing.expect(try supplied.next() == null);
    input.invocation.payload.modifier_invocation.arguments = null;
    supplied = .{ .contract = input.hierarchy[0] };
    try std.testing.expectError(error.InvalidAst, supplied.next());
    const constructor = AST.contractConstructor(input.hierarchy[0]).?;
    const modifier = try tree.createNode(.{}, .{ .modifier_definition = .{ .callable = constructor.payload.function_definition.callable, .body = constructor.payload.function_definition.body } });
    input.invocation.payload.modifier_invocation.modifier_name = try named(&tree, modifier);
    supplied = .{ .contract = input.hierarchy[0] };
    try std.testing.expect(try supplied.next() == null);
}
