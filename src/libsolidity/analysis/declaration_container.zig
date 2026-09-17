// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Name container translated from `DeclarationContainer.cpp`.
//!
//! Sorted arrays replace upstream's ordered `std::map` instances to preserve
//! deterministic diagnostic suggestions and recursive lookup.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTImplementation = @import("../ast/ast.zig");
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;
const StringUtils = @import("../../libsolutil/string_utils.zig");

pub const ResolvingSettings = struct {
    recursive: bool = false,
    also_invisible: bool = false,
    only_visible_as_unqualified_names: bool = false,
};

pub const ContainerError = std.mem.Allocator.Error || error{
    InvalidActivation,
    InvalidDeclaration,
    InvalidDeclarationUpdate,
};

pub const NameEntry = struct {
    name: []u8,
    declarations: std.ArrayList(*const AST.Node) = .empty,

    fn deinit(self: *NameEntry, allocator: std.mem.Allocator) void {
        self.declarations.deinit(allocator);
        allocator.free(self.name);
        self.* = undefined;
    }
};

pub const Homonym = struct {
    location: *const SourceLocation,
    declarations: []*const AST.Node,
};

pub const Homonyms = struct {
    items: std.ArrayList(Homonym) = .empty,

    pub fn deinit(self: *Homonyms, allocator: std.mem.Allocator) void {
        for (self.items.items) |item| allocator.free(item.declarations);
        self.items.deinit(allocator);
        self.* = undefined;
    }
};

const HomonymCandidate = struct {
    name: []u8,
    location: *const SourceLocation,
};

pub const DeclarationContainer = struct {
    allocator: std.mem.Allocator,
    enclosing_node: ?*const AST.Node,
    enclosing_container: ?*DeclarationContainer,
    inner_containers: std.ArrayList(*const DeclarationContainer) = .empty,
    declaration_entries: std.ArrayList(NameEntry) = .empty,
    invisible_entries: std.ArrayList(NameEntry) = .empty,
    homonym_candidates: std.ArrayList(HomonymCandidate) = .empty,

    /// Creates a stable container and records its borrowed identity in the
    /// parent. Call `destroy` on every container after all lookup passes end.
    pub fn create(
        allocator: std.mem.Allocator,
        enclosing_node: ?*const AST.Node,
        enclosing_container: ?*DeclarationContainer,
    ) std.mem.Allocator.Error!*DeclarationContainer {
        const result = try allocator.create(DeclarationContainer);
        errdefer allocator.destroy(result);
        result.* = .{
            .allocator = allocator,
            .enclosing_node = enclosing_node,
            .enclosing_container = enclosing_container,
        };
        errdefer result.deinit();
        if (enclosing_container) |parent|
            try parent.inner_containers.append(allocator, result);
        return result;
    }

    pub fn destroy(self: *DeclarationContainer) void {
        const allocator = self.allocator;
        self.deinit();
        allocator.destroy(self);
    }

    fn deinit(self: *DeclarationContainer) void {
        for (self.declaration_entries.items) |*entry| entry.deinit(self.allocator);
        self.declaration_entries.deinit(self.allocator);
        for (self.invisible_entries.items) |*entry| entry.deinit(self.allocator);
        self.invisible_entries.deinit(self.allocator);
        self.inner_containers.deinit(self.allocator);
        for (self.homonym_candidates.items) |candidate|
            self.allocator.free(candidate.name);
        self.homonym_candidates.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn enclosingNode(self: *const DeclarationContainer) ?*const AST.Node {
        return self.enclosing_node;
    }

    pub fn enclosingContainer(self: *const DeclarationContainer) ?*const DeclarationContainer {
        return self.enclosing_container;
    }

    pub fn declarations(self: *const DeclarationContainer) []const NameEntry {
        return self.declaration_entries.items;
    }

    pub fn conflictingDeclaration(
        self: *const DeclarationContainer,
        declaration: *const AST.Node,
        alternative_name: ?[]const u8,
    ) ContainerError!?*const AST.Node {
        const declaration_data = declaration.declarationConst() orelse
            return error.InvalidDeclaration;
        const name = alternative_name orelse declaration_data.name;
        if (name.len == 0) return error.InvalidDeclaration;

        const overload_kind: ?AST.Kind = switch (declaration.nodeKind()) {
            .function_definition,
            .event_definition,
            .magic_variable_declaration,
            => declaration.nodeKind(),
            else => null,
        };

        if (overload_kind) |expected_kind| {
            if (entryConst(&self.declaration_entries, name)) |entry|
                for (entry.declarations.items) |existing|
                    if (existing.nodeKind() != expected_kind) return existing;
            if (entryConst(&self.invisible_entries, name)) |entry|
                for (entry.declarations.items) |existing|
                    if (existing.nodeKind() != expected_kind) return existing;
            return null;
        }

        var count: usize = 0;
        var first: ?*const AST.Node = null;
        if (entryConst(&self.declaration_entries, name)) |entry| {
            count += entry.declarations.items.len;
            if (entry.declarations.items.len != 0) first = entry.declarations.items[0];
        }
        if (entryConst(&self.invisible_entries, name)) |entry| {
            count += entry.declarations.items.len;
            if (first == null and entry.declarations.items.len != 0)
                first = entry.declarations.items[0];
        }
        if (count == 1 and first == declaration) return null;
        return if (count == 0) null else first;
    }

    pub fn registerDeclaration(
        self: *DeclarationContainer,
        declaration: *const AST.Node,
        alternative_name: ?[]const u8,
        alternative_location: ?*const SourceLocation,
        invisible: bool,
        update: bool,
    ) ContainerError!bool {
        const declaration_data = declaration.declarationConst() orelse
            return error.InvalidDeclaration;
        const name = alternative_name orelse declaration_data.name;
        if (name.len == 0) return true;

        if (update) {
            if (declaration.nodeKind() == .function_definition)
                return error.InvalidDeclarationUpdate;
            removeEntry(self.allocator, &self.declaration_entries, name);
            removeEntry(self.allocator, &self.invisible_entries, name);
        } else {
            if (try self.conflictingDeclaration(declaration, name) != null) return false;
        }

        const entries = if (invisible) &self.invisible_entries else &self.declaration_entries;
        const entry = try ensureEntry(self.allocator, entries, name);
        if (!containsDeclaration(entry.declarations.items, declaration))
            try entry.declarations.append(self.allocator, declaration);

        if (!update and self.enclosing_container != null and
            ASTImplementation.isVisibleAsUnqualifiedName(declaration))
        {
            const candidate_name = try self.allocator.dupe(u8, name);
            errdefer self.allocator.free(candidate_name);
            try self.homonym_candidates.append(self.allocator, .{
                .name = candidate_name,
                .location = alternative_location orelse &declaration.location,
            });
        }
        return true;
    }

    pub fn registerIntrinsic(
        self: *DeclarationContainer,
        declaration: *const AST.Node,
        invisible: bool,
        update: bool,
    ) ContainerError!bool {
        return self.registerDeclaration(declaration, null, null, invisible, update);
    }

    pub fn resolveNameAlloc(
        self: *const DeclarationContainer,
        allocator: std.mem.Allocator,
        name: []const u8,
        settings: ResolvingSettings,
    ) ContainerError![]*const AST.Node {
        if (name.len == 0) return error.InvalidDeclaration;
        var result: std.ArrayList(*const AST.Node) = .empty;
        errdefer result.deinit(allocator);

        if (entryConst(&self.declaration_entries, name)) |entry|
            try appendResolved(&result, allocator, entry, settings);
        if (settings.also_invisible)
            if (entryConst(&self.invisible_entries, name)) |entry|
                try appendResolved(&result, allocator, entry, settings);

        if (result.items.len == 0 and settings.recursive)
            if (self.enclosing_container) |parent| {
                result.deinit(allocator);
                return parent.resolveNameAlloc(allocator, name, settings);
            };
        return result.toOwnedSlice(allocator);
    }

    pub fn activateVariable(
        self: *DeclarationContainer,
        name: []const u8,
    ) ContainerError!void {
        const invisible_index = findEntryIndex(self.invisible_entries.items, name);
        if (invisible_index >= self.invisible_entries.items.len or
            !std.mem.eql(u8, self.invisible_entries.items[invisible_index].name, name) or
            self.invisible_entries.items[invisible_index].declarations.items.len != 1)
            return error.InvalidActivation;
        if (entryConst(&self.declaration_entries, name)) |visible|
            if (visible.declarations.items.len != 0) return error.InvalidActivation;

        const declaration = self.invisible_entries.items[invisible_index].declarations.items[0];
        const visible = try ensureEntry(self.allocator, &self.declaration_entries, name);
        try visible.declarations.append(self.allocator, declaration);
        var removed = self.invisible_entries.orderedRemove(invisible_index);
        removed.deinit(self.allocator);
    }

    pub fn isInvisible(self: *const DeclarationContainer, name: []const u8) bool {
        return entryConst(&self.invisible_entries, name) != null;
    }

    pub fn similarNamesAlloc(
        self: *const DeclarationContainer,
        allocator: std.mem.Allocator,
        name: []const u8,
    ) std.mem.Allocator.Error![][]const u8 {
        var result: std.ArrayList([]const u8) = .empty;
        errdefer result.deinit(allocator);
        try self.appendSimilarNames(&result, allocator, name);
        return result.toOwnedSlice(allocator);
    }

    fn appendSimilarNames(
        self: *const DeclarationContainer,
        result: *std.ArrayList([]const u8),
        allocator: std.mem.Allocator,
        name: []const u8,
    ) std.mem.Allocator.Error!void {
        const maximum_edit_distance: usize = if (name.len > 3) 2 else name.len / 2;
        for (self.declaration_entries.items) |entry|
            if (try StringUtils.stringWithinDistance(
                allocator,
                name,
                entry.name,
                maximum_edit_distance,
                80 * 80,
            )) try result.append(allocator, entry.name);
        for (self.invisible_entries.items) |entry|
            if (try StringUtils.stringWithinDistance(
                allocator,
                name,
                entry.name,
                maximum_edit_distance,
                80 * 80,
            )) try result.append(allocator, entry.name);
        if (self.enclosing_container) |parent|
            try parent.appendSimilarNames(result, allocator, name);
    }

    pub fn populateHomonyms(
        self: *const DeclarationContainer,
        result: *Homonyms,
        allocator: std.mem.Allocator,
    ) ContainerError!void {
        for (self.inner_containers.items) |inner|
            try inner.populateHomonyms(result, allocator);

        const parent = self.enclosing_container orelse return;
        for (self.homonym_candidates.items) |candidate| {
            const found = try parent.resolveNameAlloc(allocator, candidate.name, .{
                .recursive = true,
                .also_invisible = true,
            });
            if (found.len == 0) {
                allocator.free(found);
                continue;
            }
            errdefer allocator.free(found);
            try result.items.append(allocator, .{
                .location = candidate.location,
                .declarations = found,
            });
        }
    }
};

fn appendResolved(
    result: *std.ArrayList(*const AST.Node),
    allocator: std.mem.Allocator,
    entry: *const NameEntry,
    settings: ResolvingSettings,
) std.mem.Allocator.Error!void {
    for (entry.declarations.items) |declaration| {
        if (settings.only_visible_as_unqualified_names and
            !ASTImplementation.isVisibleAsUnqualifiedName(declaration)) continue;
        try result.append(allocator, declaration);
    }
}

fn containsDeclaration(items: []const *const AST.Node, needle: *const AST.Node) bool {
    for (items) |item| if (item == needle) return true;
    return false;
}

fn findEntryIndex(items: []const NameEntry, name: []const u8) usize {
    var lower: usize = 0;
    var upper = items.len;
    while (lower < upper) {
        const middle = lower + (upper - lower) / 2;
        if (std.mem.order(u8, items[middle].name, name) == .lt)
            lower = middle + 1
        else
            upper = middle;
    }
    return lower;
}

fn entryConst(entries: *const std.ArrayList(NameEntry), name: []const u8) ?*const NameEntry {
    const index = findEntryIndex(entries.items, name);
    if (index == entries.items.len or !std.mem.eql(u8, entries.items[index].name, name))
        return null;
    return &entries.items[index];
}

fn ensureEntry(
    allocator: std.mem.Allocator,
    entries: *std.ArrayList(NameEntry),
    name: []const u8,
) std.mem.Allocator.Error!*NameEntry {
    const index = findEntryIndex(entries.items, name);
    if (index < entries.items.len and std.mem.eql(u8, entries.items[index].name, name))
        return &entries.items[index];
    const owned_name = try allocator.dupe(u8, name);
    errdefer allocator.free(owned_name);
    try entries.insert(allocator, index, .{ .name = owned_name });
    return &entries.items[index];
}

fn removeEntry(
    allocator: std.mem.Allocator,
    entries: *std.ArrayList(NameEntry),
    name: []const u8,
) void {
    const index = findEntryIndex(entries.items, name);
    if (index == entries.items.len or !std.mem.eql(u8, entries.items[index].name, name))
        return;
    var removed = entries.orderedRemove(index);
    removed.deinit(allocator);
}

test "declaration containers preserve overloads, visibility, activation, and homonyms" {
    const Diagnostics = @import("../../liblangutil/diagnostics.zig");
    const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
    const Parser = @import("../parsing/parser.zig");
    const Scoper = @import("scoper.zig");

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { " ++
        "struct S { uint alpha; } " ++
        "function ping(uint a) external {} " ++
        "function ping(address a) external {} " ++
        "uint value; " ++
        "function g() external { uint value; } " ++
        "}";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Names.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    try std.testing.expect(!reporter.hasErrors());
    const root = parsed.tree.root.?;
    try Scoper.assignScopes(&parsed.tree, root);

    const contract = root.payload.source_unit.nodes[0];
    const sub_nodes = contract.payload.contract_definition.sub_nodes;
    const structure = sub_nodes[0];
    const structure_member = structure.payload.struct_definition.members[0];
    const first_ping = sub_nodes[1];
    const second_ping = sub_nodes[2];
    const state_value = sub_nodes[3];
    const function_g = sub_nodes[4];
    const local_value = function_g.payload.function_definition.body.?
        .payload.block.statements[0].payload.variable_declaration_statement
        .declarations[0].?;

    const root_container = try DeclarationContainer.create(std.testing.allocator, root, null);
    defer root_container.destroy();
    const contract_container = try DeclarationContainer.create(
        std.testing.allocator,
        contract,
        root_container,
    );
    defer contract_container.destroy();
    const function_container = try DeclarationContainer.create(
        std.testing.allocator,
        function_g,
        contract_container,
    );
    defer function_container.destroy();
    const struct_container = try DeclarationContainer.create(
        std.testing.allocator,
        structure,
        contract_container,
    );
    defer struct_container.destroy();

    try std.testing.expect(try root_container.registerIntrinsic(contract, false, false));
    try std.testing.expect(try contract_container.registerIntrinsic(first_ping, false, false));
    try std.testing.expect(try contract_container.registerIntrinsic(second_ping, false, false));
    try std.testing.expect(!(try contract_container.registerDeclaration(
        state_value,
        "ping",
        null,
        false,
        false,
    )));
    const overloads = try contract_container.resolveNameAlloc(
        std.testing.allocator,
        "ping",
        .{},
    );
    defer std.testing.allocator.free(overloads);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{ first_ping, second_ping },
        overloads,
    );

    try std.testing.expect(try contract_container.registerIntrinsic(state_value, false, false));
    try std.testing.expect(try function_container.registerIntrinsic(local_value, true, false));
    try std.testing.expect(function_container.isInvisible("value"));
    const hidden = try function_container.resolveNameAlloc(
        std.testing.allocator,
        "value",
        .{},
    );
    defer std.testing.allocator.free(hidden);
    try std.testing.expectEqual(@as(usize, 0), hidden.len);
    const recursive_hidden = try function_container.resolveNameAlloc(
        std.testing.allocator,
        "value",
        .{ .recursive = true, .also_invisible = true },
    );
    defer std.testing.allocator.free(recursive_hidden);
    try std.testing.expectEqualSlices(*const AST.Node, &.{local_value}, recursive_hidden);
    try function_container.activateVariable("value");
    try std.testing.expect(!function_container.isInvisible("value"));

    try std.testing.expect(try struct_container.registerIntrinsic(
        structure_member,
        false,
        false,
    ));
    const qualified_only = try struct_container.resolveNameAlloc(
        std.testing.allocator,
        "alpha",
        .{ .only_visible_as_unqualified_names = true },
    );
    defer std.testing.allocator.free(qualified_only);
    try std.testing.expectEqual(@as(usize, 0), qualified_only.len);

    const suggestions = try function_container.similarNamesAlloc(
        std.testing.allocator,
        "valu",
    );
    defer std.testing.allocator.free(suggestions);
    try std.testing.expectEqualStrings("value", suggestions[0]);

    var homonyms: Homonyms = .{};
    defer homonyms.deinit(std.testing.allocator);
    try root_container.populateHomonyms(&homonyms, std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 1), homonyms.items.items.len);
    try std.testing.expect(homonyms.items.items[0].location == &local_value.location);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{state_value},
        homonyms.items.items[0].declarations,
    );
}
