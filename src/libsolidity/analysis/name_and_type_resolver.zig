// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Declaration registration and lexical name lookup translated from
//! `NameAndTypeResolver.cpp`.
//!
//! The resolver owns stable declaration containers but borrows syntax trees,
//! the diagnostic reporter, and `GlobalContext`. All borrowed objects must
//! outlive the resolver. `ReferencesResolver` uses this module's registration,
//! import, lookup, homonym, inherited-scope, and C3 linearization support.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const ContainerModule = @import("declaration_container.zig");
const DeclarationContainer = ContainerModule.DeclarationContainer;
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const GlobalContextModule = @import("global_context.zig");
const GlobalContext = GlobalContextModule.GlobalContext;
const Scoper = @import("scoper.zig");
const SetOnceError = @import("../../libsolutil/set_once.zig").SetOnceError;
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;
const StringUtils = @import("../../libsolutil/string_utils.zig");
const Token = @import("../../liblangutil/token.zig");

pub const ResolverError = std.mem.Allocator.Error ||
    Diagnostics.ReportError ||
    ContainerModule.ContainerError ||
    GlobalContextModule.GlobalContextError ||
    SetOnceError ||
    error{
        InvalidAst,
        InvalidGlobalDeclaration,
        InvalidImportBinding,
        InvalidRegistration,
        InvalidScopeTree,
        MissingScope,
    };

pub const SourceUnitEntry = struct {
    path: []const u8,
    source_unit: *AST.Node,
};

const ScopeMap = std.AutoHashMap(?*const AST.Node, *DeclarationContainer);

pub const NameAndTypeResolver = struct {
    allocator: std.mem.Allocator,
    scopes: ScopeMap,
    owned_containers: std.ArrayList(*DeclarationContainer) = .empty,
    evm_version: EVMVersion,
    current_scope: *DeclarationContainer,
    reporter: *Diagnostics.ErrorReporter,
    global_context: *GlobalContext,
    experimental_solidity: bool,

    pub fn init(
        allocator: std.mem.Allocator,
        global_context: *GlobalContext,
        evm_version: EVMVersion,
        reporter: *Diagnostics.ErrorReporter,
        experimental_solidity: bool,
    ) ResolverError!NameAndTypeResolver {
        var self: NameAndTypeResolver = .{
            .allocator = allocator,
            .scopes = ScopeMap.init(allocator),
            .evm_version = evm_version,
            .current_scope = undefined,
            .reporter = reporter,
            .global_context = global_context,
            .experimental_solidity = experimental_solidity,
        };
        errdefer self.deinit();

        const global = try self.createOwnedContainer(null, null);
        try self.scopes.put(null, global);
        self.current_scope = global;
        for (global_context.declarations()) |declaration|
            if (!(try global.registerIntrinsic(declaration, false, false)))
                return error.InvalidGlobalDeclaration;
        return self;
    }

    pub fn deinit(self: *NameAndTypeResolver) void {
        while (self.owned_containers.pop()) |container| container.destroy();
        self.owned_containers.deinit(self.allocator);
        self.scopes.deinit();
        self.* = undefined;
    }

    fn createOwnedContainer(
        self: *NameAndTypeResolver,
        enclosing_node: ?*const AST.Node,
        enclosing_container: ?*DeclarationContainer,
    ) std.mem.Allocator.Error!*DeclarationContainer {
        const container = try DeclarationContainer.create(
            self.allocator,
            enclosing_node,
            enclosing_container,
        );
        errdefer container.destroy();
        try self.owned_containers.append(self.allocator, container);
        return container;
    }

    fn ensureScope(
        self: *NameAndTypeResolver,
        node: *const AST.Node,
        enclosing_node: ?*const AST.Node,
    ) ResolverError!*DeclarationContainer {
        if (self.scopes.get(node)) |existing| return existing;
        const parent = self.scopes.get(enclosing_node) orelse return error.MissingScope;
        const container = try self.createOwnedContainer(enclosing_node, parent);
        errdefer {
            const removed = self.owned_containers.pop().?;
            std.debug.assert(removed == container);
            container.destroy();
        }
        try self.scopes.put(node, container);
        return container;
    }

    /// Registers every declaration and creates every lexical container. The
    /// tree must already have passed through `Scoper.assignScopes`.
    pub fn registerDeclarations(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
        initial_scope: ?*const AST.Node,
    ) ResolverError!bool {
        return self.registerDeclarationsMode(tree, source_unit, initial_scope, false);
    }

    /// Reconstructs transient declaration containers from an already analyzed
    /// source without mutating its retained annotations.
    pub fn registerDeclarationsReusingAnnotations(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
        initial_scope: ?*const AST.Node,
    ) ResolverError!bool {
        return self.registerDeclarationsMode(tree, source_unit, initial_scope, true);
    }

    fn registerDeclarationsMode(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
        initial_scope: ?*const AST.Node,
        reuse_annotations: bool,
    ) ResolverError!bool {
        var registration: Registration = .{
            .resolver = self,
            .tree = tree,
            .initial_scope = initial_scope,
            .current_scope = initial_scope,
            .reuse_annotations = reuse_annotations,
        };
        defer registration.deinit();
        try registration.run(source_unit);
        if (registration.current_scope != initial_scope) return error.InvalidScopeTree;
        return true;
    }

    pub fn registerSource(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
    ) ResolverError!bool {
        return self.registerDeclarations(tree, source_unit, null);
    }

    pub fn registerSourceReusingAnnotations(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
    ) ResolverError!bool {
        return self.registerDeclarationsReusingAnnotations(tree, source_unit, null);
    }

    /// Applies symbol, wildcard, and unit-alias import semantics after every
    /// source unit has been registered. Import annotations are populated by
    /// the import-resolution phase before this call.
    pub fn performImports(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
        source_units: []const SourceUnitEntry,
    ) ResolverError!bool {
        return self.performImportsMode(tree, source_unit, source_units, false);
    }

    pub fn performImportsReusingAnnotations(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
        source_units: []const SourceUnitEntry,
    ) ResolverError!bool {
        return self.performImportsMode(tree, source_unit, source_units, true);
    }

    fn performImportsMode(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        source_unit: *AST.Node,
        source_units: []const SourceUnitEntry,
        reuse_annotations: bool,
    ) ResolverError!bool {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
        const target = self.scopes.get(source_unit) orelse return error.MissingScope;
        var error_found = false;

        for (source_unit.payload.source_unit.nodes) |node| {
            if (node.nodeKind() != .import_directive) continue;
            const import_annotation = try importAnnotation(tree, node);
            const absolute_path = import_annotation.absolute_path.value orelse
                return error.InvalidImportBinding;
            const importee = findSourceUnit(source_units, absolute_path) orelse
                return error.InvalidImportBinding;
            if (import_annotation.source_unit != importee) return error.InvalidImportBinding;
            const imported_scope = self.scopes.get(importee) orelse return error.MissingScope;
            const import = node.payload.import_directive;

            if (import.symbol_aliases.len != 0) {
                for (import.symbol_aliases) |alias| {
                    const symbol_name = switch (alias.symbol.payload) {
                        .identifier => |identifier| identifier.name,
                        else => return error.InvalidAst,
                    };
                    const declarations = try imported_scope.resolveNameAlloc(
                        self.allocator,
                        symbol_name,
                        .{},
                    );
                    defer self.allocator.free(declarations);
                    if (declarations.len == 0) {
                        const message = try std.fmt.allocPrint(
                            self.allocator,
                            "Declaration \"{s}\" not found in \"{s}\" (referenced as \"{s}\").",
                            .{ symbol_name, absolute_path, import.path },
                        );
                        defer self.allocator.free(message);
                        try self.reporter.declarationError(
                            errorId(2904),
                            node.location,
                            message,
                        );
                        error_found = true;
                        continue;
                    }
                    const alias_name = alias.alias orelse symbol_name;
                    for (declarations) |declaration| {
                        if (!(try registerDeclarationChecked(
                            target,
                            declaration,
                            alias_name,
                            &alias.location,
                            false,
                            self.reporter,
                        ))) {
                            error_found = true;
                        }
                    }
                }
            } else if (import.declaration.name.len == 0) {
                for (imported_scope.declarations()) |entry| {
                    for (entry.declarations.items) |declaration| {
                        if (!(try registerDeclarationChecked(
                            target,
                            declaration,
                            entry.name,
                            &node.location,
                            false,
                            self.reporter,
                        ))) {
                            error_found = true;
                        }
                    }
                }
            }
        }

        if (!reuse_annotations) {
            const source_annotation = try sourceUnitAnnotation(tree, source_unit);
            const entries = target.declarations();
            const exported = try tree.allocator().alloc(ASTAnnotations.ExportedSymbol, entries.len);
            for (entries, 0..) |entry, index| {
                exported[index] = .{
                    .name = try tree.ownString(entry.name),
                    .declarations = try ownNodeSlice(tree, entry.declarations.items),
                };
            }
            try source_annotation.exported_symbols.assign(exported);
        }
        return !error_found;
    }

    pub fn updateDeclaration(
        self: *NameAndTypeResolver,
        declaration: *const AST.Node,
        invisible: bool,
    ) ResolverError!bool {
        const global = self.scopes.get(null) orelse return error.MissingScope;
        if (ASTImplementation.scope(declaration) != null) return error.InvalidRegistration;
        return global.registerIntrinsic(declaration, invisible, true);
    }

    pub fn activateVariable(
        self: *NameAndTypeResolver,
        name: []const u8,
    ) ResolverError!void {
        if (self.current_scope.isInvisible(name))
            try self.current_scope.activateVariable(name);
    }

    /// Returns an allocator-owned declaration slice for a single lexical
    /// scope. `null` selects the implicit global scope.
    pub fn resolveNameAlloc(
        self: *const NameAndTypeResolver,
        allocator: std.mem.Allocator,
        name: []const u8,
        scope_node: ?*const AST.Node,
    ) ResolverError![]*const AST.Node {
        const container = self.scopes.get(scope_node) orelse
            return allocator.alloc(*const AST.Node, 0);
        return container.resolveNameAlloc(allocator, name, .{});
    }

    pub fn nameFromCurrentScopeAlloc(
        self: *const NameAndTypeResolver,
        allocator: std.mem.Allocator,
        name: []const u8,
        include_invisibles: bool,
    ) ResolverError![]*const AST.Node {
        return self.current_scope.resolveNameAlloc(allocator, name, .{
            .recursive = true,
            .also_invisible = include_invisibles,
        });
    }

    pub fn pathFromCurrentScopeAlloc(
        self: *const NameAndTypeResolver,
        allocator: std.mem.Allocator,
        path: AST.StringList,
        include_invisibles: bool,
    ) ResolverError![]*const AST.Node {
        if (path.len == 0) return error.InvalidAst;
        var result: std.ArrayList(*const AST.Node) = .empty;
        errdefer result.deinit(allocator);

        var candidates = try self.current_scope.resolveNameAlloc(allocator, path[0], .{
            .recursive = true,
            .also_invisible = include_invisibles,
            .only_visible_as_unqualified_names = true,
        });
        defer allocator.free(candidates);

        var index: usize = 1;
        while (index < path.len and candidates.len == 1) : (index += 1) {
            const candidate = candidates[0];
            const nested_scope = self.scopes.get(candidate) orelse {
                result.clearRetainingCapacity();
                return result.toOwnedSlice(allocator);
            };
            try result.append(allocator, candidate);
            const next = try nested_scope.resolveNameAlloc(allocator, path[index], .{
                .also_invisible = include_invisibles,
            });
            allocator.free(candidates);
            candidates = next;
        }
        if (index == path.len and candidates.len == 1) {
            try result.append(allocator, candidates[0]);
            return result.toOwnedSlice(allocator);
        }
        result.clearRetainingCapacity();
        return result.toOwnedSlice(allocator);
    }

    pub fn setScope(
        self: *NameAndTypeResolver,
        node: ?*const AST.Node,
    ) ResolverError!void {
        self.current_scope = self.scopes.get(node) orelse return error.MissingScope;
    }

    pub fn containsScope(
        self: *const NameAndTypeResolver,
        node: ?*const AST.Node,
    ) bool {
        return self.scopes.contains(node);
    }

    pub fn warnHomonymDeclarations(self: *NameAndTypeResolver) ResolverError!void {
        const global = self.scopes.get(null) orelse return error.MissingScope;
        var homonyms: ContainerModule.Homonyms = .{};
        defer homonyms.deinit(self.allocator);
        try global.populateHomonyms(&homonyms, self.allocator);

        for (homonyms.items.items) |homonym| {
            var magic_shadowed = false;
            var same_name: Diagnostics.SecondarySourceLocation = .{};
            defer same_name.deinit(self.allocator);
            var shadowed: Diagnostics.SecondarySourceLocation = .{};
            defer shadowed.deinit(self.allocator);

            for (homonym.declarations) |outer| {
                if (outer.nodeKind() == .magic_variable_declaration) {
                    magic_shadowed = true;
                } else if (!ASTImplementation.isVisibleInContract(outer)) {
                    try same_name.append(
                        self.allocator,
                        "The other declaration is here:",
                        outer.location,
                    );
                } else {
                    try shadowed.append(
                        self.allocator,
                        "The shadowed declaration is here:",
                        outer.location,
                    );
                }
            }

            if (magic_shadowed)
                try self.reporter.warning(
                    errorId(2319),
                    homonym.location.*,
                    "This declaration shadows a builtin symbol.",
                );
            if (same_name.infos.items.len != 0)
                try self.reporter.warningWithSecondary(
                    errorId(8760),
                    homonym.location.*,
                    "This declaration has the same name as another declaration.",
                    &same_name,
                );
            if (shadowed.infos.items.len != 0)
                try self.reporter.warningWithSecondary(
                    errorId(2519),
                    homonym.location.*,
                    "This declaration shadows an existing declaration.",
                    &shadowed,
                );
        }
    }

    pub fn similarNameSuggestionsAlloc(
        self: *const NameAndTypeResolver,
        allocator: std.mem.Allocator,
        name: []const u8,
    ) ResolverError![]u8 {
        const suggestions = try self.current_scope.similarNamesAlloc(allocator, name);
        defer allocator.free(suggestions);
        return StringUtils.quotedAlternativesListAlloc(allocator, suggestions);
    }

    pub fn experimentalSolidity(self: *const NameAndTypeResolver) bool {
        return self.experimental_solidity;
    }

    /// Imports declarations made directly in a base contract into the current
    /// contract scope. Members inherited by the base are imported when its
    /// own linearized bases are processed.
    pub fn importInheritedScope(
        self: *NameAndTypeResolver,
        base: *const AST.Node,
    ) ResolverError!void {
        if (base.nodeKind() != .contract_definition) return error.InvalidAst;
        const source = self.scopes.get(base) orelse return error.MissingScope;
        for (source.declarations()) |entry| {
            for (entry.declarations.items) |declaration| {
                if (ASTImplementation.scope(declaration) != base or
                    !ASTImplementation.isVisibleInDerivedContracts(declaration)) continue;
                if (try self.current_scope.registerIntrinsic(declaration, false, false)) continue;

                const conflicting = try self.current_scope.conflictingDeclaration(
                    declaration,
                    null,
                ) orelse return error.InvalidRegistration;
                if (declaration.nodeKind() == .modifier_definition and
                    conflicting.nodeKind() == .modifier_definition) continue;
                if (declaration.nodeKind() == .function_definition and
                    ASTImplementation.isStateVariable(conflicting) and
                    ASTImplementation.isPublic(conflicting)) continue;

                var first = conflicting.location;
                var second = declaration.location;
                if (declaration.location.start < conflicting.location.start) {
                    first = declaration.location;
                    second = conflicting.location;
                }
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(self.allocator);
                try secondary.append(
                    self.allocator,
                    "The previous declaration is here:",
                    first,
                );
                try self.reporter.reportWithSecondary(
                    errorId(9097),
                    .DeclarationError,
                    second,
                    &secondary,
                    "Identifier already declared.",
                );
            }
        }
    }

    /// Computes and stores the upstream reverse-precedence C3 linearization.
    /// Base identifier paths must already reference contract declarations.
    pub fn linearizeBaseContracts(
        self: *NameAndTypeResolver,
        tree: *AST.Tree,
        contract: *AST.Node,
    ) ResolverError!void {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        var inputs: std.ArrayList([]const *const AST.Node) = .empty;
        defer inputs.deinit(self.allocator);
        var direct: std.ArrayList(*const AST.Node) = .empty;
        defer direct.deinit(self.allocator);

        for (contract.payload.contract_definition.base_contracts) |specifier| {
            if (specifier.nodeKind() != .inheritance_specifier) return error.InvalidAst;
            const base_name = specifier.payload.inheritance_specifier.base_name;
            const referenced = (try identifierPathAnnotation(tree, base_name)).referenced_declaration;
            if (referenced == null or referenced.?.nodeKind() != .contract_definition) {
                try self.reporter.fatal(
                    errorId(8758),
                    .TypeError,
                    base_name.location,
                    null,
                    "Contract expected.",
                );
            }
            const base = referenced.?;
            const bases = (try contractAnnotation(tree, @constCast(base))).linearized_base_contracts;
            if (bases.len == 0) {
                try self.reporter.fatal(
                    errorId(2449),
                    .TypeError,
                    base_name.location,
                    null,
                    "Definition of base has to precede definition of derived contract",
                );
            }
            try direct.insert(self.allocator, 0, base);
            try inputs.insert(self.allocator, 0, bases);
        }
        try direct.insert(self.allocator, 0, contract);
        try inputs.append(self.allocator, direct.items);

        const merged = try cThreeMergeAlloc(
            self.allocator,
            *const AST.Node,
            inputs.items,
        );
        defer self.allocator.free(merged);
        if (merged.len == 0) {
            try self.reporter.fatal(
                errorId(5005),
                .TypeError,
                contract.location,
                null,
                "Linearization of inheritance graph impossible",
            );
        }
        (try contractAnnotation(tree, contract)).linearized_base_contracts =
            try ownNodeSlice(tree, merged);
    }
};

const Phase = enum { enter, leave };
const Frame = struct { node: *AST.Node, phase: Phase };

const Registration = struct {
    resolver: *NameAndTypeResolver,
    tree: *AST.Tree,
    initial_scope: ?*const AST.Node,
    current_scope: ?*const AST.Node,
    current_function: ?*AST.Node = null,
    current_contract: ?*AST.Node = null,
    reuse_annotations: bool = false,
    frames: std.ArrayList(Frame) = .empty,

    fn deinit(self: *Registration) void {
        if (self.current_contract != null)
            self.resolver.global_context.resetCurrentContract();
        self.frames.deinit(self.resolver.allocator);
        self.* = undefined;
    }

    fn run(self: *Registration, root: *AST.Node) ResolverError!void {
        try self.frames.append(self.resolver.allocator, .{ .node = root, .phase = .enter });
        while (self.frames.pop()) |frame| switch (frame.phase) {
            .enter => try self.enter(frame.node),
            .leave => try self.leave(frame.node),
        };
    }

    fn enter(self: *Registration, node: *AST.Node) ResolverError!void {
        if (node.nodeKind() == .source_unit)
            _ = try self.resolver.ensureScope(node, self.current_scope);

        if (node.nodeKind() == .import_directive) {
            const annotation = try importAnnotation(self.tree, node);
            const importee = annotation.source_unit orelse return error.InvalidImportBinding;
            const imported_scope = if (self.resolver.scopes.get(importee)) |existing|
                existing
            else
                try self.resolver.ensureScope(@constCast(importee), null);
            try self.resolver.scopes.put(node, imported_scope);
        }

        if (node.nodeKind() == .contract_definition) {
            if (self.current_contract != null) return error.InvalidScopeTree;
            self.current_contract = node;
            self.resolver.global_context.setCurrentContract(node);
            const global = self.resolver.scopes.get(null) orelse return error.MissingScope;
            if (!(try global.registerIntrinsic(
                try self.resolver.global_context.currentThis(),
                false,
                true,
            ))) return error.InvalidGlobalDeclaration;
            if (!(try global.registerIntrinsic(
                try self.resolver.global_context.currentSuper(),
                false,
                true,
            ))) return error.InvalidGlobalDeclaration;
        }

        if (ASTAnnotations.scopableForNode(node)) |scopable| {
            if (scopable.scope != self.current_scope or
                scopable.contract != self.current_contract) return error.InvalidScopeTree;
        }

        if (node.declarationConst() != null)
            try self.registerDeclaration(node);

        if (!self.reuse_annotations)
            if (try typeDeclarationAnnotation(self.tree, node)) |annotation|
                try self.assignCanonicalName(node, annotation);

        if (Scoper.isScopeOpener(node.nodeKind())) {
            _ = try self.resolver.ensureScope(node, self.current_scope);
            self.current_scope = node;
        }

        if (isVariableScope(node.nodeKind())) {
            if (self.current_function != null) return error.InvalidScopeTree;
            self.current_function = node;
        }

        try self.frames.append(self.resolver.allocator, .{ .node = node, .phase = .leave });
        if (node.nodeKind() == .import_directive) return;

        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.resolver.allocator);
        try ASTImplementation.appendChildren(self.resolver.allocator, &children, node);
        var index = children.items.len;
        while (index != 0) {
            index -= 1;
            try self.frames.append(self.resolver.allocator, .{
                .node = @constCast(children.items[index]),
                .phase = .enter,
            });
        }
    }

    fn leave(self: *Registration, node: *AST.Node) ResolverError!void {
        if (!self.reuse_annotations and node.nodeKind() == .variable_declaration_statement) {
            const function = self.current_function orelse return error.InvalidScopeTree;
            const annotation = try callableAnnotation(self.tree, function);
            for (node.payload.variable_declaration_statement.declarations) |declaration|
                if (declaration) |present|
                    try annotation.local_variables.append(self.tree.allocator(), present);
        }

        if (node.nodeKind() == .contract_definition) {
            if (self.current_contract != node) return error.InvalidScopeTree;
            const global = self.resolver.scopes.get(null) orelse return error.MissingScope;
            if (!(try global.registerIntrinsic(
                try self.resolver.global_context.currentThis(),
                true,
                true,
            ))) return error.InvalidGlobalDeclaration;
            if (!(try global.registerIntrinsic(
                try self.resolver.global_context.currentSuper(),
                true,
                true,
            ))) return error.InvalidGlobalDeclaration;
            self.resolver.global_context.resetCurrentContract();
            self.current_contract = null;
        }

        if (Scoper.isScopeOpener(node.nodeKind())) {
            if (self.current_scope != node) return error.InvalidScopeTree;
            const container = self.resolver.scopes.get(node) orelse return error.MissingScope;
            self.current_scope = container.enclosingNode();
        }
        if (isVariableScope(node.nodeKind())) {
            if (self.current_function != node) return error.InvalidScopeTree;
            self.current_function = null;
        }
    }

    fn registerDeclaration(
        self: *Registration,
        declaration: *AST.Node,
    ) ResolverError!void {
        const current = self.current_scope orelse return error.MissingScope;
        var target_node: ?*const AST.Node = current;
        var inactive = current.nodeKind() == .block or current.nodeKind() == .for_statement;

        if (current.nodeKind() == .for_all_quantifier and
            declaration.nodeKind() == .function_definition)
        {
            target_node = ASTImplementation.scope(current) orelse return error.InvalidScopeTree;
            inactive = false;
        }
        const target = self.resolver.scopes.get(target_node) orelse return error.MissingScope;
        _ = try registerDeclarationChecked(
            target,
            declaration,
            null,
            null,
            inactive,
            self.resolver.reporter,
        );
    }

    fn assignCanonicalName(
        self: *Registration,
        declaration: *AST.Node,
        annotation: *ASTAnnotations.TypeDeclarationAnnotation,
    ) ResolverError!void {
        const data = declaration.declarationConst() orelse return error.InvalidAst;
        if (data.name.len == 0) return error.InvalidAst;
        var components: std.ArrayList([]const u8) = .empty;
        defer components.deinit(self.resolver.allocator);
        try components.append(self.resolver.allocator, data.name);

        var scope_node = self.current_scope;
        while (scope_node) |scope_value| {
            if (scope_value.declarationConst()) |scope_declaration| {
                if (scope_declaration.name.len == 0) return error.InvalidAst;
                try components.append(self.resolver.allocator, scope_declaration.name);
            }
            const container = self.resolver.scopes.get(scope_value) orelse return error.MissingScope;
            scope_node = container.enclosingNode();
        }

        var length: usize = components.items.len - 1;
        for (components.items) |component| length += component.len;
        const canonical = try self.tree.allocator().alloc(u8, length);
        var output_index: usize = 0;
        var component_index = components.items.len;
        while (component_index != 0) {
            component_index -= 1;
            if (output_index != 0) {
                canonical[output_index] = '.';
                output_index += 1;
            }
            const component = components.items[component_index];
            @memcpy(canonical[output_index..][0..component.len], component);
            output_index += component.len;
        }
        std.debug.assert(output_index == canonical.len);
        try annotation.canonical_name.assign(canonical);
    }
};

pub fn registerDeclarationChecked(
    container: *DeclarationContainer,
    declaration: *const AST.Node,
    alternative_name: ?[]const u8,
    alternative_location: ?*const SourceLocation,
    inactive: bool,
    reporter: *Diagnostics.ErrorReporter,
) ResolverError!bool {
    const declaration_data = declaration.declarationConst() orelse return error.InvalidAst;
    const location = alternative_location orelse &declaration.location;
    const name = alternative_name orelse declaration_data.name;
    if (inactive and !ASTImplementation.isVisibleInContract(declaration))
        return error.InvalidRegistration;

    if (isReservedName(name) and !ASTImplementation.isPublicFunctionOrEvent(declaration)) {
        const message = try std.fmt.allocPrint(
            reporter.allocator,
            "The name \"{s}\" is reserved.",
            .{name},
        );
        defer reporter.allocator.free(message);
        try reporter.declarationError(errorId(3726), location.*, message);
    } else if (Token.isFutureSolidityKeyword(name)) {
        const message = try std.fmt.allocPrint(
            reporter.allocator,
            "\"{s}\" will be promoted to keyword in the future and will not be allowed as an identifier anymore.",
            .{name},
        );
        defer reporter.allocator.free(message);
        try reporter.warning(errorId(6335), location.*, message);
    }

    const registered = try container.registerDeclaration(
        declaration,
        alternative_name,
        location,
        !ASTImplementation.isVisibleInContract(declaration) or inactive,
        false,
    );
    if (registered) return true;

    const conflicting = try container.conflictingDeclaration(
        declaration,
        alternative_name,
    ) orelse return error.InvalidRegistration;
    var first = conflicting.location;
    var second = location.*;
    const comparable = location.source_name != null and
        conflicting.location.source_name != null and
        std.mem.eql(
            u8,
            location.source_name.?,
            conflicting.location.source_name.?,
        );
    if (comparable and location.start < conflicting.location.start) {
        first = location.*;
        second = conflicting.location;
    }
    var secondary: Diagnostics.SecondarySourceLocation = .{};
    defer secondary.deinit(reporter.allocator);
    try secondary.append(
        reporter.allocator,
        "The previous declaration is here:",
        first,
    );
    try reporter.reportWithSecondary(
        errorId(2333),
        .DeclarationError,
        second,
        &secondary,
        "Identifier already declared.",
    );
    return false;
}

pub fn cThreeMergeAlloc(
    allocator: std.mem.Allocator,
    comptime T: type,
    input: []const []const T,
) std.mem.Allocator.Error![]T {
    var lists: std.ArrayList(std.ArrayList(T)) = .empty;
    defer {
        for (lists.items) |*list| list.deinit(allocator);
        lists.deinit(allocator);
    }
    for (input) |source| {
        if (source.len == 0) continue;
        var list: std.ArrayList(T) = .empty;
        errdefer list.deinit(allocator);
        try list.appendSlice(allocator, source);
        try lists.append(allocator, list);
    }

    var result: std.ArrayList(T) = .empty;
    errdefer result.deinit(allocator);
    while (lists.items.len != 0) {
        var candidate: ?T = null;
        for (lists.items) |list| {
            const head = list.items[0];
            var appears_in_tail = false;
            for (lists.items) |other| {
                for (other.items[1..]) |item|
                    if (std.meta.eql(item, head)) {
                        appears_in_tail = true;
                        break;
                    };
                if (appears_in_tail) break;
            }
            if (!appears_in_tail) {
                candidate = head;
                break;
            }
        }
        const selected = candidate orelse {
            result.clearRetainingCapacity();
            return result.toOwnedSlice(allocator);
        };
        try result.append(allocator, selected);

        var list_index: usize = 0;
        while (list_index < lists.items.len) {
            var item_index: usize = 0;
            while (item_index < lists.items[list_index].items.len) {
                if (std.meta.eql(lists.items[list_index].items[item_index], selected))
                    _ = lists.items[list_index].orderedRemove(item_index)
                else
                    item_index += 1;
            }
            if (lists.items[list_index].items.len == 0) {
                var removed = lists.orderedRemove(list_index);
                removed.deinit(allocator);
            } else {
                list_index += 1;
            }
        }
    }
    return result.toOwnedSlice(allocator);
}

fn isReservedName(name: []const u8) bool {
    return std.mem.eql(u8, name, "_") or
        std.mem.eql(u8, name, "super") or
        std.mem.eql(u8, name, "this");
}

fn isVariableScope(kind: AST.Kind) bool {
    return switch (kind) {
        .function_definition,
        .modifier_definition,
        .event_definition,
        .error_definition,
        => true,
        else => false,
    };
}

fn findSourceUnit(entries: []const SourceUnitEntry, path: []const u8) ?*AST.Node {
    for (entries) |entry|
        if (std.mem.eql(u8, entry.path, path)) return entry.source_unit;
    return null;
}

fn ownNodeSlice(
    tree: *AST.Tree,
    values: []const *const AST.Node,
) std.mem.Allocator.Error!AST.NodeList {
    const owned = try tree.allocator().alloc(*AST.Node, values.len);
    for (values, 0..) |value, index| owned[index] = @constCast(value);
    return owned;
}

fn sourceUnitAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolverError!*ASTAnnotations.SourceUnitAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .source_unit => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn importAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolverError!*ASTAnnotations.ImportAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .import => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn identifierPathAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolverError!*ASTAnnotations.IdentifierPathAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .identifier_path => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn contractAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolverError!*ASTAnnotations.ContractDefinitionAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .contract_definition => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn callableAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolverError!*ASTAnnotations.CallableDeclarationAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .documented_callable => |*annotation| &annotation.callable,
        else => error.InvalidAst,
    };
}

fn typeDeclarationAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolverError!?*ASTAnnotations.TypeDeclarationAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .type_declaration => |*annotation| annotation,
        .struct_declaration => |*annotation| &annotation.type_declaration,
        .contract_definition => |*annotation| &annotation.type_declaration,
        .type_class_definition => |*annotation| &annotation.type_declaration,
        else => null,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "registration creates lexical scopes, canonical names, inactive locals, and globals" {
    const Parser = @import("../parsing/parser.zig");
    const TypeProviderModule = @import("../ast/type_provider.zig");

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { " ++
        "struct S { uint member; } " ++
        "uint value; " ++
        "function ping(uint a) public {} " ++
        "function ping(address a) public {} " ++
        "function f(uint parameter) external { uint value; } " ++
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

    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var global = try GlobalContext.init(
        std.testing.allocator,
        &provider,
        EVMVersion.current(),
    );
    defer global.deinit();
    var resolver = try NameAndTypeResolver.init(
        std.testing.allocator,
        &global,
        EVMVersion.current(),
        &reporter,
        false,
    );
    defer resolver.deinit();
    try std.testing.expect(try resolver.registerSource(&parsed.tree, root));

    const globals = try resolver.resolveNameAlloc(
        std.testing.allocator,
        "require",
        null,
    );
    defer std.testing.allocator.free(globals);
    try std.testing.expectEqual(@as(usize, 3), globals.len);

    const contract = root.payload.source_unit.nodes[0];
    const contract_names = try resolver.resolveNameAlloc(
        std.testing.allocator,
        "C",
        root,
    );
    defer std.testing.allocator.free(contract_names);
    try std.testing.expectEqualSlices(*const AST.Node, &.{contract}, contract_names);

    const members = contract.payload.contract_definition.sub_nodes;
    const structure = members[0];
    const overloads = try resolver.resolveNameAlloc(
        std.testing.allocator,
        "ping",
        contract,
    );
    defer std.testing.allocator.free(overloads);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{ members[2], members[3] },
        overloads,
    );
    const structure_annotation = (try typeDeclarationAnnotation(
        &parsed.tree,
        structure,
    )).?;
    try std.testing.expectEqualStrings(
        "C.S",
        (try structure_annotation.canonical_name.get()).*,
    );

    const function = members[4];
    const body = function.payload.function_definition.body.?;
    const local = body.payload.block.statements[0]
        .payload.variable_declaration_statement.declarations[0].?;
    const hidden = try resolver.resolveNameAlloc(
        std.testing.allocator,
        "value",
        body,
    );
    defer std.testing.allocator.free(hidden);
    try std.testing.expectEqual(@as(usize, 0), hidden.len);
    const function_annotation = try callableAnnotation(&parsed.tree, function);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{local},
        function_annotation.local_variables.items,
    );

    try resolver.setScope(body);
    const recursive_hidden = try resolver.nameFromCurrentScopeAlloc(
        std.testing.allocator,
        "value",
        true,
    );
    defer std.testing.allocator.free(recursive_hidden);
    try std.testing.expectEqualSlices(*const AST.Node, &.{local}, recursive_hidden);
    try resolver.activateVariable("value");
    const active = try resolver.nameFromCurrentScopeAlloc(
        std.testing.allocator,
        "value",
        false,
    );
    defer std.testing.allocator.free(active);
    try std.testing.expectEqualSlices(*const AST.Node, &.{local}, active);

    var rebuilt = try NameAndTypeResolver.init(
        std.testing.allocator,
        &global,
        EVMVersion.current(),
        &reporter,
        false,
    );
    defer rebuilt.deinit();
    try std.testing.expect(try rebuilt.registerSourceReusingAnnotations(
        &parsed.tree,
        root,
    ));
    const rebuilt_members = try rebuilt.resolveNameAlloc(
        std.testing.allocator,
        "ping",
        contract,
    );
    defer std.testing.allocator.free(rebuilt_members);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{ members[2], members[3] },
        rebuilt_members,
    );
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{local},
        function_annotation.local_variables.items,
    );
    try std.testing.expectEqualStrings(
        "C.S",
        (try structure_annotation.canonical_name.get()).*,
    );
}

test "C3 merge preserves Solidity base precedence and reports conflicts as empty" {
    const a: u8 = 1;
    const b: u8 = 2;
    const o: u8 = 3;
    const consistent = [_][]const *const u8{
        &.{ &b, &o },
        &.{ &a, &o },
        &.{ &b, &a },
    };
    const merged = try cThreeMergeAlloc(
        std.testing.allocator,
        *const u8,
        &consistent,
    );
    defer std.testing.allocator.free(merged);
    try std.testing.expectEqualSlices(*const u8, &.{ &b, &a, &o }, merged);

    const impossible = [_][]const *const u8{
        &.{ &a, &b },
        &.{ &b, &a },
    };
    const failed = try cThreeMergeAlloc(
        std.testing.allocator,
        *const u8,
        &impossible,
    );
    defer std.testing.allocator.free(failed);
    try std.testing.expectEqual(@as(usize, 0), failed.len);
}

test "imports preserve aliases, unit paths, and exported symbol ownership" {
    const Parser = @import("../parsing/parser.zig");
    const TypeProviderModule = @import("../ast/type_provider.zig");

    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var imported = try Parser.parseSource(
        std.testing.allocator,
        "// SPDX-License-Identifier: UNLICENSED\nstruct Shared { uint value; }",
        "B.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer imported.deinit();
    var importer = try Parser.parseSource(
        std.testing.allocator,
        "// SPDX-License-Identifier: UNLICENSED\n" ++
            "import {Shared as Alias} from \"B.sol\"; " ++
            "import \"B.sol\" as Unit;",
        "A.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer importer.deinit();
    try std.testing.expect(!reporter.hasErrors());
    const imported_root = imported.tree.root.?;
    const importer_root = importer.tree.root.?;
    try Scoper.assignScopes(&imported.tree, imported_root);
    try Scoper.assignScopes(&importer.tree, importer_root);

    for (importer_root.payload.source_unit.nodes) |node| {
        const annotation = try importAnnotation(&importer.tree, node);
        try annotation.absolute_path.assign("B.sol");
        annotation.source_unit = imported_root;
    }

    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var global = try GlobalContext.init(
        std.testing.allocator,
        &provider,
        EVMVersion.current(),
    );
    defer global.deinit();
    var resolver = try NameAndTypeResolver.init(
        std.testing.allocator,
        &global,
        EVMVersion.current(),
        &reporter,
        false,
    );
    defer resolver.deinit();
    try std.testing.expect(try resolver.registerSource(&imported.tree, imported_root));
    try std.testing.expect(try resolver.registerSource(&importer.tree, importer_root));
    try std.testing.expect(try resolver.performImports(
        &importer.tree,
        importer_root,
        &.{.{ .path = "B.sol", .source_unit = imported_root }},
    ));

    const shared = imported_root.payload.source_unit.nodes[0];
    const alias = try resolver.resolveNameAlloc(
        std.testing.allocator,
        "Alias",
        importer_root,
    );
    defer std.testing.allocator.free(alias);
    try std.testing.expectEqualSlices(*const AST.Node, &.{shared}, alias);

    try resolver.setScope(importer_root);
    const path = try resolver.pathFromCurrentScopeAlloc(
        std.testing.allocator,
        &.{ "Unit", "Shared" },
        false,
    );
    defer std.testing.allocator.free(path);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{ importer_root.payload.source_unit.nodes[1], shared },
        path,
    );

    const source_annotation = try sourceUnitAnnotation(&importer.tree, importer_root);
    const exported = (try source_annotation.exported_symbols.get()).*;
    try std.testing.expectEqual(@as(usize, 2), exported.len);
    try std.testing.expectEqualStrings("Alias", exported[0].name);
    try std.testing.expectEqualStrings("Unit", exported[1].name);

    var rebuilt = try NameAndTypeResolver.init(
        std.testing.allocator,
        &global,
        EVMVersion.current(),
        &reporter,
        false,
    );
    defer rebuilt.deinit();
    try std.testing.expect(try rebuilt.registerSourceReusingAnnotations(
        &imported.tree,
        imported_root,
    ));
    try std.testing.expect(try rebuilt.registerSourceReusingAnnotations(
        &importer.tree,
        importer_root,
    ));
    try std.testing.expect(try rebuilt.performImportsReusingAnnotations(
        &importer.tree,
        importer_root,
        &.{.{ .path = "B.sol", .source_unit = imported_root }},
    ));
    const rebuilt_alias = try rebuilt.resolveNameAlloc(
        std.testing.allocator,
        "Alias",
        importer_root,
    );
    defer std.testing.allocator.free(rebuilt_alias);
    try std.testing.expectEqualSlices(*const AST.Node, &.{shared}, rebuilt_alias);
    try std.testing.expect(
        (try source_annotation.exported_symbols.get()).*.ptr == exported.ptr,
    );
}

test "contract C3 linearization stores reverse base precedence in the syntax arena" {
    const Parser = @import("../parsing/parser.zig");
    const TypeProviderModule = @import("../ast/type_provider.zig");

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract A {} contract B is A {} contract C is A {} contract D is B, C {}";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Linearization.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    try std.testing.expect(!reporter.hasErrors());
    const root = parsed.tree.root.?;
    try Scoper.assignScopes(&parsed.tree, root);

    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var global = try GlobalContext.init(
        std.testing.allocator,
        &provider,
        EVMVersion.current(),
    );
    defer global.deinit();
    var resolver = try NameAndTypeResolver.init(
        std.testing.allocator,
        &global,
        EVMVersion.current(),
        &reporter,
        false,
    );
    defer resolver.deinit();
    try std.testing.expect(try resolver.registerSource(&parsed.tree, root));

    const contracts = root.payload.source_unit.nodes;
    for (contracts, 0..) |contract, contract_index| {
        for (contract.payload.contract_definition.base_contracts) |specifier| {
            const base_name = specifier.payload.inheritance_specifier.base_name;
            const name = base_name.payload.identifier_path.path[0];
            var referenced: ?*AST.Node = null;
            for (contracts[0..contract_index]) |candidate|
                if (std.mem.eql(
                    u8,
                    candidate.payload.contract_definition.declaration.name,
                    name,
                )) {
                    referenced = candidate;
                    break;
                };
            (try identifierPathAnnotation(&parsed.tree, base_name)).referenced_declaration =
                referenced orelse return error.TestUnexpectedResult;
        }
        try resolver.linearizeBaseContracts(&parsed.tree, contract);
    }

    const d_linearized = (try contractAnnotation(&parsed.tree, contracts[3]))
        .linearized_base_contracts;
    try std.testing.expectEqualSlices(
        *AST.Node,
        &.{ contracts[3], contracts[2], contracts[1], contracts[0] },
        d_linearized,
    );
}
