// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Reference binding translated from `ReferencesResolver.cpp`.
//!
//! This pass binds Solidity identifiers and identifier paths, preserves C99
//! local-variable activation order, links returns to their callable, resolves
//! `@inheritdoc`, and records Solidity references from inline Yul. It borrows
//! the syntax tree and `NameAndTypeResolver`; annotation buffers are allocated
//! in the syntax tree's arena.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const NameResolverModule = @import("name_and_type_resolver.zig");
const NameAndTypeResolver = NameResolverModule.NameAndTypeResolver;
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;
const YulAST = @import("../../libyul/ast.zig");

pub const ResolveError = NameResolverModule.ResolverError ||
    error{InvalidYulStringHandle};

const Action = union(enum) {
    enter: *AST.Node,
    leave: *AST.Node,
    set_type_context: bool,
};

pub const ReferencesResolver = struct {
    tree: *AST.Tree,
    reporter: *Diagnostics.ErrorReporter,
    resolver: *NameAndTypeResolver,
    evm_version: EVMVersion,
    resolve_inside_code: bool,
    function_definitions: std.ArrayList(?*const AST.Node) = .empty,
    actions: std.ArrayList(Action) = .empty,
    yul_annotation: ?*ASTAnnotations.InlineAssemblyAnnotation = null,
    yul_inside_function: bool = false,
    type_context: bool = false,

    pub fn init(
        tree: *AST.Tree,
        reporter: *Diagnostics.ErrorReporter,
        resolver: *NameAndTypeResolver,
        evm_version: EVMVersion,
        resolve_inside_code: bool,
    ) ReferencesResolver {
        return .{
            .tree = tree,
            .reporter = reporter,
            .resolver = resolver,
            .evm_version = evm_version,
            .resolve_inside_code = resolve_inside_code,
        };
    }

    pub fn deinit(self: *ReferencesResolver) void {
        self.function_definitions.deinit(self.tree.backing_allocator);
        self.actions.deinit(self.tree.backing_allocator);
        self.* = undefined;
    }

    pub fn resolve(self: *ReferencesResolver, root: *AST.Node) ResolveError!bool {
        const watcher = self.reporter.errorWatcher();
        try self.actions.append(
            self.tree.backing_allocator,
            .{ .enter = root },
        );
        while (self.actions.pop()) |action| switch (action) {
            .enter => |node| try self.enter(node),
            .leave => |node| try self.leave(node),
            .set_type_context => |value| self.type_context = value,
        };
        if (self.function_definitions.items.len != 0 or self.yul_annotation != null)
            return error.InvalidAst;
        return watcher.ok();
    }

    fn enter(self: *ReferencesResolver, node: *AST.Node) ResolveError!void {
        switch (node.payload) {
            .block => {
                try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                if (!self.resolve_inside_code) return;
                try self.resolver.setScope(node);
                return self.scheduleGenericChildren(node);
            },
            .try_catch_clause => {
                try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                if (!self.resolve_inside_code) return;
                try self.resolver.setScope(node);
                return self.scheduleGenericChildren(node);
            },
            .for_statement => {
                try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                if (!self.resolve_inside_code) return;
                try self.resolver.setScope(node);
                return self.scheduleGenericChildren(node);
            },
            .variable_declaration => |value| {
                if (value.documentation) |documentation|
                    try self.resolveInheritDoc(
                        documentation,
                        try variableDocumentedAnnotation(self.tree, node),
                    );
                if (self.resolver.experimentalSolidity()) {
                    if (value.type_name != null) return error.InvalidAst;
                    try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                    if (value.value) |child|
                        try self.actions.append(self.tree.backing_allocator, .{ .enter = child });
                    if (value.overrides) |child|
                        try self.actions.append(self.tree.backing_allocator, .{ .enter = child });
                    if (value.experimental_type_expression) |child| {
                        try self.actions.append(
                            self.tree.backing_allocator,
                            .{ .set_type_context = self.type_context },
                        );
                        try self.actions.append(self.tree.backing_allocator, .{ .enter = child });
                        try self.actions.append(
                            self.tree.backing_allocator,
                            .{ .set_type_context = true },
                        );
                    }
                    return;
                }
            },
            .identifier => {
                try self.resolveIdentifier(node);
                try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                return;
            },
            .function_definition => |value| {
                try self.function_definitions.append(self.tree.backing_allocator, node);
                if (value.documentation) |documentation|
                    try self.resolveInheritDoc(
                        documentation,
                        try callableDocumentedAnnotation(self.tree, node),
                    );
            },
            .modifier_definition => |value| {
                try self.function_definitions.append(self.tree.backing_allocator, null);
                if (value.documentation) |documentation|
                    try self.resolveInheritDoc(
                        documentation,
                        try callableDocumentedAnnotation(self.tree, node),
                    );
            },
            .using_for_directive => {
                try self.resolveUsingFor(node);
                try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                if (node.payload.using_for_directive.type_name) |type_name|
                    try self.actions.append(
                        self.tree.backing_allocator,
                        .{ .enter = type_name },
                    );
                return;
            },
            .inline_assembly => {
                try self.resolveInlineAssembly(node);
                try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                return;
            },
            .return_statement => {
                try self.resolveReturn(node);
            },
            .binary_operation => |value| {
                if (self.resolver.experimentalSolidity()) {
                    try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
                    if (value.operator == .Colon) {
                        try self.actions.append(
                            self.tree.backing_allocator,
                            .{ .set_type_context = self.type_context },
                        );
                        try self.actions.append(
                            self.tree.backing_allocator,
                            .{ .enter = value.right },
                        );
                        try self.actions.append(
                            self.tree.backing_allocator,
                            .{ .set_type_context = !self.type_context },
                        );
                    } else {
                        try self.actions.append(
                            self.tree.backing_allocator,
                            .{ .enter = value.right },
                        );
                    }
                    try self.actions.append(
                        self.tree.backing_allocator,
                        .{ .enter = value.left },
                    );
                    return;
                }
            },
            else => {},
        }

        try self.actions.append(self.tree.backing_allocator, .{ .leave = node });
        try self.scheduleGenericChildren(node);
    }

    fn leave(self: *ReferencesResolver, node: *AST.Node) ResolveError!void {
        switch (node.payload) {
            .block, .try_catch_clause, .for_statement => {
                if (self.resolve_inside_code) {
                    const parent = ASTImplementation.scope(node) orelse
                        return error.InvalidAst;
                    try self.resolver.setScope(parent);
                }
            },
            .variable_declaration_statement => |value| {
                if (self.resolve_inside_code)
                    for (value.declarations) |declaration|
                        if (declaration) |present|
                            try self.resolver.activateVariable(
                                present.payload.variable_declaration.declaration.name,
                            );
            },
            .function_definition, .modifier_definition => {
                const callable = self.function_definitions.pop() orelse
                    return error.InvalidAst;
                switch (node.nodeKind()) {
                    .function_definition => if (callable == null or callable.? != node)
                        return error.InvalidAst,
                    .modifier_definition => if (callable != null)
                        return error.InvalidAst,
                    else => unreachable,
                }
            },
            .identifier_path => try self.resolveIdentifierPath(node, false, null),
            else => {},
        }
    }

    fn scheduleGenericChildren(
        self: *ReferencesResolver,
        node: *const AST.Node,
    ) ResolveError!void {
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.tree.backing_allocator);
        try ASTImplementation.appendChildren(
            self.tree.backing_allocator,
            &children,
            node,
        );
        var index = children.items.len;
        while (index != 0) {
            index -= 1;
            try self.actions.append(self.tree.backing_allocator, .{
                .enter = @constCast(children.items[index]),
            });
        }
    }

    fn resolveIdentifier(self: *ReferencesResolver, node: *AST.Node) ResolveError!void {
        const name = node.payload.identifier.name;
        const declarations = try self.resolver.nameFromCurrentScopeAlloc(
            self.tree.backing_allocator,
            name,
            false,
        );
        defer self.tree.backing_allocator.free(declarations);
        const annotation = try identifierAnnotation(self.tree, node);
        annotation.referenced_declaration = null;
        annotation.candidate_declarations.clearRetainingCapacity();

        if (declarations.len == 0) {
            if (self.resolver.experimentalSolidity() and self.type_context) return;
            const suggestions = try self.resolver.similarNameSuggestionsAlloc(
                self.tree.backing_allocator,
                name,
            );
            defer self.tree.backing_allocator.free(suggestions);
            var message: []u8 = undefined;
            if (suggestions.len == 0) {
                message = try self.tree.backing_allocator.dupe(
                    u8,
                    "Undeclared identifier.",
                );
            } else {
                const exact = try std.fmt.allocPrint(
                    self.tree.backing_allocator,
                    "\"{s}\"",
                    .{name},
                );
                defer self.tree.backing_allocator.free(exact);
                message = if (std.mem.eql(u8, exact, suggestions))
                    try std.fmt.allocPrint(
                        self.tree.backing_allocator,
                        "Undeclared identifier. {s} is not (or not yet) visible at this point.",
                        .{suggestions},
                    )
                else
                    try std.fmt.allocPrint(
                        self.tree.backing_allocator,
                        "Undeclared identifier. Did you mean {s}?",
                        .{suggestions},
                    );
            }
            defer self.tree.backing_allocator.free(message);
            try self.reporter.declarationError(errorId(7576), node.location, message);
        } else if (declarations.len == 1) {
            annotation.referenced_declaration = declarations[0];
        } else {
            try annotation.candidate_declarations.appendSlice(
                self.tree.allocator(),
                declarations,
            );
        }
    }

    fn resolveIdentifierPath(
        self: *ReferencesResolver,
        node: *AST.Node,
        include_invisibles: bool,
        custom_error: ?[]const u8,
    ) ResolveError!void {
        const path = node.payload.identifier_path.path;
        const declarations = try self.resolver.pathFromCurrentScopeAlloc(
            self.tree.backing_allocator,
            path,
            include_invisibles,
        );
        defer self.tree.backing_allocator.free(declarations);
        if (declarations.len == 0) {
            try self.reporter.fatal(
                errorId(if (custom_error == null) 7920 else 9589),
                .DeclarationError,
                node.location,
                null,
                custom_error orelse "Identifier not found or not unique.",
            );
        }

        const annotation = try identifierPathAnnotation(self.tree, node);
        annotation.referenced_declaration = declarations[declarations.len - 1];
        annotation.path_declarations.clearRetainingCapacity();
        try annotation.path_declarations.appendSlice(
            self.tree.allocator(),
            declarations,
        );
    }

    fn resolveUsingFor(self: *ReferencesResolver, node: *AST.Node) ResolveError!void {
        const using_for = node.payload.using_for_directive;
        for (using_for.functions_and_operators) |entry| {
            const path = entry.function_or_library;
            if (path.nodeKind() != .identifier_path) return error.InvalidAst;
            try self.resolveIdentifierPath(
                path,
                true,
                if (using_for.uses_braces)
                    "Identifier is not a function name or not unique."
                else
                    "Identifier is not a library name.",
            );
        }
    }

    fn resolveReturn(self: *ReferencesResolver, node: *AST.Node) ResolveError!void {
        if (self.function_definitions.items.len == 0) return error.InvalidAst;
        const function = self.function_definitions.items[
            self.function_definitions.items.len - 1
        ];
        const annotation = try returnAnnotation(self.tree, node);
        annotation.function = function;
        annotation.function_return_parameters = if (function) |definition|
            definition.payload.function_definition.callable.return_parameters
        else
            null;
    }

    fn resolveInheritDoc(
        self: *ReferencesResolver,
        documentation: *AST.Node,
        annotation: *ASTAnnotations.StructurallyDocumentedAnnotation,
    ) ResolveError!void {
        var count: usize = 0;
        var content: []const u8 = "";
        for (annotation.doc_tags.items) |entry|
            if (std.mem.eql(u8, entry.name, "inheritdoc")) {
                count += 1;
                content = entry.tag.content;
            };
        if (count == 0) return;
        if (count > 1) {
            try self.reporter.docstringParsingError(
                errorId(5142),
                documentation.location,
                "Documentation tag @inheritdoc can only be given once.",
            );
            return;
        }
        if (content.len == 0) {
            try self.reporter.docstringParsingError(
                errorId(1933),
                documentation.location,
                "Expected contract name following documentation tag @inheritdoc.",
            );
            return;
        }

        var path: std.ArrayList([]const u8) = .empty;
        defer path.deinit(self.tree.backing_allocator);
        var iterator = std.mem.splitScalar(u8, content, '.');
        while (iterator.next()) |component| {
            if (component.len == 0) {
                const message = try std.fmt.allocPrint(
                    self.tree.backing_allocator,
                    "Documentation tag @inheritdoc reference \"{s}\" is malformed.",
                    .{content},
                );
                defer self.tree.backing_allocator.free(message);
                try self.reporter.docstringParsingError(
                    errorId(5967),
                    documentation.location,
                    message,
                );
                return;
            }
            try path.append(self.tree.backing_allocator, component);
        }

        const declarations = try self.resolver.pathFromCurrentScopeAlloc(
            self.tree.backing_allocator,
            path.items,
            false,
        );
        defer self.tree.backing_allocator.free(declarations);
        if (declarations.len == 0) {
            const message = try std.fmt.allocPrint(
                self.tree.backing_allocator,
                "Documentation tag @inheritdoc references inexistent contract \"{s}\".",
                .{content},
            );
            defer self.tree.backing_allocator.free(message);
            try self.reporter.docstringParsingError(
                errorId(9397),
                documentation.location,
                message,
            );
            return;
        }
        const result = declarations[declarations.len - 1];
        if (result.nodeKind() != .contract_definition) {
            const message = try std.fmt.allocPrint(
                self.tree.backing_allocator,
                "Documentation tag @inheritdoc reference \"{s}\" is not a contract.",
                .{content},
            );
            defer self.tree.backing_allocator.free(message);
            try self.reporter.docstringParsingError(
                errorId(1430),
                documentation.location,
                message,
            );
            return;
        }
        annotation.inheritdoc_reference = result;
    }

    fn resolveInlineAssembly(
        self: *ReferencesResolver,
        node: *AST.Node,
    ) ResolveError!void {
        if (self.yul_annotation != null) return error.InvalidAst;
        const annotation = try inlineAssemblyAnnotation(self.tree, node);
        self.yul_annotation = annotation;
        defer self.yul_annotation = null;
        const operations = node.payload.inline_assembly.operations orelse
            return error.InvalidAst;
        try self.walkYul(operations.root());
    }

    fn walkYul(self: *ReferencesResolver, root: *const YulAST.Block) ResolveError!void {
        const YulAction = union(enum) {
            block: *const YulAST.Block,
            statement: *const YulAST.Statement,
            expression: *const YulAST.Expression,
            identifier: *const YulAST.Identifier,
            function_enter: *const YulAST.FunctionDefinition,
            function_leave: bool,
        };
        var actions: std.ArrayList(YulAction) = .empty;
        defer actions.deinit(self.tree.backing_allocator);
        try actions.append(self.tree.backing_allocator, .{ .block = root });

        while (actions.pop()) |action| switch (action) {
            .block => |block| {
                var index = block.statements.items.len;
                while (index != 0) {
                    index -= 1;
                    try actions.append(self.tree.backing_allocator, .{
                        .statement = &block.statements.items[index],
                    });
                }
            },
            .statement => |statement| switch (statement.*) {
                .expression_statement => |*value| try actions.append(
                    self.tree.backing_allocator,
                    .{ .expression = &value.expression },
                ),
                .assignment => |*value| {
                    if (value.value) |expression|
                        try actions.append(
                            self.tree.backing_allocator,
                            .{ .expression = expression },
                        );
                    var index = value.variable_names.items.len;
                    while (index != 0) {
                        index -= 1;
                        try actions.append(self.tree.backing_allocator, .{
                            .identifier = &value.variable_names.items[index],
                        });
                    }
                },
                .variable_declaration => |*value| {
                    try self.resolveYulVariableDeclaration(value);
                    if (value.value) |expression|
                        try actions.append(
                            self.tree.backing_allocator,
                            .{ .expression = expression },
                        );
                },
                .function_definition => |*value| try actions.append(
                    self.tree.backing_allocator,
                    .{ .function_enter = value },
                ),
                .if_statement => |*value| {
                    try actions.append(self.tree.backing_allocator, .{ .block = &value.body });
                    if (value.condition) |expression|
                        try actions.append(
                            self.tree.backing_allocator,
                            .{ .expression = expression },
                        );
                },
                .switch_statement => |*value| {
                    var index = value.cases.items.len;
                    while (index != 0) {
                        index -= 1;
                        const case_value = &value.cases.items[index];
                        try actions.append(
                            self.tree.backing_allocator,
                            .{ .block = &case_value.body },
                        );
                    }
                    if (value.expression) |expression|
                        try actions.append(
                            self.tree.backing_allocator,
                            .{ .expression = expression },
                        );
                },
                .for_loop => |*value| {
                    try actions.append(self.tree.backing_allocator, .{ .block = &value.post });
                    try actions.append(self.tree.backing_allocator, .{ .block = &value.body });
                    if (value.condition) |expression|
                        try actions.append(
                            self.tree.backing_allocator,
                            .{ .expression = expression },
                        );
                    try actions.append(self.tree.backing_allocator, .{ .block = &value.pre });
                },
                .block => |*value| try actions.append(
                    self.tree.backing_allocator,
                    .{ .block = value },
                ),
                .break_statement,
                .continue_statement,
                .leave_statement,
                => {},
            },
            .expression => |expression| switch (expression.*) {
                .identifier => |*identifier| try actions.append(
                    self.tree.backing_allocator,
                    .{ .identifier = identifier },
                ),
                .function_call => |*call| {
                    // Upstream deliberately visits function arguments in
                    // reverse order and does not visit the function name.
                    for (call.arguments.items) |*argument|
                        try actions.append(
                            self.tree.backing_allocator,
                            .{ .expression = argument },
                        );
                },
                .literal => {},
            },
            .identifier => |identifier| try self.resolveYulIdentifier(identifier),
            .function_enter => |function| {
                try self.validateYulIdentifierName(
                    try function.name.str(),
                    try yulLocation(function.debug_data),
                );
                for (function.parameters.items) |parameter|
                    try self.validateYulIdentifierName(
                        try parameter.name.str(),
                        try yulLocation(parameter.debug_data),
                    );
                for (function.return_variables.items) |parameter|
                    try self.validateYulIdentifierName(
                        try parameter.name.str(),
                        try yulLocation(parameter.debug_data),
                    );
                const previous = self.yul_inside_function;
                self.yul_inside_function = true;
                try actions.append(
                    self.tree.backing_allocator,
                    .{ .function_leave = previous },
                );
                try actions.append(
                    self.tree.backing_allocator,
                    .{ .block = &function.body },
                );
            },
            .function_leave => |previous| self.yul_inside_function = previous,
        };
    }

    fn resolveYulIdentifier(
        self: *ReferencesResolver,
        identifier: *const YulAST.Identifier,
    ) ResolveError!void {
        const location = try yulLocation(identifier.debug_data);
        const full_name = try identifier.name.str();

        if (self.resolver.experimentalSolidity()) {
            var split = std.mem.splitScalar(u8, full_name, '.');
            const first = split.next() orelse return error.InvalidAst;
            const second = split.next();
            if (split.next() != null) {
                try self.reporter.declarationError(
                    errorId(4955),
                    location,
                    "Unsupported identifier in inline assembly.",
                );
                return;
            }
            const declarations = try self.resolver.nameFromCurrentScopeAlloc(
                self.tree.backing_allocator,
                first,
                false,
            );
            defer self.tree.backing_allocator.free(declarations);
            if (declarations.len == 0) {
                if (second != null)
                    try self.reporter.declarationError(
                        errorId(7531),
                        location,
                        "Unsupported identifier in inline assembly.",
                    );
            } else if (declarations.len == 1) {
                try self.setYulExternalReference(
                    identifier,
                    declarations[0],
                    second orelse "",
                );
            } else {
                try self.reporter.declarationError(
                    errorId(5387),
                    location,
                    "Multiple matching identifiers. Resolving overloaded identifiers is not supported.",
                );
            }
            return;
        }

        var suffix: []const u8 = "";
        const suffixes = [_][]const u8{ "address", "length", "offset", "selector", "slot" };
        for (suffixes) |candidate|
            if (std.mem.endsWith(u8, full_name, candidate) and
                full_name.len > candidate.len and
                full_name[full_name.len - candidate.len - 1] == '.')
            {
                suffix = candidate;
                break;
            };

        var declarations = try self.resolver.nameFromCurrentScopeAlloc(
            self.tree.backing_allocator,
            full_name,
            false,
        );
        defer self.tree.backing_allocator.free(declarations);
        if (suffix.len != 0) {
            if (declarations.len != 0) return;
            const real_name = full_name[0 .. full_name.len - suffix.len - 1];
            if (real_name.len == 0 or std.mem.findScalar(u8, real_name, '.') != null)
                return error.InvalidAst;
            self.tree.backing_allocator.free(declarations);
            declarations = try self.resolver.nameFromCurrentScopeAlloc(
                self.tree.backing_allocator,
                real_name,
                false,
            );
        }

        if (declarations.len > 1) {
            try self.reporter.declarationError(
                errorId(4718),
                location,
                "Multiple matching identifiers. Resolving overloaded identifiers is not supported.",
            );
            return;
        }
        if (declarations.len == 0) {
            if (std.mem.endsWith(u8, full_name, "_slot") or
                std.mem.endsWith(u8, full_name, "_offset"))
                try self.reporter.declarationError(
                    errorId(9467),
                    location,
                    "Identifier not found. Use \".slot\" and \".offset\" to access storage or transient storage variables.",
                );
            return;
        }
        if (ASTImplementation.isLocalVariable(declarations[0]) and
            self.yul_inside_function)
        {
            try self.reporter.declarationError(
                errorId(6578),
                location,
                "Cannot access local Solidity variables from inside an inline assembly function.",
            );
            return;
        }
        try self.setYulExternalReference(identifier, declarations[0], suffix);
    }

    fn resolveYulVariableDeclaration(
        self: *ReferencesResolver,
        declaration: *const YulAST.VariableDeclaration,
    ) ResolveError!void {
        for (declaration.variables.items) |variable| {
            const location = try yulLocation(variable.debug_data);
            const name = try variable.name.str();
            try self.validateYulIdentifierName(name, location);
            const declarations = try self.resolver.nameFromCurrentScopeAlloc(
                self.tree.backing_allocator,
                name,
                false,
            );
            defer self.tree.backing_allocator.free(declarations);
            if (declarations.len == 0) continue;
            var secondary: Diagnostics.SecondarySourceLocation = .{};
            defer secondary.deinit(self.tree.backing_allocator);
            for (declarations) |shadowed|
                try secondary.append(
                    self.tree.backing_allocator,
                    "The shadowed declaration is here:",
                    shadowed.location,
                );
            try self.reporter.reportWithSecondary(
                errorId(3859),
                .DeclarationError,
                location,
                &secondary,
                "This declaration shadows a declaration outside the inline assembly block.",
            );
        }
    }

    fn setYulExternalReference(
        self: *ReferencesResolver,
        identifier: *const YulAST.Identifier,
        declaration: *const AST.Node,
        suffix: []const u8,
    ) ResolveError!void {
        const annotation = self.yul_annotation orelse return error.InvalidAst;
        const identity: ASTAnnotations.YulIdentifierRef = identifier;
        for (annotation.external_references.items) |*reference|
            if (reference.identifier == identity) {
                reference.info.declaration = declaration;
                reference.info.suffix = suffix;
                return;
            };
        try annotation.external_references.append(self.tree.allocator(), .{
            .identifier = identity,
            .info = .{
                .declaration = declaration,
                .suffix = suffix,
            },
        });
    }

    fn validateYulIdentifierName(
        self: *ReferencesResolver,
        name: []const u8,
        location: SourceLocation,
    ) ResolveError!void {
        if (std.mem.findScalar(u8, name, '.') != null)
            try self.reporter.declarationError(
                errorId(3927),
                location,
                "User-defined identifiers in inline assembly cannot contain '.'.",
            );
        if (std.mem.eql(u8, name, "this") or
            std.mem.eql(u8, name, "super") or
            std.mem.eql(u8, name, "_"))
        {
            const message = try std.fmt.allocPrint(
                self.tree.backing_allocator,
                "The identifier name \"{s}\" is reserved.",
                .{name},
            );
            defer self.tree.backing_allocator.free(message);
            try self.reporter.declarationError(errorId(4113), location, message);
        }
    }
};

/// Runs the two-phase contract reference pass used by
/// `NameAndTypeResolver::resolveNamesAndTypes` upstream.
pub fn resolveSource(
    tree: *AST.Tree,
    resolver: *NameAndTypeResolver,
    source_unit: *AST.Node,
) ResolveError!bool {
    if (source_unit.nodeKind() != .source_unit) return error.InvalidAst;
    var success = true;
    for (source_unit.payload.source_unit.nodes) |node| {
        try resolver.setScope(source_unit);
        if (!(try resolveNode(tree, resolver, node, true))) {
            success = false;
        }
    }
    return success;
}

fn resolveNode(
    tree: *AST.Tree,
    resolver: *NameAndTypeResolver,
    node: *AST.Node,
    resolve_inside_code: bool,
) ResolveError!bool {
    if (node.nodeKind() == .contract_definition)
        return resolveContract(tree, resolver, node);
    if (resolver.containsScope(node)) try resolver.setScope(node);
    var references = ReferencesResolver.init(
        tree,
        resolver.reporter,
        resolver,
        resolver.evm_version,
        resolve_inside_code,
    );
    defer references.deinit();
    return references.resolve(node);
}

fn resolveContract(
    tree: *AST.Tree,
    resolver: *NameAndTypeResolver,
    contract: *AST.Node,
) ResolveError!bool {
    const parent_scope = ASTImplementation.scope(contract) orelse return error.InvalidAst;
    try resolver.setScope(parent_scope);
    resolver.global_context.setCurrentContract(contract);
    var context_active = true;
    defer if (context_active) resolver.global_context.resetCurrentContract();

    if (contract.payload.contract_definition.contract_kind != .Library) {
        if (!(try resolver.updateDeclaration(
            try resolver.global_context.currentSuper(),
            false,
        ))) return error.InvalidGlobalDeclaration;
    }
    if (!(try resolver.updateDeclaration(
        try resolver.global_context.currentThis(),
        false,
    ))) return error.InvalidGlobalDeclaration;

    var success = true;
    for (contract.payload.contract_definition.base_contracts) |base| {
        if (!(try resolveNode(tree, resolver, base, true))) {
            success = false;
        }
    }
    if (contract.payload.contract_definition.storage_layout_specifier) |layout| {
        if (!(try resolveNode(tree, resolver, layout, true))) {
            success = false;
        }
    }

    try resolver.setScope(contract);
    if (success) {
        try resolver.linearizeBaseContracts(tree, contract);
        const linearized = (try contractAnnotation(tree, contract)).linearized_base_contracts;
        for (linearized[1..]) |base| try resolver.importInheritedScope(base);
    }

    for (contract.payload.contract_definition.sub_nodes) |node| {
        try resolver.setScope(contract);
        if (!(try resolveNode(tree, resolver, node, false))) {
            success = false;
        }
    }
    if (success) {
        for (contract.payload.contract_definition.sub_nodes) |node| {
            try resolver.setScope(contract);
            if (!(try resolveNode(tree, resolver, node, true))) {
                success = false;
            }
        }
    }

    if (!(try resolver.updateDeclaration(
        try resolver.global_context.currentThis(),
        true,
    ))) return error.InvalidGlobalDeclaration;
    if (!(try resolver.updateDeclaration(
        try resolver.global_context.currentSuper(),
        true,
    ))) return error.InvalidGlobalDeclaration;
    resolver.global_context.resetCurrentContract();
    context_active = false;
    return success;
}

fn yulLocation(debug_data: ?@import("../../liblangutil/debug_data.zig").DebugData) ResolveError!SourceLocation {
    const debug = debug_data orelse return SourceLocation{};
    if (!debug.native_location.eql(debug.origin_location)) return error.InvalidAst;
    return debug.native_location;
}

fn identifierAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolveError!*ASTAnnotations.IdentifierAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .identifier => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn identifierPathAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolveError!*ASTAnnotations.IdentifierPathAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .identifier_path => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn returnAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolveError!*ASTAnnotations.ReturnAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .return_statement => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn inlineAssemblyAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolveError!*ASTAnnotations.InlineAssemblyAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .inline_assembly => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn callableDocumentedAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolveError!*ASTAnnotations.StructurallyDocumentedAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .documented_callable => |*annotation| &annotation.documented,
        else => error.InvalidAst,
    };
}

fn variableDocumentedAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolveError!*ASTAnnotations.StructurallyDocumentedAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .variable_declaration => |*annotation| &annotation.documented,
        else => error.InvalidAst,
    };
}

fn contractAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) ResolveError!*ASTAnnotations.ContractDefinitionAnnotation {
    const value = try ASTAnnotations.ensure(tree, node);
    return switch (value.*) {
        .contract_definition => |*annotation| annotation,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "reference resolution binds paths, overload candidates, locals, returns, and inline Yul" {
    const Parser = @import("../parsing/parser.zig");
    const Scoper = @import("scoper.zig");
    const TypeProviderModule = @import("../ast/type_provider.zig");
    const GlobalContext = @import("global_context.zig").GlobalContext;

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { " ++
        "struct S { uint member; } " ++
        "uint state; " ++
        "function ping(uint x) public {} " ++
        "function ping(address x) public {} " ++
        "function f(S memory item, uint arg) public returns (uint out) { " ++
        "uint local = state; ping(arg); assembly { let x := state.slot } return local; " ++
        "} }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "References.sol",
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
    try std.testing.expect(try resolveSource(&parsed.tree, &resolver, root));
    try std.testing.expect(!reporter.hasErrors());

    const contract = root.payload.source_unit.nodes[0];
    const members = contract.payload.contract_definition.sub_nodes;
    const structure = members[0];
    const function = members[4];
    const parameters = function.payload.function_definition.callable.parameters
        .payload.parameter_list.parameters;
    const type_path = parameters[0].payload.variable_declaration.type_name.?
        .payload.user_defined_type_name.path_node;
    try std.testing.expect(
        (try identifierPathAnnotation(&parsed.tree, type_path)).referenced_declaration ==
            structure,
    );

    const statements = function.payload.function_definition.body.?.payload.block.statements;
    const state_identifier = statements[0].payload.variable_declaration_statement
        .initial_value.?;
    try std.testing.expect(
        (try identifierAnnotation(&parsed.tree, state_identifier)).referenced_declaration ==
            members[1],
    );
    const call = statements[1].payload.expression_statement.expression;
    const ping_identifier = call.payload.function_call.expression;
    try std.testing.expectEqual(
        @as(usize, 2),
        (try identifierAnnotation(&parsed.tree, ping_identifier))
            .candidate_declarations.items.len,
    );

    const inline_assembly = statements[2];
    const assembly_annotation = try inlineAssemblyAnnotation(&parsed.tree, inline_assembly);
    try std.testing.expectEqual(@as(usize, 1), assembly_annotation.external_references.items.len);
    try std.testing.expect(
        assembly_annotation.external_references.items[0].info.declaration == members[1],
    );
    try std.testing.expectEqualStrings(
        "slot",
        assembly_annotation.external_references.items[0].info.suffix,
    );

    const return_statement = statements[3];
    const return_annotation = try returnAnnotation(&parsed.tree, return_statement);
    try std.testing.expect(return_annotation.function == function);
    try std.testing.expect(
        return_annotation.function_return_parameters ==
            function.payload.function_definition.callable.return_parameters,
    );
    const local = statements[0].payload.variable_declaration_statement.declarations[0].?;
    const returned = return_statement.payload.return_statement.expression.?;
    try std.testing.expect(
        (try identifierAnnotation(&parsed.tree, returned)).referenced_declaration == local,
    );
}

test "reference resolution reports a local used before C99 activation" {
    const Parser = @import("../parsing/parser.zig");
    const Scoper = @import("scoper.zig");
    const TypeProviderModule = @import("../ast/type_provider.zig");
    const GlobalContext = @import("global_context.zig").GlobalContext;

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { function f() public { uint local = local; } }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Activation.sol",
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
    _ = try resolver.registerSource(&parsed.tree, root);
    try std.testing.expect(!(try resolveSource(&parsed.tree, &resolver, root)));
    try std.testing.expectEqual(@as(usize, 1), reporter.diagnostics().len);
    try std.testing.expectEqual(@as(u64, 7576), reporter.diagnostics()[0].error_id.value);
    try std.testing.expectEqualStrings(
        "Undeclared identifier. \"local\" is not (or not yet) visible at this point.",
        reporter.diagnostics()[0].description,
    );
}
