// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Declaration type assignment translated from `DeclarationTypeChecker.cpp`.
//!
//! The pass borrows one compilation-scoped `TypeProvider` and writes stable
//! type pointers into the syntax trees' annotations. Traversal is structurally
//! faithful to the upstream visitor, including its special handling for
//! recursive structs, function type names, using directives, and inheritance.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const ConstantEvaluator = @import("constant_evaluator.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;

pub const CheckError = ConstantEvaluator.EvaluateError ||
    TypeProviderModule.ProviderError ||
    Diagnostics.ReportError ||
    error{InvalidAst};

const max_ast_depth = 4096;

pub const DeclarationTypeChecker = struct {
    allocator: std.mem.Allocator,
    tree: *AST.Tree,
    reporter: *Diagnostics.ErrorReporter,
    type_provider: *TypeProviderModule.TypeProvider,
    evm_version: EVMVersion,
    inside_function_type: bool = false,
    recursive_struct_seen: bool = false,
    current_structs_seen: std.AutoHashMap(*const AST.Node, void),

    pub fn init(
        allocator: std.mem.Allocator,
        tree: *AST.Tree,
        reporter: *Diagnostics.ErrorReporter,
        type_provider: *TypeProviderModule.TypeProvider,
        evm_version: EVMVersion,
    ) DeclarationTypeChecker {
        return .{
            .allocator = allocator,
            .tree = tree,
            .reporter = reporter,
            .type_provider = type_provider,
            .evm_version = evm_version,
            .current_structs_seen = std.AutoHashMap(*const AST.Node, void).init(allocator),
        };
    }

    pub fn deinit(self: *DeclarationTypeChecker) void {
        self.current_structs_seen.deinit();
        self.* = undefined;
    }

    pub fn check(self: *DeclarationTypeChecker, root: *AST.Node) CheckError!bool {
        const watcher = self.reporter.errorWatcher();
        try self.checkNode(root, 0);
        if (self.current_structs_seen.count() != 0) return error.InvalidAst;
        return watcher.ok();
    }

    fn checkNode(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        if (depth >= max_ast_depth) return error.InvalidAst;

        switch (node.payload) {
            .elementary_type_name => {
                try self.visitElementaryTypeName(node);
                return;
            },
            .enum_definition => {
                try self.visitEnumDefinition(node);
                return;
            },
            .struct_definition => {
                try self.visitStructDefinition(node, depth);
                return;
            },
            .function_type_name => {
                try self.visitFunctionTypeName(node, depth);
                return;
            },
            .using_for_directive => {
                try self.visitUsingForDirective(node, depth);
                return;
            },
            .inheritance_specifier => if (!(try self.visitInheritanceSpecifier(node)))
                return,
            else => {},
        }

        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(self.allocator);
        try ASTImplementation.appendChildren(self.allocator, &children, node);
        for (children.items) |child|
            try self.checkNode(@constCast(child), depth + 1);

        switch (node.payload) {
            .user_defined_value_type_definition => try self.endUserDefinedValueType(node),
            .user_defined_type_name => try self.endUserDefinedTypeName(node, depth),
            .identifier_path => try self.endIdentifierPath(node),
            .mapping => try self.endMapping(node),
            .array_type_name => try self.endArrayTypeName(node),
            .variable_declaration => try self.endVariableDeclaration(node),
            else => {},
        }
    }

    fn visitElementaryTypeName(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const annotation = try typeNameAnnotation(self.tree, node);
        if (annotation.type_ref != null) return;
        const value = node.payload.elementary_type_name;
        annotation.type_ref = try self.type_provider.fromElementaryTypeToken(
            value.type_name,
            null,
        );
        if (value.state_mutability) |state_mutability| {
            if (annotation.type_ref.?.category() != .Address) return error.InvalidAst;
            switch (state_mutability) {
                .Payable => annotation.type_ref = self.type_provider.payableAddress(),
                .NonPayable => annotation.type_ref = self.type_provider.address(),
                else => try self.reporter.typeError(
                    errorId(2311),
                    node.location,
                    "Address types can only be payable or non-payable.",
                ),
            }
        }
    }

    fn visitEnumDefinition(
        self: *DeclarationTypeChecker,
        node: *const AST.Node,
    ) CheckError!void {
        if (node.payload.enum_definition.members.len > 256)
            try self.reporter.declarationError(
                errorId(1611),
                node.location,
                "Enum with more than 256 members is not allowed.",
            );
    }

    fn visitStructDefinition(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const annotation = try structAnnotation(self.tree, node);
        if (annotation.recursive) |recursive| {
            if (self.current_structs_seen.count() != 0 and recursive)
                self.recursive_struct_seen = true;
            return;
        }
        if (self.current_structs_seen.contains(node)) {
            annotation.recursive = true;
            self.recursive_struct_seen = true;
            return;
        }

        const previous_recursive_seen = self.recursive_struct_seen;
        var has_recursive_child = false;
        try self.current_structs_seen.put(node, {});
        defer _ = self.current_structs_seen.remove(node);

        for (node.payload.struct_definition.members) |member| {
            self.recursive_struct_seen = false;
            try self.checkNode(member, depth + 1);
            if ((try variableAnnotation(self.tree, member)).type_ref == null)
                return error.InvalidAst;
            has_recursive_child = has_recursive_child or self.recursive_struct_seen;
        }
        if (annotation.recursive == null) annotation.recursive = has_recursive_child;
        self.recursive_struct_seen = previous_recursive_seen or annotation.recursive.?;

        var active = std.AutoHashMap(*const AST.Node, void).init(self.allocator);
        defer active.deinit();
        if (try self.hasDirectStructCycle(node, &active, 0))
            try self.reporter.fatal(
                errorId(2046),
                .TypeError,
                node.location,
                null,
                "Recursive struct definition.",
            );
        if (self.current_structs_seen.count() == 1)
            self.recursive_struct_seen = false;
    }

    fn hasDirectStructCycle(
        self: *DeclarationTypeChecker,
        structure: *const AST.Node,
        active: *std.AutoHashMap(*const AST.Node, void),
        depth: usize,
    ) CheckError!bool {
        if (depth >= 256)
            try self.reporter.fatal(
                errorId(5651),
                .DeclarationError,
                structure.location,
                null,
                "Struct definition exhausts cyclic dependency validator.",
            );
        if (active.contains(structure)) return true;
        try active.put(structure, {});
        defer _ = active.remove(structure);

        for (structure.payload.struct_definition.members) |member| {
            var member_type = (try variableAnnotation(
                self.tree,
                member,
            )).type_ref orelse return error.InvalidAst;
            while (member_type.category() == .Array) {
                const array = member_type.payload.Array;
                if (array.isDynamicallySized()) break;
                member_type = array.base_type;
            }
            if (member_type.category() == .Struct and
                try self.hasDirectStructCycle(
                    member_type.payload.Struct.declaration,
                    active,
                    depth + 1,
                )) return true;
        }
        return false;
    }

    fn endUserDefinedValueType(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const value = node.payload.user_defined_value_type_definition;
        if (value.underlying_type.nodeKind() != .elementary_type_name)
            try self.reporter.fatal(
                errorId(8657),
                .TypeError,
                value.underlying_type.location,
                null,
                "The underlying type for a user defined value type has to be an elementary value type.",
            );
        const underlying = (try typeNameAnnotation(
            self.tree,
            value.underlying_type,
        )).type_ref orelse return error.InvalidAst;
        if (underlying.category() == .UserDefinedValueType) return error.InvalidAst;
        _ = try self.type_provider.userDefinedValueType(node, underlying);
        if (!TypeBehavior.isValueType(underlying)) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "The underlying type of the user defined value type \"{s}\" is not a value type.",
                .{value.declaration.name},
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(8129), node.location, message);
        }
    }

    fn endUserDefinedTypeName(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const annotation = try typeNameAnnotation(self.tree, node);
        if (annotation.type_ref != null) return;
        const path = node.payload.user_defined_type_name.path_node;
        const declaration = (try identifierPathAnnotation(
            self.tree,
            path,
        )).referenced_declaration orelse return error.InvalidAst;

        annotation.type_ref = switch (declaration.nodeKind()) {
            .struct_definition => blk: {
                if (!self.inside_function_type and
                    self.current_structs_seen.count() != 0)
                    try self.visitStructDefinition(@constCast(declaration), depth + 1);
                break :blk try self.type_provider.structType(declaration, .Storage);
            },
            .enum_definition => try self.type_provider.enumType(declaration),
            .contract_definition => try self.type_provider.contract(declaration, false),
            .user_defined_value_type_definition => blk: {
                const underlying_node = declaration.payload
                    .user_defined_value_type_definition.underlying_type;
                const underlying_annotation = try typeNameAnnotation(
                    self.tree,
                    underlying_node,
                );
                break :blk try self.type_provider.userDefinedValueType(
                    declaration,
                    underlying_annotation.type_ref,
                );
            },
            else => {
                annotation.type_ref = self.type_provider.emptyTuple();
                try self.reporter.fatal(
                    errorId(5172),
                    .TypeError,
                    node.location,
                    null,
                    "Name has to refer to a user-defined type.",
                );
                unreachable;
            },
        };
    }

    fn endIdentifierPath(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const declaration = (try identifierPathAnnotation(
            self.tree,
            node,
        )).referenced_declaration orelse return error.InvalidAst;
        if (declaration.nodeKind() == .contract_definition and
            declaration.payload.contract_definition.contract_kind == .Library)
            try self.reporter.typeError(
                errorId(1130),
                node.location,
                "Invalid use of a library name.",
            );
    }

    fn visitFunctionTypeName(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const annotation = try typeNameAnnotation(self.tree, node);
        if (annotation.type_ref != null) return;
        const value = node.payload.function_type_name;

        const previous_inside = self.inside_function_type;
        self.inside_function_type = true;
        defer self.inside_function_type = previous_inside;
        try self.checkNode(value.parameter_types, depth + 1);
        try self.checkNode(value.return_types, depth + 1);

        const visibility = value.effectiveVisibility();
        switch (visibility) {
            .Internal, .External => {},
            else => {
                try self.reporter.fatal(
                    errorId(6012),
                    .TypeError,
                    node.location,
                    null,
                    "Invalid visibility, can only be \"external\" or \"internal\".",
                );
                unreachable;
            },
        }
        if (value.state_mutability == .Payable and visibility != .External)
            try self.reporter.fatal(
                errorId(7415),
                .TypeError,
                node.location,
                null,
                "Only external function types can be payable.",
            );
        annotation.type_ref = try self.type_provider.functionFromTypeName(node);
    }

    fn endMapping(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const annotation = try typeNameAnnotation(self.tree, node);
        if (annotation.type_ref != null) return;
        const value = node.payload.mapping;
        var key_type = (try typeNameAnnotation(
            self.tree,
            value.key_type,
        )).type_ref orelse return error.InvalidAst;
        if (value.key_type.nodeKind() == .user_defined_type_name) switch (key_type.category()) {
            .Enum, .Contract, .UserDefinedValueType => {},
            else => try self.reporter.fatal(
                errorId(7804),
                .TypeError,
                value.key_type.location,
                null,
                "Only elementary types, user defined value types, contract types or enums are allowed as mapping keys.",
            ),
        } else if (value.key_type.nodeKind() != .elementary_type_name) {
            return error.InvalidAst;
        }

        var value_type = (try typeNameAnnotation(
            self.tree,
            value.value_type,
        )).type_ref orelse return error.InvalidAst;
        key_type = try self.type_provider.withLocationIfReference(
            .Memory,
            key_type,
            false,
        );
        value_type = try self.type_provider.withLocationIfReference(
            .Storage,
            value_type,
            false,
        );
        annotation.type_ref = try self.type_provider.mapping(
            key_type,
            value.key_name,
            value_type,
            value.value_name,
        );

        if (value.key_name.len == 0) return;
        var child_mapping = value_type.asMapping();
        var current_value_name = value.value_name;
        while (true) {
            var conflict = false;
            const inspecting_child_mapping = child_mapping != null;
            if (child_mapping) |child| {
                conflict = std.mem.eql(u8, value.key_name, child.key_name);
                current_value_name = child.value_name;
                child_mapping = child.value_type.asMapping();
            } else {
                conflict = std.mem.eql(u8, value.key_name, current_value_name);
            }
            if (conflict) {
                const message = try std.fmt.allocPrint(
                    self.allocator,
                    "Conflicting parameter name \"{s}\" in mapping.",
                    .{value.key_name},
                );
                defer self.allocator.free(message);
                try self.reporter.declarationError(errorId(1809), node.location, message);
            }
            if (!inspecting_child_mapping) break;
        }
    }

    fn endArrayTypeName(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const annotation = try typeNameAnnotation(self.tree, node);
        if (annotation.type_ref != null) return;
        const value = node.payload.array_type_name;
        const base_type = (try typeNameAnnotation(
            self.tree,
            value.base_type,
        )).type_ref orelse {
            if (self.reporter.hasErrors()) return;
            return error.InvalidAst;
        };

        if (value.length) |length_expression| {
            var length_value: ?ConstantEvaluator.RationalValue = null;
            if (expressionType(length_expression)) |annotated_type|
                if (annotated_type.category() == .RationalNumber) {
                    const rational = annotated_type.payload.RationalNumber;
                    length_value = .{
                        .numerator = rational.numerator.clone(),
                        .denominator = rational.denominator.clone(),
                    };
                };
            if (length_value == null) {
                var evaluated = try ConstantEvaluator.evaluate(
                    self.allocator,
                    self.reporter,
                    self.type_provider,
                    length_expression,
                );
                defer evaluated.deinit();
                if (evaluated.rationalValue()) |rational|
                    length_value = rational.clone();
            }
            defer if (length_value) |*present| present.deinit();
            var static_length: u256 = 0;
            if (length_value == null) {
                try self.reporter.typeError(
                    errorId(5462),
                    length_expression.location,
                    "Invalid array length, expected integer literal or constant expression.",
                );
            } else if (length_value.?.numerator.isZero()) {
                try self.reporter.typeError(
                    errorId(1406),
                    length_expression.location,
                    "Array with zero length specified.",
                );
            } else if (length_value.?.denominator.compareUnsigned(1) == .eq) {
                if (length_value.?.numerator.isNegative()) {
                    try self.reporter.typeError(
                        errorId(3658),
                        length_expression.location,
                        "Array with negative length specified.",
                    );
                } else if (length_value.?.numerator.bitLength() > 256) {
                    try self.reporter.typeError(
                        errorId(1847),
                        length_expression.location,
                        "Array length too large, maximum is 2**256 - 1.",
                    );
                } else {
                    static_length = length_value.?.numerator.toU256Wrapping();
                }
            } else {
                try self.reporter.typeError(
                    errorId(3208),
                    length_expression.location,
                    "Array with fractional length specified.",
                );
            }
            annotation.type_ref = try self.type_provider.arrayWithLength(
                .Storage,
                base_type,
                static_length,
            );
        } else {
            annotation.type_ref = try self.type_provider.array(.Storage, base_type);
        }
    }

    fn endVariableDeclaration(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
    ) CheckError!void {
        const annotation = try variableAnnotation(self.tree, node);
        if (annotation.type_ref != null) return;
        const value = node.payload.variable_declaration;
        const constant = value.mutability == .Constant;
        const immutable = value.mutability == .Immutable;
        const state_variable = isStateVariable(node);
        const file_level = isFileLevelVariable(node);

        if (file_level and !constant)
            try self.reporter.declarationError(
                errorId(8342),
                node.location,
                "Only constant variables are allowed at file level.",
            );
        if (constant and !state_variable and !file_level)
            try self.reporter.declarationError(
                errorId(1788),
                node.location,
                "The \"constant\" keyword can only be used for state variables or variables at file level.",
            );
        if (immutable and !state_variable)
            try self.reporter.declarationError(
                errorId(8297),
                node.location,
                "The \"immutable\" keyword can only be used for state variables.",
            );

        var variable_location = value.reference_location;
        var type_location: Types.DataLocation = .Memory;
        if (variable_location == .Transient and
            !self.evm_version.supportsTransientStorage())
            try self.reporter.declarationError(
                errorId(7985),
                node.location,
                "Transient storage is not supported by EVM versions older than cancun.",
            );

        const type_name = value.type_name orelse return error.InvalidAst;
        var type_ref = (try typeNameAnnotation(
            self.tree,
            type_name,
        )).type_ref orelse return error.InvalidAst;
        const has_reference_or_mapping = type_ref.asReference() != null or
            type_ref.category() == .Mapping;
        const allowed = allowedDataLocations(node, has_reference_or_mapping);
        if (!allowed[locationIndex(variable_location)]) {
            const message = try self.invalidDataLocationMessage(
                node,
                allowed,
                has_reference_or_mapping,
                variable_location,
            );
            defer self.allocator.free(message);
            try self.reporter.typeError(errorId(6651), node.location, message);
            variable_location = firstAllowedLocation(allowed) orelse return error.InvalidAst;
        }

        if (isEventOrErrorParameter(node) or file_level) {
            if (variable_location != .Unspecified) return error.InvalidAst;
            type_location = .Memory;
        } else if (state_variable) {
            switch (variable_location) {
                .Unspecified => type_location = if (constant or immutable)
                    .Memory
                else
                    .Storage,
                .Transient => {
                    if (constant or immutable)
                        try self.reporter.declarationError(
                            errorId(2197),
                            node.location,
                            "Transient cannot be used as data location for constant or immutable variables.",
                        );
                    if (value.value != null)
                        try self.reporter.declarationError(
                            errorId(9825),
                            node.location,
                            "Initialization of transient storage state variables is not supported.",
                        );
                    type_location = .Transient;
                },
                else => return error.InvalidAst,
            }
        } else if (isStructOrEnumMember(node)) {
            type_location = .Storage;
        } else switch (variable_location) {
            .Memory => type_location = .Memory,
            .Storage => type_location = .Storage,
            .CallData => type_location = .CallData,
            .Transient => return error.InvalidAst,
            .Unspecified => if (has_reference_or_mapping) return error.InvalidAst,
        }

        if (!TypeBehavior.isValueType(type_ref) and type_location == .Transient) {
            // `solUnimplementedAssert` is not source-bound upstream, so this
            // diagnostic deliberately carries an invalid location.
            try self.reporter.unimplementedFeatureError(
                errorId(1834),
                .{},
                "Transient data location is only supported for value types.",
            );
        } else if (type_ref.asReference() != null) {
            type_ref = try self.type_provider.withLocation(
                type_ref,
                type_location,
                !state_variable,
            );
        }

        if (constant and !TypeBehavior.isValueType(type_ref)) {
            const allowed_constant = if (type_ref.asArray()) |array|
                array.isByteArrayOrString()
            else
                false;
            if (!allowed_constant)
                try self.reporter.fatal(
                    errorId(9259),
                    .TypeError,
                    node.location,
                    null,
                    "Only constants of value type and byte array type are implemented.",
                );
        }
        annotation.type_ref = type_ref;
    }

    fn invalidDataLocationMessage(
        self: *DeclarationTypeChecker,
        variable: *const AST.Node,
        allowed: [5]bool,
        has_reference_or_mapping: bool,
        actual: AST.VariableLocation,
    ) std.mem.Allocator.Error![]u8 {
        var output: std.ArrayList(u8) = .empty;
        errdefer output.deinit(self.allocator);
        if (!has_reference_or_mapping) {
            try output.appendSlice(
                self.allocator,
                "Data location can only be specified for array, struct or mapping types",
            );
        } else {
            try output.appendSlice(self.allocator, "Data location must be ");
            var names: [5][]const u8 = undefined;
            var count: usize = 0;
            inline for (std.meta.fields(AST.VariableLocation)) |field| {
                const location: AST.VariableLocation = @enumFromInt(field.value);
                if (allowed[locationIndex(location)]) {
                    names[count] = variableLocationDiagnosticName(location);
                    count += 1;
                }
            }
            for (names[0..count], 0..) |name, index| {
                if (index != 0) {
                    if (index + 1 == count)
                        try output.appendSlice(self.allocator, " or ")
                    else
                        try output.appendSlice(self.allocator, ", ");
                }
                try output.appendSlice(self.allocator, name);
            }
            if (isConstructorParameter(variable)) {
                try output.appendSlice(self.allocator, " for constructor parameter");
            } else if (isCallableOrCatchParameter(variable)) {
                try output.appendSlice(self.allocator, " for ");
                if (isReturnParameter(variable))
                    try output.appendSlice(self.allocator, "return ");
                try output.appendSlice(self.allocator, "parameter in");
                if (isExternalCallableParameter(variable))
                    try output.appendSlice(self.allocator, " external");
                try output.appendSlice(self.allocator, " function");
            } else {
                try output.appendSlice(self.allocator, " for variable");
            }
        }
        try output.appendSlice(self.allocator, ", but ");
        try output.appendSlice(self.allocator, variableLocationDiagnosticName(actual));
        try output.appendSlice(self.allocator, " was given.");
        return output.toOwnedSlice(self.allocator);
    }

    fn visitUsingForDirective(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
        depth: usize,
    ) CheckError!void {
        const value = node.payload.using_for_directive;
        if (value.uses_braces) {
            for (value.functions_and_operators) |entry| {
                const function = (try identifierPathAnnotation(
                    self.tree,
                    entry.function_or_library,
                )).referenced_declaration orelse return error.InvalidAst;
                if (function.nodeKind() != .function_definition)
                    try self.reporter.fatal(
                        errorId(8187),
                        .TypeError,
                        entry.function_or_library.location,
                        null,
                        "Expected function name.",
                    );
                const definition = function.payload.function_definition;
                const enclosing = ASTImplementation.scope(function);
                const library_function = enclosing != null and
                    enclosing.?.nodeKind() == .contract_definition and
                    enclosing.?.payload.contract_definition.contract_kind == .Library;
                if (!definition.free and !library_function)
                    try self.reporter.typeError(
                        errorId(4167),
                        entry.function_or_library.location,
                        "Only file-level functions and library functions can be attached to a type in a \"using\" statement",
                    );
            }
        } else {
            if (value.functions_and_operators.len == 0) return error.InvalidAst;
            const path = value.functions_and_operators[0].function_or_library;
            const library = (try identifierPathAnnotation(
                self.tree,
                path,
            )).referenced_declaration orelse return error.InvalidAst;
            if (library.nodeKind() != .contract_definition or
                library.payload.contract_definition.contract_kind != .Library)
                try self.reporter.fatal(
                    errorId(4357),
                    .TypeError,
                    path.location,
                    null,
                    "Library name expected. If you want to attach a function, use '{...}'.",
                );
        }
        if (value.type_name) |type_name|
            try self.checkNode(type_name, depth + 1);
    }

    fn visitInheritanceSpecifier(
        self: *DeclarationTypeChecker,
        node: *AST.Node,
    ) CheckError!bool {
        const name = node.payload.inheritance_specifier.base_name;
        const contract = (try identifierPathAnnotation(
            self.tree,
            name,
        )).referenced_declaration orelse return error.InvalidAst;
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        if (contract.payload.contract_definition.contract_kind == .Library) {
            try self.reporter.typeError(
                errorId(2571),
                name.location,
                "Libraries cannot be inherited from.",
            );
            return false;
        }
        return true;
    }
};

fn allowedDataLocations(
    variable: *const AST.Node,
    has_reference_or_mapping: bool,
) [5]bool {
    var allowed = [_]bool{false} ** 5;
    if (isStateVariable(variable)) {
        allowed[locationIndex(.Unspecified)] = true;
        allowed[locationIndex(.Transient)] = true;
    } else if (!has_reference_or_mapping or isEventOrErrorParameter(variable)) {
        allowed[locationIndex(.Unspecified)] = true;
    } else if (isCallableOrCatchParameter(variable)) {
        allowed[locationIndex(.Memory)] = true;
        if (isConstructorParameter(variable) or
            isInternalCallableParameter(variable) or
            isLibraryFunctionParameter(variable))
            allowed[locationIndex(.Storage)] = true;
        if (!isTryCatchParameter(variable) and !isConstructorParameter(variable))
            allowed[locationIndex(.CallData)] = true;
    } else if (ASTImplementation.isLocalVariable(variable)) {
        allowed[locationIndex(.Memory)] = true;
        allowed[locationIndex(.Storage)] = true;
        allowed[locationIndex(.CallData)] = true;
    } else {
        allowed[locationIndex(.Unspecified)] = true;
    }
    return allowed;
}

fn firstAllowedLocation(allowed: [5]bool) ?AST.VariableLocation {
    inline for (std.meta.fields(AST.VariableLocation)) |field| {
        const location: AST.VariableLocation = @enumFromInt(field.value);
        if (allowed[locationIndex(location)]) return location;
    }
    return null;
}

fn variableLocationDiagnosticName(location: AST.VariableLocation) []const u8 {
    return switch (location) {
        .Memory => "\"memory\"",
        .Storage => "\"storage\"",
        .Transient => "\"transient\"",
        .CallData => "\"calldata\"",
        .Unspecified => "none",
    };
}

fn locationIndex(location: AST.VariableLocation) usize {
    return @intCast(@intFromEnum(location));
}

fn isStateVariable(variable: *const AST.Node) bool {
    return ASTImplementation.isStateVariable(variable);
}

fn isFileLevelVariable(variable: *const AST.Node) bool {
    return ASTImplementation.isFileLevelVariable(variable);
}

fn isStructOrEnumMember(variable: *const AST.Node) bool {
    const enclosing = ASTImplementation.scope(variable) orelse return false;
    return enclosing.nodeKind() == .struct_definition or
        enclosing.nodeKind() == .enum_definition;
}

fn isEventOrErrorParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isEventOrErrorParameter(variable);
}

fn isTryCatchParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isTryCatchParameter(variable);
}

fn isCallableOrCatchParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isCallableOrCatchParameter(variable);
}

fn isReturnParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isReturnParameter(variable);
}

fn isExternalCallableParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isExternalCallableParameter(variable);
}

fn isInternalCallableParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isInternalCallableParameter(variable);
}

fn isConstructorParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isConstructorParameter(variable);
}

fn isLibraryFunctionParameter(variable: *const AST.Node) bool {
    return ASTImplementation.isLibraryFunctionParameter(variable);
}

fn typeNameAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.TypeNameAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .type_name => |*value| value,
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

fn identifierPathAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.IdentifierPathAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .identifier_path => |*value| value,
        else => error.InvalidAst,
    };
}

fn expressionType(node: *const AST.Node) ?*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    const expression = switch (annotation.*) {
        .expression => |*value| value,
        .identifier => |*value| &value.expression,
        .member_access => |*value| &value.expression,
        .operation => |*value| &value.expression,
        .binary_operation => |*value| &value.operation.expression,
        .function_call => |*value| &value.expression,
        else => return null,
    };
    return expression.type_ref;
}

fn structAnnotation(
    tree: *AST.Tree,
    node: *AST.Node,
) CheckError!*ASTAnnotations.StructDeclarationAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .struct_declaration => |*value| value,
        else => error.InvalidAst,
    };
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "declaration types assign concrete composite locations and function signatures" {
    const Parser = @import("../parsing/parser.zig");
    const Scoper = @import("scoper.zig");
    const GlobalContext = @import("global_context.zig").GlobalContext;
    const NameResolver = @import("name_and_type_resolver.zig").NameAndTypeResolver;
    const ReferencesResolver = @import("references_resolver.zig");

    const source =
        "// SPDX-License-Identifier: UNLICENSED\n" ++
        "type Price is uint128; " ++
        "contract C { struct S { uint value; S[] children; } " ++
        "mapping(address owner => mapping(uint id => S item)) private records; " ++
        "function f(S calldata input) external returns (Price out) {} }";
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "Types.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
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
    var resolver = try NameResolver.init(
        std.testing.allocator,
        &global,
        EVMVersion.current(),
        &reporter,
        false,
    );
    defer resolver.deinit();
    try std.testing.expect(try resolver.registerSource(&parsed.tree, root));
    try std.testing.expect(try ReferencesResolver.resolveSource(
        &parsed.tree,
        &resolver,
        root,
    ));

    var checker = DeclarationTypeChecker.init(
        std.testing.allocator,
        &parsed.tree,
        &reporter,
        &provider,
        EVMVersion.current(),
    );
    defer checker.deinit();
    try std.testing.expect(try checker.check(root));
    try std.testing.expect(!reporter.hasErrors());

    const contract = root.payload.source_unit.nodes[1];
    const members = contract.payload.contract_definition.sub_nodes;
    const structure = members[0];
    try std.testing.expect((try structAnnotation(
        &parsed.tree,
        structure,
    )).recursive.?);
    const mapping_variable = members[1];
    const mapping_type = (try variableAnnotation(
        &parsed.tree,
        mapping_variable,
    )).type_ref.?;
    try std.testing.expectEqual(Types.Category.Mapping, mapping_type.category());
    try std.testing.expectEqualStrings("owner", mapping_type.payload.Mapping.key_name);

    const function = members[2];
    const input = function.payload.function_definition.callable.parameters
        .payload.parameter_list.parameters[0];
    const input_type = (try variableAnnotation(&parsed.tree, input)).type_ref.?;
    try std.testing.expectEqual(
        Types.DataLocation.CallData,
        input_type.payload.Struct.reference.location,
    );
}

test "declaration type diagnostics preserve data-location wording" {
    const Parser = @import("../parsing/parser.zig");
    const Scoper = @import("scoper.zig");

    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        "// SPDX-License-Identifier: UNLICENSED\ncontract C { function f() public { uint memory value; } }",
        "Location.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();
    const root = parsed.tree.root.?;
    try Scoper.assignScopes(&parsed.tree, root);
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var checker = DeclarationTypeChecker.init(
        std.testing.allocator,
        &parsed.tree,
        &reporter,
        &provider,
        EVMVersion.current(),
    );
    defer checker.deinit();
    try std.testing.expect(!(try checker.check(root)));
    try std.testing.expectEqual(@as(u64, 6651), reporter.diagnostics()[0].error_id.value);
    try std.testing.expectEqualStrings(
        "Data location can only be specified for array, struct or mapping types, but \"memory\" was given.",
        reporter.diagnostics()[0].description,
    );
}
