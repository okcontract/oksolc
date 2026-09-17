// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Solidity syntax tree and semantic queries translated from `AST.cpp`.
//!
//! Semantic queries use analysis annotations for type resolution, contract
//! interfaces, and virtual dispatch.

const std = @import("std");
const AST = @This();
const ASTAnnotations = @import("ast_annotations.zig");
const Types = @import("types.zig");
const TypeProviderModule = @import("type_provider.zig");
const TypeBehavior = @import("types.zig");
const TokenModule = @import("../../liblangutil/token.zig");
const CommonData = @import("../../libsolutil/common_data.zig");
const FunctionSelector = @import("../../libsolutil/function_selector.zig");
const IncrementalIdentity = @import("../../incremental/identity.zig");

pub const SourceId = IncrementalIdentity.SourceId;
pub const LocalNodeId = IncrementalIdentity.LocalNodeId;
pub const NodeRef = IncrementalIdentity.NodeRef;

/// Stable indirection owned by one immutable syntax tree. Semantic revisions
/// rebind this context to their annotation table without mutating syntax nodes.
pub const SemanticContext = struct {
    annotation_table: ?*anyopaque = null,
    owns_annotation_table: bool = false,
};

pub const AstError = TypeBehavior.BehaviorError || CommonData.AddressError || error{
    InvalidAst,
    MissingAnnotation,
    MissingCallGraph,
    SelectorCollision,
    VirtualDeclarationNotFound,
    InvalidNamedArguments,
};

pub const DataLocationSet = std.EnumSet(AST.VariableLocation);

pub const InterfaceFunction = struct {
    selector: FunctionSelector.H32,
    function_type: *const Types.Type,
};

pub fn visibilityToString(value: AST.Visibility) error{InvalidVisibility}![]const u8 {
    return switch (value) {
        .Public => "public",
        .Internal => "internal",
        .Private => "private",
        .External => "external",
        .Default => error.InvalidVisibility,
    };
}

pub fn mutabilityToString(value: AST.VariableMutability) []const u8 {
    return switch (value) {
        .Mutable => "mutable",
        .Immutable => "immutable",
        .Constant => "constant",
    };
}

pub fn variableLocationToString(value: AST.VariableLocation) []const u8 {
    return switch (value) {
        .Unspecified => "default",
        .Storage => "storage",
        .Transient => "transient",
        .Memory => "memory",
        .CallData => "calldata",
    };
}

pub fn contractKindToString(value: AST.ContractKind) []const u8 {
    return switch (value) {
        .Interface => "interface",
        .Contract => "contract",
        .Library => "library",
    };
}

pub fn scope(node: *const AST.Node) ?*const AST.Node {
    const annotation = ASTAnnotations.scopableForNodeConst(node) orelse return null;
    return annotation.scope;
}

fn contractAnnotation(
    node: *const AST.Node,
) ?*const ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => null,
    };
}

fn sourceUnitAnnotation(
    node: *const AST.Node,
) ?*const ASTAnnotations.SourceUnitAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .source_unit => |*value| value,
        else => null,
    };
}

fn variableAnnotation(
    node: *const AST.Node,
) ?*const ASTAnnotations.VariableDeclarationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .variable_declaration => |*value| value,
        else => null,
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

/// Extracts the common referenced-declaration annotation projection.
pub fn referencedDeclaration(expression: *const AST.Node) ?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(expression) orelse return null;
    return switch (annotation.*) {
        .member_access => |value| value.referenced_declaration,
        .identifier_path => |value| value.referenced_declaration,
        .identifier => |value| value.referenced_declaration,
        else => null,
    };
}

pub fn filteredNodesAlloc(
    allocator: std.mem.Allocator,
    nodes: AST.NodeList,
    kind: AST.Kind,
) std.mem.Allocator.Error![]*const AST.Node {
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    for (nodes) |node|
        if (node.nodeKind() == kind) try result.append(allocator, node);
    return result.toOwnedSlice(allocator);
}

fn callableAnnotationMutable(
    tree: *AST.Tree,
    callable: *AST.Node,
) AstError!*ASTAnnotations.CallableDeclarationAnnotation {
    const annotation = try ASTAnnotations.ensure(tree, callable);
    return switch (annotation.*) {
        .documented_callable => |*value| &value.callable,
        else => error.InvalidAst,
    };
}

pub fn addLocalVariable(
    tree: *AST.Tree,
    callable: *AST.Node,
    variable: *const AST.Node,
) AstError!void {
    if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
    const annotation = try callableAnnotationMutable(tree, callable);
    try annotation.local_variables.append(tree.allocator(), variable);
}

pub fn localVariables(callable: *const AST.Node) ?[]const *const AST.Node {
    const annotation = ASTAnnotations.annotationConst(callable) orelse return null;
    return switch (annotation.*) {
        .documented_callable => |value| value.callable.local_variables.items,
        else => null,
    };
}

pub fn sourceUnit(node: *const AST.Node) ?*const AST.Node {
    var current = scope(node) orelse return null;
    while (scope(current)) |parent| current = parent;
    return if (current.nodeKind() == .source_unit) current else null;
}

pub fn functionOrModifierDefinition(node: *const AST.Node) ?*const AST.Node {
    var current = scope(node) orelse return null;
    while (true) {
        switch (current.nodeKind()) {
            .function_definition, .modifier_definition => return current,
            else => {},
        }
        current = scope(current) orelse return null;
    }
}

pub fn sourceUnitName(node: *const AST.Node) ?[]const u8 {
    const unit = sourceUnit(node) orelse return null;
    const annotation = sourceUnitAnnotation(unit) orelse return null;
    return annotation.path.value;
}

pub fn isEnumValue(declaration: *const AST.Node) bool {
    const enclosing = scope(declaration) orelse return false;
    return enclosing.nodeKind() == .enum_definition;
}

pub fn isStructMember(declaration: *const AST.Node) bool {
    const enclosing = scope(declaration) orelse return false;
    return enclosing.nodeKind() == .struct_definition;
}

pub fn isEventOrErrorParameter(declaration: *const AST.Node) bool {
    const enclosing = scope(declaration) orelse return false;
    return enclosing.nodeKind() == .event_definition or
        enclosing.nodeKind() == .error_definition;
}

pub fn isFileLevelVariable(declaration: *const AST.Node) bool {
    if (declaration.nodeKind() != .variable_declaration) return false;
    const enclosing = scope(declaration) orelse return false;
    return enclosing.nodeKind() == .source_unit;
}

fn parameterNodes(node: *const AST.Node) ?AST.NodeList {
    const list = switch (node.payload) {
        .function_type_name => |value| value.parameter_types,
        .function_definition => |value| value.callable.parameters,
        .modifier_definition => |value| value.callable.parameters,
        .event_definition => |value| value.callable.parameters,
        .error_definition => |value| value.callable.parameters,
        else => return null,
    };
    if (list.nodeKind() != .parameter_list) return null;
    return list.payload.parameter_list.parameters;
}

fn returnParameterNodes(node: *const AST.Node) ?AST.NodeList {
    const list = switch (node.payload) {
        .function_type_name => |value| value.return_types,
        .function_definition => |value| value.callable.return_parameters orelse return null,
        .modifier_definition => |value| value.callable.return_parameters orelse return null,
        .event_definition => |value| value.callable.return_parameters orelse return null,
        .error_definition => |value| value.callable.return_parameters orelse return null,
        else => return null,
    };
    if (list.nodeKind() != .parameter_list) return null;
    return list.payload.parameter_list.parameters;
}

fn containsNode(nodes: AST.NodeList, needle: *const AST.Node) bool {
    for (nodes) |node| if (node == needle) return true;
    return false;
}

pub fn isReturnParameter(variable: *const AST.Node) bool {
    if (variable.nodeKind() != .variable_declaration) return false;
    const enclosing = scope(variable) orelse return false;
    const parameters = returnParameterNodes(enclosing) orelse return false;
    return containsNode(parameters, variable);
}

pub fn isTryCatchParameter(variable: *const AST.Node) bool {
    if (variable.nodeKind() != .variable_declaration) return false;
    const enclosing = scope(variable) orelse return false;
    return enclosing.nodeKind() == .try_catch_clause;
}

pub fn isCallableOrCatchParameter(variable: *const AST.Node) bool {
    if (variable.nodeKind() != .variable_declaration) return false;
    if (isReturnParameter(variable) or isTryCatchParameter(variable)) return true;
    const enclosing = scope(variable) orelse return false;
    const parameters = parameterNodes(enclosing) orelse return false;
    return containsNode(parameters, variable);
}

pub fn isLocalOrReturn(variable: *const AST.Node) bool {
    return isReturnParameter(variable) or
        (isLocalVariable(variable) and !isCallableOrCatchParameter(variable));
}

pub fn isExternalCallableParameter(variable: *const AST.Node) bool {
    if (!isCallableOrCatchParameter(variable) or isReturnParameter(variable)) return false;
    const enclosing = scope(variable) orelse return false;
    return enclosing.nodeKind() != .function_type_name and
        enclosing.effectiveVisibility() == .External;
}

pub fn isPublicCallableParameter(variable: *const AST.Node) bool {
    if (!isCallableOrCatchParameter(variable) or isReturnParameter(variable)) return false;
    const enclosing = scope(variable) orelse return false;
    return enclosing.nodeKind() != .function_type_name and
        enclosing.effectiveVisibility() == .Public;
}

pub fn isInternalCallableParameter(variable: *const AST.Node) bool {
    if (!isCallableOrCatchParameter(variable)) return false;
    const enclosing = scope(variable) orelse return false;
    return switch (enclosing.payload) {
        .function_type_name => |value| value.effectiveVisibility() == .Internal,
        .function_definition,
        .modifier_definition,
        .event_definition,
        .error_definition,
        => if (enclosing.effectiveVisibility()) |visibility|
            @intFromEnum(visibility) <= @intFromEnum(AST.Visibility.Internal)
        else
            false,
        else => false,
    };
}

pub fn isConstructorParameter(variable: *const AST.Node) bool {
    if (!isCallableOrCatchParameter(variable)) return false;
    const enclosing = scope(variable) orelse return false;
    return enclosing.nodeKind() == .function_definition and
        enclosing.payload.function_definition.kind == .Constructor;
}

pub fn functionIsLibrary(function: *const AST.Node) bool {
    if (function.nodeKind() != .function_definition) return false;
    const enclosing = scope(function) orelse return false;
    return enclosing.nodeKind() == .contract_definition and
        enclosing.payload.contract_definition.contract_kind == .Library;
}

pub fn isLibraryFunctionParameter(variable: *const AST.Node) bool {
    if (!isCallableOrCatchParameter(variable)) return false;
    const enclosing = scope(variable) orelse return false;
    return functionIsLibrary(enclosing);
}

pub fn hasReferenceOrMappingType(variable: *const AST.Node) AstError!bool {
    if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
    const type_name = variable.payload.variable_declaration.type_name orelse
        return error.InvalidAst;
    const annotation = ASTAnnotations.annotationConst(type_name) orelse
        return error.MissingAnnotation;
    const type_ref = switch (annotation.*) {
        .type_name => |value| value.type_ref orelse return error.MissingAnnotation,
        else => return error.InvalidAst,
    };
    return type_ref.category() == .Mapping or type_ref.asReference() != null;
}

pub fn allowedDataLocations(variable: *const AST.Node) AstError!DataLocationSet {
    if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
    if (isStateVariable(variable))
        return DataLocationSet.initMany(&.{ .Unspecified, .Transient });
    if (!(try hasReferenceOrMappingType(variable)) or isEventOrErrorParameter(variable))
        return DataLocationSet.initOne(.Unspecified);
    if (isCallableOrCatchParameter(variable)) {
        var result = DataLocationSet.initOne(.Memory);
        if (isConstructorParameter(variable) or
            isInternalCallableParameter(variable) or
            isLibraryFunctionParameter(variable)) result.insert(.Storage);
        if (!isTryCatchParameter(variable) and
            !isConstructorParameter(variable)) result.insert(.CallData);
        return result;
    }
    if (isLocalVariable(variable))
        return DataLocationSet.initMany(&.{ .Memory, .Storage, .CallData });
    return DataLocationSet.initOne(.Unspecified);
}

pub fn functionVirtualSemantics(function: *const AST.Node) bool {
    if (function.nodeKind() != .function_definition) return false;
    const value = function.payload.function_definition;
    if (value.callable.marked_virtual) return true;
    const annotation = ASTAnnotations.annotationConst(function) orelse return false;
    const callable = switch (annotation.*) {
        .documented_callable => |entry| entry.callable,
        else => return false,
    };
    const contract = callable.declaration.scopable.contract orelse return false;
    return contract.nodeKind() == .contract_definition and
        contract.payload.contract_definition.contract_kind == .Interface;
}

pub fn referencedSourceUnitsAlloc(
    allocator: std.mem.Allocator,
    source: *const AST.Node,
    recurse: bool,
    initial_skip_list: []const *const AST.Node,
) AstError![]*const AST.Node {
    if (source.nodeKind() != .source_unit) return error.InvalidAst;
    var skip = std.AutoHashMap(*const AST.Node, void).init(allocator);
    defer skip.deinit();
    for (initial_skip_list) |entry| try skip.put(entry, {});
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    try collectReferencedSourceUnits(allocator, source, recurse, &skip, &result);
    std.sort.insertion(*const AST.Node, result.items, {}, nodeIdLessThan);
    return result.toOwnedSlice(allocator);
}

fn collectReferencedSourceUnits(
    allocator: std.mem.Allocator,
    source: *const AST.Node,
    recurse: bool,
    skip: *std.AutoHashMap(*const AST.Node, void),
    result: *std.ArrayList(*const AST.Node),
) AstError!void {
    if (source.nodeKind() != .source_unit) return error.InvalidAst;
    for (source.payload.source_unit.nodes) |node| {
        if (node.nodeKind() != .import_directive) continue;
        const annotation = ASTAnnotations.annotationConst(node) orelse
            return error.MissingAnnotation;
        const imported = switch (annotation.*) {
            .import => |value| value.source_unit orelse return error.MissingAnnotation,
            else => return error.InvalidAst,
        };
        const insertion = try skip.getOrPut(imported);
        if (insertion.found_existing) continue;
        try result.append(allocator, imported);
        if (recurse)
            try collectReferencedSourceUnits(allocator, imported, true, skip, result);
    }
}

fn nodeIdLessThan(_: void, left: *const AST.Node, right: *const AST.Node) bool {
    return ASTAnnotations.compatibilityId(left) < ASTAnnotations.compatibilityId(right);
}

pub fn contractHierarchy(contract: *const AST.Node) AstError!AST.NodeList {
    if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
    const annotation = contractAnnotation(contract) orelse return error.MissingAnnotation;
    if (annotation.linearized_base_contracts.len == 0 or
        annotation.linearized_base_contracts[0] != contract)
        return error.MissingAnnotation;
    return annotation.linearized_base_contracts;
}

pub fn contractDerivesFrom(
    contract: *const AST.Node,
    base: *const AST.Node,
) AstError!bool {
    for (try contractHierarchy(contract)) |candidate|
        if (candidate == base) return true;
    return false;
}

pub fn contractConstructor(contract: *const AST.Node) ?*const AST.Node {
    if (contract.nodeKind() != .contract_definition) return null;
    for (contract.payload.contract_definition.sub_nodes) |member|
        if (member.nodeKind() == .function_definition and
            member.payload.function_definition.kind == .Constructor) return member;
    return null;
}

pub fn contractCanBeDeployed(contract: *const AST.Node) bool {
    if (contract.nodeKind() != .contract_definition) return false;
    const value = contract.payload.contract_definition;
    return !value.abstract and value.contract_kind != .Interface;
}

fn contractSpecialFunction(
    contract: *const AST.Node,
    kind: AST.Token,
) AstError!?*const AST.Node {
    for (try contractHierarchy(contract)) |base|
        for (base.payload.contract_definition.sub_nodes) |member|
            if (member.nodeKind() == .function_definition and
                member.payload.function_definition.kind == kind) return member;
    return null;
}

pub fn contractFallbackFunction(contract: *const AST.Node) AstError!?*const AST.Node {
    return contractSpecialFunction(contract, .Fallback);
}

pub fn contractReceiveFunction(contract: *const AST.Node) AstError!?*const AST.Node {
    return contractSpecialFunction(contract, .Receive);
}

pub fn superContract(
    contract: *const AST.Node,
    most_derived_contract: *const AST.Node,
) AstError!?*const AST.Node {
    const hierarchy = try contractHierarchy(most_derived_contract);
    for (hierarchy, 0..) |candidate, index| {
        if (candidate != contract) continue;
        if (index + 1 == hierarchy.len) return null;
        if (hierarchy[index + 1] == contract) return error.InvalidAst;
        return hierarchy[index + 1];
    }
    return error.InvalidAst;
}

pub fn nextConstructor(
    contract: *const AST.Node,
    most_derived_contract: *const AST.Node,
) AstError!?*const AST.Node {
    var next = (try superContract(contract, most_derived_contract)) orelse return null;
    for (try contractHierarchy(most_derived_contract)) |candidate| {
        if (candidate != next) continue;
        if (contractConstructor(candidate)) |constructor| return constructor;
        next = (try superContract(candidate, most_derived_contract)) orelse return null;
    }
    return null;
}

pub fn definedFunctionsByNameAlloc(
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
    name: []const u8,
) AstError![]*const AST.Node {
    if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    for (contract.payload.contract_definition.sub_nodes) |member|
        if (member.nodeKind() == .function_definition and
            std.mem.eql(
                u8,
                member.payload.function_definition.callable.declaration.name,
                name,
            )) try result.append(allocator, member);
    return result.toOwnedSlice(allocator);
}

pub fn fullyQualifiedContractNameAlloc(
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
) AstError![]u8 {
    if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
    const source_name = sourceUnitName(contract) orelse return error.MissingAnnotation;
    return std.fmt.allocPrint(
        allocator,
        "{s}:{s}",
        .{ source_name, contract.payload.contract_definition.declaration.name },
    );
}

fn annotatedVariableType(variable: *const AST.Node) AstError!*const Types.Type {
    if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
    return (variableAnnotation(variable) orelse return error.MissingAnnotation).type_ref orelse
        error.MissingAnnotation;
}

fn annotatedTypeName(type_name: *const AST.Node) AstError!*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(type_name) orelse
        return error.MissingAnnotation;
    return switch (annotation.*) {
        .type_name => |value| value.type_ref orelse error.MissingAnnotation,
        else => error.InvalidAst,
    };
}

pub fn typeNameType(type_name: *const AST.Node) AstError!*const Types.Type {
    if (!type_name.isTypeName()) return error.InvalidAst;
    return annotatedTypeName(type_name);
}

fn modifierType(
    provider: *TypeProviderModule.TypeProvider,
    modifier: *const AST.Node,
) AstError!*const Types.Type {
    if (modifier.nodeKind() != .modifier_definition) return error.InvalidAst;
    const parameters_node = modifier.payload.modifier_definition.callable.parameters;
    if (parameters_node.nodeKind() != .parameter_list) return error.InvalidAst;
    const parameters = parameters_node.payload.parameter_list.parameters;
    const types = try provider.backing_allocator.alloc(*const Types.Type, parameters.len);
    defer provider.backing_allocator.free(types);
    for (parameters, types) |parameter, *target|
        target.* = try annotatedVariableType(parameter);
    return provider.modifier(types);
}

/// Type of an expression that directly references a declaration. The optional
/// result preserves the upstream experimental `TypeDefinition::type()` null.
pub fn declarationType(
    provider: *TypeProviderModule.TypeProvider,
    declaration: *const AST.Node,
) AstError!?*const Types.Type {
    return switch (declaration.payload) {
        .import_directive => blk: {
            const annotation = ASTAnnotations.annotationConst(declaration) orelse
                return error.MissingAnnotation;
            const imported = switch (annotation.*) {
                .import => |value| value.source_unit orelse return error.MissingAnnotation,
                else => return error.InvalidAst,
            };
            break :blk try provider.module(imported);
        },
        .contract_definition => try provider.typeType(try provider.contract(declaration, false)),
        .struct_definition => blk: {
            const annotation = ASTAnnotations.annotationConst(declaration) orelse
                return error.MissingAnnotation;
            const recursive = switch (annotation.*) {
                .struct_declaration => |value| value.recursive,
                else => return error.InvalidAst,
            };
            if (recursive == null) return error.MissingAnnotation;
            break :blk try provider.typeType(try provider.structType(declaration, .Storage));
        },
        .enum_definition => try provider.typeType(try provider.enumType(declaration)),
        .enum_value => blk: {
            const enclosing = scope(declaration) orelse return error.MissingAnnotation;
            if (enclosing.nodeKind() != .enum_definition) return error.InvalidAst;
            break :blk try provider.enumType(enclosing);
        },
        .user_defined_value_type_definition => |value| try provider.typeType(
            try provider.userDefinedValueType(
                declaration,
                try annotatedTypeName(value.underlying_type),
            ),
        ),
        .function_definition => blk: {
            const visibility = declaration.effectiveVisibility() orelse return error.InvalidAst;
            if (visibility == .External) return error.InvalidAst;
            break :blk try provider.functionFromDefinition(declaration, .Internal);
        },
        .modifier_definition => try modifierType(provider, declaration),
        .event_definition => try provider.functionFromEvent(declaration),
        .error_definition => try provider.functionFromError(declaration),
        .variable_declaration => try annotatedVariableType(declaration),
        .magic_variable_declaration => |value| if (value.type_ref) |type_ref|
            @as(*const Types.Type, @ptrCast(@alignCast(type_ref)))
        else
            return error.MissingAnnotation,
        .type_definition => null,
        else => return error.InvalidAst,
    };
}

pub fn declarationFunctionType(
    provider: *TypeProviderModule.TypeProvider,
    declaration: *const AST.Node,
    internal: bool,
) AstError!?*const Types.Type {
    return switch (declaration.payload) {
        .function_definition => blk: {
            const visibility = declaration.effectiveVisibility() orelse return error.InvalidAst;
            if (internal) switch (visibility) {
                .Private, .Internal, .Public => break :blk try provider.functionFromDefinition(
                    declaration,
                    .Internal,
                ),
                .External => break :blk null,
                .Default => return error.InvalidAst,
            } else switch (visibility) {
                .Private, .Internal => break :blk null,
                .Public, .External => break :blk try provider.functionFromDefinition(
                    declaration,
                    .External,
                ),
                .Default => return error.InvalidAst,
            }
        },
        .variable_declaration => if (internal or !declaration.isPublic())
            null
        else
            try provider.functionFromVariable(declaration),
        .event_definition => if (internal) try provider.functionFromEvent(declaration) else null,
        .error_definition => if (internal) try provider.functionFromError(declaration) else null,
        .magic_variable_declaration => |value| blk: {
            const type_ref = value.type_ref orelse return error.MissingAnnotation;
            const concrete: *const Types.Type = @ptrCast(@alignCast(type_ref));
            if (concrete.category() != .Function) return error.InvalidAst;
            break :blk concrete;
        },
        else => null,
    };
}

pub fn functionTypeViaContractName(
    provider: *TypeProviderModule.TypeProvider,
    function: *const AST.Node,
    access_kind: AST.ContractNameAccessKind,
) AstError!*const Types.Type {
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    const visibility = function.effectiveVisibility() orelse return error.InvalidAst;
    switch (access_kind) {
        .Local => {
            if (functionIsLibrary(function) or
                @intFromEnum(visibility) <= @intFromEnum(AST.Visibility.Private))
                return error.InvalidAst;
            if (!function.isVisibleInContract() or
                !function.payload.function_definition.implemented())
                return provider.functionFromDefinition(function, .Declaration);
            return (try declarationType(provider, function)) orelse error.InvalidAst;
        },
        .Foreign => {
            if (functionIsLibrary(function) or
                !function.isVisibleViaContractTypeAccess()) return error.InvalidAst;
            return provider.functionFromDefinition(function, .Declaration);
        },
        .Library => {
            if (!functionIsLibrary(function)) return error.InvalidAst;
            if (!function.isPublic())
                return (try declarationType(provider, function)) orelse error.InvalidAst;
            const internal = try provider.functionFromDefinition(function, .Internal);
            return TypeBehavior.asExternallyCallableFunction(
                provider,
                internal.payload.Function,
                true,
            );
        },
    }
}

pub fn declarationTypeViaContractName(
    provider: *TypeProviderModule.TypeProvider,
    declaration: *const AST.Node,
    access_kind: AST.ContractNameAccessKind,
) AstError!?*const Types.Type {
    if (!declaration.isVisibleViaContractName(access_kind)) return error.InvalidAst;
    if (declaration.nodeKind() == .function_definition)
        return try functionTypeViaContractName(provider, declaration, access_kind);
    return declarationType(provider, declaration);
}

pub fn functionTypeWhenAttached(
    provider: *TypeProviderModule.TypeProvider,
    function: *const AST.Node,
) AstError!*const Types.Type {
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    const value = function.payload.function_definition;
    if (!value.free and !functionIsLibrary(function)) return error.InvalidAst;
    if (functionIsLibrary(function))
        return functionTypeViaContractName(provider, function, .Library);
    return (try declarationType(provider, function)) orelse error.InvalidAst;
}

pub fn operationUserDefinedFunctionType(
    provider: *TypeProviderModule.TypeProvider,
    operation: *const AST.Node,
) AstError!?*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(operation) orelse
        return error.MissingAnnotation;
    const user_defined = switch (annotation.*) {
        .operation => |value| value.user_defined_function.value,
        .binary_operation => |value| value.operation.user_defined_function.value,
        else => return error.InvalidAst,
    } orelse return error.MissingAnnotation;
    const function = user_defined orelse return null;
    return functionTypeWhenAttached(provider, function);
}

pub fn functionExternalSignatureAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    function: *const AST.Node,
) AstError![]u8 {
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    const function_type = try provider.functionFromDefinition(function, .Internal);
    return TypeBehavior.externalSignatureAlloc(
        provider,
        allocator,
        function_type.payload.Function,
    );
}

pub fn declarationExternalIdentifierHexAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    declaration: *const AST.Node,
) AstError![]u8 {
    const function_type = switch (declaration.payload) {
        .function_definition => try provider.functionFromDefinition(declaration, .Internal),
        .variable_declaration => blk: {
            if (!isStateVariable(declaration) or !declaration.isPublic())
                return error.InvalidAst;
            break :blk try provider.functionFromVariable(declaration);
        },
        else => return error.InvalidAst,
    };
    return TypeBehavior.externalIdentifierHexAlloc(
        provider,
        allocator,
        function_type.payload.Function,
    );
}

pub fn resolveFunctionVirtual(
    provider: *TypeProviderModule.TypeProvider,
    function: *const AST.Node,
    most_derived_contract: *const AST.Node,
    search_start: ?*const AST.Node,
) AstError!*const AST.Node {
    if (function.nodeKind() != .function_definition or
        function.payload.function_definition.kind == .Constructor or
        function.payload.function_definition.callable.declaration.name.len == 0)
        return error.InvalidAst;
    if (search_start == null and !functionVirtualSemantics(function)) return function;
    const value = function.payload.function_definition;
    if (value.free or !value.ordinary() or functionIsLibrary(function)) return error.InvalidAst;
    const original = try provider.functionFromDefinition(function, .Internal);
    const external = try TypeBehavior.asExternallyCallableFunction(
        provider,
        original.payload.Function,
        false,
    );
    var found_start = search_start == null;
    for (try contractHierarchy(most_derived_contract)) |contract| {
        if (!found_start and contract != search_start.?) continue;
        found_start = true;
        for (contract.payload.contract_definition.sub_nodes) |candidate| {
            if (candidate.nodeKind() != .function_definition or
                !std.mem.eql(
                    u8,
                    candidate.payload.function_definition.callable.declaration.name,
                    value.callable.declaration.name,
                )) continue;
            if (!candidate.payload.function_definition.implemented() and search_start != null)
                continue;
            const candidate_internal = try provider.functionFromDefinition(candidate, .Internal);
            const candidate_external = try TypeBehavior.asExternallyCallableFunction(
                provider,
                candidate_internal.payload.Function,
                false,
            );
            if (!TypeBehavior.functionHasEqualParameterTypes(
                candidate_external.payload.Function,
                external.payload.Function,
            )) continue;
            if (!TypeBehavior.functionHasEqualParameterTypes(
                candidate_internal.payload.Function,
                original.payload.Function,
            )) return error.InvalidAst;
            return candidate;
        }
    }
    return error.VirtualDeclarationNotFound;
}

pub fn resolveModifierVirtual(
    modifier: *const AST.Node,
    most_derived_contract: *const AST.Node,
    search_start: ?*const AST.Node,
) AstError!*const AST.Node {
    if (modifier.nodeKind() != .modifier_definition or search_start != null)
        return error.InvalidAst;
    const value = modifier.payload.modifier_definition;
    if (!value.callable.marked_virtual) return modifier;
    const enclosing = scope(modifier) orelse return error.MissingAnnotation;
    if (enclosing.nodeKind() != .contract_definition or
        enclosing.payload.contract_definition.contract_kind == .Library)
        return error.InvalidAst;
    for (try contractHierarchy(most_derived_contract)) |contract|
        for (contract.payload.contract_definition.sub_nodes) |candidate|
            if (candidate.nodeKind() == .modifier_definition and
                std.mem.eql(
                    u8,
                    candidate.payload.modifier_definition.callable.declaration.name,
                    value.callable.declaration.name,
                )) return candidate;
    return error.VirtualDeclarationNotFound;
}

pub fn resolveCallableVirtual(
    provider: *TypeProviderModule.TypeProvider,
    callable: *const AST.Node,
    most_derived_contract: *const AST.Node,
    search_start: ?*const AST.Node,
) AstError!*const AST.Node {
    return switch (callable.nodeKind()) {
        .function_definition => resolveFunctionVirtual(
            provider,
            callable,
            most_derived_contract,
            search_start,
        ),
        .modifier_definition => resolveModifierVirtual(
            callable,
            most_derived_contract,
            search_start,
        ),
        .event_definition, .error_definition => callable,
        else => error.InvalidAst,
    };
}

pub fn resolveFunctionCall(
    provider: *TypeProviderModule.TypeProvider,
    function_call: *const AST.Node,
    most_derived_contract: ?*const AST.Node,
) AstError!?*const AST.Node {
    if (function_call.nodeKind() != .function_call) return error.InvalidAst;
    const expression = function_call.payload.function_call.expression;
    const function = referencedDeclaration(expression) orelse return null;
    if (function.nodeKind() != .function_definition) return null;
    switch (expression.payload) {
        .member_access => |member| {
            const annotation = ASTAnnotations.annotationConst(expression) orelse
                return error.MissingAnnotation;
            const lookup = switch (annotation.*) {
                .member_access => |value| value.required_lookup.value orelse
                    return error.MissingAnnotation,
                else => return error.InvalidAst,
            };
            if (lookup == .Super) {
                const expression_type = expressionType(member.expression) orelse
                    return error.MissingAnnotation;
                const type_type = expression_type.asTypeType() orelse return error.InvalidAst;
                const contract_type = switch (type_type.actual_type.payload) {
                    .Contract => |value| value,
                    else => return error.InvalidAst,
                };
                if (!contract_type.is_super) return error.InvalidAst;
                const derived = most_derived_contract orelse return error.InvalidAst;
                const start = (try superContract(contract_type.declaration, derived)) orelse
                    return error.VirtualDeclarationNotFound;
                return resolveFunctionVirtual(provider, function, derived, start);
            }
            if (lookup != .Static) return error.InvalidAst;
        },
        .identifier => {
            const annotation = ASTAnnotations.annotationConst(expression) orelse
                return error.MissingAnnotation;
            const lookup = switch (annotation.*) {
                .identifier => |value| value.required_lookup.value orelse
                    return error.MissingAnnotation,
                else => return error.InvalidAst,
            };
            if (lookup != .Virtual) return error.InvalidAst;
            if (functionVirtualSemantics(function)) {
                const derived = most_derived_contract orelse return error.InvalidAst;
                return resolveFunctionVirtual(provider, function, derived, null);
            }
        },
        else => return error.InvalidAst,
    }
    return function;
}

fn appendUniqueNode(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(*const AST.Node),
    node: *const AST.Node,
) std.mem.Allocator.Error!void {
    for (output.items) |existing| if (existing == node) return;
    try output.append(allocator, node);
}

fn sortNodesById(nodes: []*const AST.Node) void {
    std.sort.insertion(*const AST.Node, nodes, {}, nodeIdLessThan);
}

pub fn contractDefinedInterfaceEventsAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
) AstError![]*const AST.Node {
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    var signatures: std.ArrayList([]u8) = .empty;
    defer {
        for (signatures.items) |signature| allocator.free(signature);
        signatures.deinit(allocator);
    }
    for (try contractHierarchy(contract)) |base|
        for (base.payload.contract_definition.sub_nodes) |member| {
            if (member.nodeKind() != .event_definition) continue;
            const event_type = try provider.functionFromEvent(member);
            const signature = try TypeBehavior.externalSignatureAlloc(
                provider,
                allocator,
                event_type.payload.Function,
            );
            var seen = false;
            for (signatures.items) |existing|
                if (std.mem.eql(u8, existing, signature)) {
                    seen = true;
                    break;
                };
            if (seen) {
                allocator.free(signature);
                continue;
            }
            try signatures.append(allocator, signature);
            try result.append(allocator, member);
        };
    return result.toOwnedSlice(allocator);
}

pub fn contractUsedInterfaceEventsAlloc(
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
) AstError![]*const AST.Node {
    const annotation = contractAnnotation(contract) orelse return error.MissingAnnotation;
    if (!annotation.creation_call_graph.isSet() or
        !annotation.deployed_call_graph.isSet()) return error.MissingCallGraph;
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    // Read the event list merged from the creation and deployed call graphs
    // during analysis.
    for (annotation.interface_events.items) |event|
        try appendUniqueNode(allocator, &result, event);
    sortNodesById(result.items);
    return result.toOwnedSlice(allocator);
}

pub fn contractInterfaceEventsAlloc(
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
    require_call_graph: bool,
) AstError![]*const AST.Node {
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    for (try contractHierarchy(contract)) |base|
        for (base.payload.contract_definition.sub_nodes) |member|
            if (member.nodeKind() == .event_definition)
                try appendUniqueNode(allocator, &result, member);
    const annotation = contractAnnotation(contract) orelse return error.MissingAnnotation;
    if (annotation.creation_call_graph.isSet() != annotation.deployed_call_graph.isSet())
        return error.MissingCallGraph;
    if (require_call_graph and !annotation.creation_call_graph.isSet())
        return error.MissingCallGraph;
    if (annotation.creation_call_graph.isSet())
        for (annotation.interface_events.items) |event|
            try appendUniqueNode(allocator, &result, event);
    sortNodesById(result.items);
    return result.toOwnedSlice(allocator);
}

pub fn contractInterfaceErrorsAlloc(
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
    require_call_graph: bool,
) AstError![]*const AST.Node {
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    for (try contractHierarchy(contract)) |base|
        for (base.payload.contract_definition.sub_nodes) |member|
            if (member.nodeKind() == .error_definition)
                try appendUniqueNode(allocator, &result, member);
    const annotation = contractAnnotation(contract) orelse return error.MissingAnnotation;
    if (annotation.creation_call_graph.isSet() != annotation.deployed_call_graph.isSet())
        return error.MissingCallGraph;
    if (require_call_graph and !annotation.creation_call_graph.isSet())
        return error.MissingCallGraph;
    if (annotation.creation_call_graph.isSet())
        for (annotation.interface_errors.items) |error_node|
            try appendUniqueNode(allocator, &result, error_node);
    sortNodesById(result.items);
    return result.toOwnedSlice(allocator);
}

pub fn contractInterfaceFunctionListAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
    include_inherited_functions: bool,
) AstError![]InterfaceFunction {
    var result: std.ArrayList(InterfaceFunction) = .empty;
    errdefer result.deinit(allocator);
    var signatures: std.ArrayList([]u8) = .empty;
    defer {
        for (signatures.items) |signature| allocator.free(signature);
        signatures.deinit(allocator);
    }
    for (try contractHierarchy(contract)) |base| {
        if (!include_inherited_functions and base != contract) continue;
        for (base.payload.contract_definition.sub_nodes) |member| {
            const raw_type: ?*const Types.Type = switch (member.payload) {
                .function_definition => if (member.isPartOfExternalInterface())
                    try provider.functionFromDefinition(member, .External)
                else
                    null,
                .variable_declaration => if (member.isPartOfExternalInterface())
                    try provider.functionFromVariable(member)
                else
                    null,
                else => null,
            };
            const raw = raw_type orelse continue;
            _ = (try TypeBehavior.interfaceFunctionType(
                provider,
                raw.payload.Function,
            )) orelse continue;
            const signature = try TypeBehavior.externalSignatureAlloc(
                provider,
                allocator,
                raw.payload.Function,
            );
            var seen = false;
            for (signatures.items) |existing|
                if (std.mem.eql(u8, existing, signature)) {
                    seen = true;
                    break;
                };
            if (seen) {
                allocator.free(signature);
                continue;
            }
            try signatures.append(allocator, signature);
            try result.append(allocator, .{
                .selector = FunctionSelector.selectorFromSignatureH32(signature),
                // Upstream uses the transformed type only as an eligibility
                // check. The interface list retains the original declaration
                // type for ABI compatibility and NatSpec consumers.
                .function_type = raw,
            });
        }
    }
    return result.toOwnedSlice(allocator);
}

pub fn contractInterfaceFunctionsAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
    include_inherited_functions: bool,
) AstError![]InterfaceFunction {
    const result = try contractInterfaceFunctionListAlloc(
        provider,
        allocator,
        contract,
        include_inherited_functions,
    );
    errdefer allocator.free(result);
    for (result, 0..) |entry, index|
        for (result[0..index]) |earlier|
            if (entry.selector.eql(&earlier.selector)) return error.SelectorCollision;
    std.sort.insertion(InterfaceFunction, result, {}, struct {
        fn lessThan(_: void, left: InterfaceFunction, right: InterfaceFunction) bool {
            return left.selector.lessThan(&right.selector);
        }
    }.lessThan);
    return result;
}

pub fn contractInterfaceId(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
) AstError!u32 {
    const functions = try contractInterfaceFunctionListAlloc(
        provider,
        allocator,
        contract,
        false,
    );
    defer allocator.free(functions);
    var result: u32 = 0;
    for (functions) |function| result ^= function.selector.toInteger();
    return result;
}

/// Returns the visibility after applying the declaration kind's upstream
/// default. Constructors are never ordinary contract members, but retaining a
/// concrete value here keeps the common declaration predicates total.
pub fn effectiveVisibility(declaration: *const AST.Node) ?AST.Visibility {
    return declaration.effectiveVisibility();
}

pub fn isPublic(declaration: *const AST.Node) bool {
    return declaration.isPublic();
}

pub fn isVisibleAsLibraryMember(declaration: *const AST.Node) bool {
    return declaration.isVisibleAsLibraryMember();
}

pub fn isVisibleViaContractTypeAccess(declaration: *const AST.Node) bool {
    return declaration.isVisibleViaContractTypeAccess();
}

pub fn isPartOfExternalInterface(declaration: *const AST.Node) bool {
    return declaration.isPartOfExternalInterface();
}

pub fn declarationIsLValue(declaration: *const AST.Node) bool {
    return declaration.isLValue();
}

/// Mirrors `Declaration::isVisibleInContract`, including the function
/// override which excludes constructors, fallback, and receive declarations.
pub fn isVisibleInContract(declaration: *const AST.Node) bool {
    return declaration.isVisibleInContract();
}

/// Structs, enums, events, and errors use the explicit upstream overrides;
/// other declarations follow the visibility lattice on `Declaration`.
pub fn isVisibleInDerivedContracts(declaration: *const AST.Node) bool {
    return declaration.isVisibleInDerivedContracts();
}

pub fn isStateVariable(declaration: *const AST.Node) bool {
    return declaration.nodeKind() == .variable_declaration and
        if (scope(declaration)) |enclosing|
            enclosing.nodeKind() == .contract_definition
        else
            false;
}

pub fn isLocalVariable(declaration: *const AST.Node) bool {
    if (declaration.nodeKind() != .variable_declaration) return false;
    const enclosing = scope(declaration) orelse return false;
    return switch (enclosing.nodeKind()) {
        .function_type_name,
        .function_definition,
        .modifier_definition,
        .event_definition,
        .error_definition,
        .block,
        .try_catch_clause,
        .for_statement,
        => true,
        else => false,
    };
}

pub fn isPublicFunctionOrEvent(declaration: *const AST.Node) bool {
    return switch (declaration.payload) {
        .function_definition => |value| !value.free and isPublic(declaration),
        .event_definition => true,
        else => false,
    };
}

/// Mirrors `Declaration::isVisibleAsUnqualifiedName` after `Scoper` has run.
pub fn isVisibleAsUnqualifiedName(declaration: *const AST.Node) bool {
    const enclosing = scope(declaration) orelse return true;
    switch (enclosing.nodeKind()) {
        .struct_definition,
        .enum_definition,
        .event_definition,
        .error_definition,
        => return false,
        .function_definition => {
            if (!enclosing.payload.function_definition.implemented()) return false;
        },
        else => {},
    }
    return true;
}

pub fn literalValueWithoutUnderscoresAlloc(
    allocator: std.mem.Allocator,
    literal: AST.Literal,
) std.mem.Allocator.Error![]u8 {
    var output = try allocator.alloc(u8, literal.value.len);
    var length: usize = 0;
    for (literal.value) |byte| {
        if (byte == '_') continue;
        output[length] = byte;
        length += 1;
    }
    if (length == output.len) return output;
    return allocator.realloc(output, length);
}

pub fn literalIsHexNumber(literal: AST.Literal) bool {
    return literal.token == .Number and literal.value.len >= 2 and
        literal.value[0] == '0' and
        literal.value[1] == 'x';
}

pub fn literalLooksLikeAddress(literal: AST.Literal) bool {
    if (literal.sub_denomination != .None or !literalIsHexNumber(literal)) return false;
    var cleaned_length: usize = 0;
    for (literal.value) |byte| cleaned_length += @intFromBool(byte != '_');
    const difference = if (cleaned_length > 42)
        cleaned_length - 42
    else
        42 - cleaned_length;
    return difference <= 1;
}

pub fn literalPassesAddressChecksum(
    allocator: std.mem.Allocator,
    literal: AST.Literal,
) AstError!bool {
    if (!literalIsHexNumber(literal)) return error.InvalidAst;
    const cleaned = try literalValueWithoutUnderscoresAlloc(allocator, literal);
    defer allocator.free(cleaned);
    return CommonData.passesAddressChecksum(cleaned, true);
}

pub fn literalChecksummedAddressAlloc(
    allocator: std.mem.Allocator,
    literal: AST.Literal,
) AstError![]u8 {
    if (!literalIsHexNumber(literal)) return error.InvalidAst;
    const cleaned = try literalValueWithoutUnderscoresAlloc(allocator, literal);
    defer allocator.free(cleaned);
    const address = cleaned[2..];
    if (address.len > 40) return allocator.dupe(u8, "");
    var padded: [40]u8 = [_]u8{'0'} ** 40;
    @memcpy(padded[40 - address.len ..], address);
    return CommonData.getChecksummedAddressAlloc(allocator, &padded);
}

pub fn sortedFunctionCallArgumentsAlloc(
    provider: *TypeProviderModule.TypeProvider,
    allocator: std.mem.Allocator,
    function_call: *const AST.Node,
) AstError![]*const AST.Node {
    if (function_call.nodeKind() != .function_call) return error.InvalidAst;
    const call = function_call.payload.function_call;
    if (call.names.len == 0)
        return allocator.dupe(*const AST.Node, call.arguments);
    if (call.names.len != call.arguments.len) return error.InvalidNamedArguments;
    const annotation = ASTAnnotations.annotationConst(function_call) orelse
        return error.MissingAnnotation;
    const kind = switch (annotation.*) {
        .function_call => |value| value.kind.value orelse return error.MissingAnnotation,
        else => return error.InvalidAst,
    };
    const function_type = if (kind == .StructConstructorCall) blk: {
        const expression_type = expressionType(call.expression) orelse
            return error.MissingAnnotation;
        const actual = expression_type.asTypeType() orelse return error.InvalidAst;
        if (actual.actual_type.category() != .Struct) return error.InvalidAst;
        break :blk try TypeBehavior.structConstructorType(provider, actual.actual_type);
    } else expressionType(call.expression) orelse return error.MissingAnnotation;
    const function = function_type.asFunction() orelse return error.InvalidAst;
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    for (function.parameterNames()) |parameter_name| {
        var found: ?*const AST.Node = null;
        for (call.names, call.arguments) |name, argument|
            if (std.mem.eql(u8, parameter_name, name)) {
                if (found != null) return error.InvalidNamedArguments;
                found = argument;
            };
        try result.append(allocator, found orelse return error.InvalidNamedArguments);
    }
    if (!function.options.arbitrary_parameters and
        (call.arguments.len != function.parameterTypes().len or
            call.arguments.len != result.items.len)) return error.InvalidNamedArguments;
    return result.toOwnedSlice(allocator);
}

pub fn findTryClause(try_statement: AST.TryStatement, error_name: ?[]const u8) ?*const AST.Node {
    if (try_statement.clauses.len <= 1) return null;
    for (try_statement.clauses[1..]) |clause_node| {
        const clause = switch (clause_node.payload) {
            .try_catch_clause => |*value| value,
            else => continue,
        };
        if (error_name) |name| {
            if (std.mem.eql(u8, clause.error_name, name)) return clause_node;
        } else if (clause.error_name.len == 0) {
            return clause_node;
        }
    }
    return null;
}

pub fn trySuccessClause(try_statement: AST.TryStatement) AstError!*const AST.Node {
    if (try_statement.clauses.len == 0) return error.InvalidAst;
    const clause = try_statement.clauses[0];
    if (clause.nodeKind() != .try_catch_clause) return error.InvalidAst;
    return clause;
}

pub fn tryPanicClause(try_statement: AST.TryStatement) ?*const AST.Node {
    return findTryClause(try_statement, "Panic");
}

pub fn tryErrorClause(try_statement: AST.TryStatement) ?*const AST.Node {
    return findTryClause(try_statement, "Error");
}

pub fn tryFallbackClause(try_statement: AST.TryStatement) ?*const AST.Node {
    return findTryClause(try_statement, null);
}

pub fn appendChildren(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(*const AST.Node),
    node: *const AST.Node,
) std.mem.Allocator.Error!void {
    switch (node.payload) {
        .source_unit => |value| try output.appendSlice(allocator, value.nodes),
        .import_directive => |value| {
            for (value.symbol_aliases) |alias| try output.append(allocator, alias.symbol);
        },
        .contract_definition => |value| {
            if (value.documentation) |child| try output.append(allocator, child);
            try output.appendSlice(allocator, value.base_contracts);
            if (value.storage_layout_specifier) |child| try output.append(allocator, child);
            try output.appendSlice(allocator, value.sub_nodes);
        },
        .storage_layout_specifier => |value| try output.append(allocator, value.base_slot_expression),
        .inheritance_specifier => |value| {
            try output.append(allocator, value.base_name);
            if (value.arguments) |arguments| try output.appendSlice(allocator, arguments);
        },
        .using_for_directive => |value| {
            for (value.functions_and_operators) |entry| try output.append(allocator, entry.function_or_library);
            if (value.type_name) |child| try output.append(allocator, child);
        },
        .struct_definition => |value| try output.appendSlice(allocator, value.members),
        .enum_definition => |value| try output.appendSlice(allocator, value.members),
        .user_defined_value_type_definition => |value| try output.append(allocator, value.underlying_type),
        .parameter_list => |value| try output.appendSlice(allocator, value.parameters),
        .override_specifier => |value| try output.appendSlice(allocator, value.overrides),
        .function_definition => |value| {
            if (value.documentation) |child| try output.append(allocator, child);
            if (value.callable.overrides) |child| try output.append(allocator, child);
            try output.append(allocator, value.callable.parameters);
            if (value.callable.return_parameters) |child| try output.append(allocator, child);
            if (value.experimental_return_expression) |child| try output.append(allocator, child);
            try output.appendSlice(allocator, value.modifiers);
            if (value.body) |child| try output.append(allocator, child);
        },
        .variable_declaration => |value| {
            if (value.type_name) |child| try output.append(allocator, child);
            if (value.experimental_type_expression) |child| try output.append(allocator, child);
            if (value.overrides) |child| try output.append(allocator, child);
            if (value.value) |child| try output.append(allocator, child);
        },
        .modifier_definition => |value| {
            if (value.documentation) |child| try output.append(allocator, child);
            try output.append(allocator, value.callable.parameters);
            if (value.callable.overrides) |child| try output.append(allocator, child);
            if (value.body) |child| try output.append(allocator, child);
        },
        .modifier_invocation => |value| {
            try output.append(allocator, value.modifier_name);
            if (value.arguments) |arguments| try output.appendSlice(allocator, arguments);
        },
        .event_definition => |value| {
            if (value.documentation) |child| try output.append(allocator, child);
            try output.append(allocator, value.callable.parameters);
        },
        .error_definition => |value| {
            if (value.documentation) |child| try output.append(allocator, child);
            try output.append(allocator, value.callable.parameters);
        },
        .user_defined_type_name => |value| try output.append(allocator, value.path_node),
        .function_type_name => |value| {
            try output.append(allocator, value.parameter_types);
            try output.append(allocator, value.return_types);
        },
        .mapping => |value| {
            try output.append(allocator, value.key_type);
            try output.append(allocator, value.value_type);
        },
        .array_type_name => |value| {
            try output.append(allocator, value.base_type);
            if (value.length) |child| try output.append(allocator, child);
        },
        .block => |value| try output.appendSlice(allocator, value.statements),
        .if_statement => |value| {
            try output.append(allocator, value.condition);
            try output.append(allocator, value.true_body);
            if (value.false_body) |child| try output.append(allocator, child);
        },
        .try_catch_clause => |value| {
            if (value.parameters) |child| try output.append(allocator, child);
            try output.append(allocator, value.block);
        },
        .try_statement => |value| {
            try output.append(allocator, value.external_call);
            try output.appendSlice(allocator, value.clauses);
        },
        .while_statement => |value| {
            try output.append(allocator, value.condition);
            try output.append(allocator, value.body);
        },
        .for_statement => |value| {
            if (value.initialization_expression) |child| try output.append(allocator, child);
            if (value.condition) |child| try output.append(allocator, child);
            if (value.loop_expression) |child| try output.append(allocator, child);
            try output.append(allocator, value.body);
        },
        .return_statement => |value| if (value.expression) |child| try output.append(allocator, child),
        .revert_statement => |value| try output.append(allocator, value.error_call),
        .emit_statement => |value| try output.append(allocator, value.event_call),
        .variable_declaration_statement => |value| {
            for (value.declarations) |child| if (child) |present| try output.append(allocator, present);
            if (value.initial_value) |child| try output.append(allocator, child);
        },
        .expression_statement => |value| try output.append(allocator, value.expression),
        .conditional => |value| {
            try output.append(allocator, value.condition);
            try output.append(allocator, value.true_expression);
            try output.append(allocator, value.false_expression);
        },
        .assignment => |value| {
            try output.append(allocator, value.left_hand_side);
            try output.append(allocator, value.right_hand_side);
        },
        .tuple_expression => |value| for (value.components) |child| if (child) |present| try output.append(allocator, present),
        .unary_operation => |value| try output.append(allocator, value.sub_expression),
        .binary_operation => |value| {
            try output.append(allocator, value.left);
            try output.append(allocator, value.right);
        },
        .function_call => |value| {
            try output.append(allocator, value.expression);
            try output.appendSlice(allocator, value.arguments);
        },
        .function_call_options => |value| {
            try output.append(allocator, value.expression);
            try output.appendSlice(allocator, value.options);
        },
        .new_expression => |value| try output.append(allocator, value.type_name),
        .member_access => |value| try output.append(allocator, value.expression),
        .index_access => |value| {
            try output.append(allocator, value.base);
            if (value.index) |child| try output.append(allocator, child);
        },
        .index_range_access => |value| {
            try output.append(allocator, value.base);
            if (value.start) |child| try output.append(allocator, child);
            if (value.end) |child| try output.append(allocator, child);
        },
        // Upstream intentionally treats `ElementaryTypeNameExpression` as a
        // visitor leaf even though it retains its parsed type-name node.
        .elementary_type_name_expression => {},
        .type_class_definition => |value| {
            try output.append(allocator, value.type_variable);
            if (value.documentation) |child| try output.append(allocator, child);
            try output.appendSlice(allocator, value.sub_nodes);
        },
        .type_class_instantiation => |value| {
            try output.append(allocator, value.type_constructor);
            if (value.argument_sorts) |child| try output.append(allocator, child);
            try output.append(allocator, value.type_class);
            try output.appendSlice(allocator, value.sub_nodes);
        },
        .type_definition => |value| {
            if (value.arguments) |child| try output.append(allocator, child);
            if (value.type_expression) |child| try output.append(allocator, child);
        },
        .type_class_name => |value| switch (value.name) {
            .identifier_path => |child| try output.append(allocator, child),
            .builtin => {},
        },
        .for_all_quantifier => |value| {
            try output.append(allocator, value.type_variable_declarations);
            try output.append(allocator, value.quantified_declaration);
        },
        .pragma_directive,
        .structured_documentation,
        .identifier_path,
        .enum_value,
        .magic_variable_declaration,
        .elementary_type_name,
        .inline_assembly,
        .placeholder_statement,
        .continue_statement,
        .break_statement,
        .throw_statement,
        .identifier,
        .literal,
        .builtin,
        => {},
    }
}

pub fn collectPreorderAlloc(
    allocator: std.mem.Allocator,
    root: *const AST.Node,
) std.mem.Allocator.Error![]*const AST.Node {
    var result: std.ArrayList(*const AST.Node) = .empty;
    errdefer result.deinit(allocator);
    var pending: std.ArrayList(*const AST.Node) = .empty;
    defer pending.deinit(allocator);
    try pending.append(allocator, root);
    while (pending.pop()) |node| {
        try result.append(allocator, node);
        var children: std.ArrayList(*const AST.Node) = .empty;
        defer children.deinit(allocator);
        try appendChildren(allocator, &children, node);
        var index = children.items.len;
        while (index != 0) {
            index -= 1;
            try pending.append(allocator, children.items[index]);
        }
    }
    return result.toOwnedSlice(allocator);
}

fn testSetScope(
    tree: *AST.Tree,
    node: *AST.Node,
    enclosing: ?*const AST.Node,
) !void {
    const annotation = try ASTAnnotations.ensure(tree, node);
    const scopable = ASTAnnotations.scopable(annotation) orelse return error.InvalidAst;
    scopable.scope = enclosing;
    var current = enclosing;
    while (current) |candidate| {
        if (candidate.nodeKind() == .contract_definition) {
            scopable.contract = candidate;
            break;
        }
        current = scope(candidate);
    }
}

fn testSetVariableType(
    tree: *AST.Tree,
    variable: *AST.Node,
    type_ref: *const Types.Type,
) !void {
    const annotation = try ASTAnnotations.ensure(tree, variable);
    switch (annotation.*) {
        .variable_declaration => |*value| value.type_ref = type_ref,
        else => return error.InvalidAst,
    }
    if (variable.payload.variable_declaration.type_name) |type_name| {
        const type_annotation = try ASTAnnotations.ensure(tree, type_name);
        switch (type_annotation.*) {
            .type_name => |*value| value.type_ref = type_ref,
            else => return error.InvalidAst,
        }
    }
}

fn testSetContractHierarchy(
    tree: *AST.Tree,
    contract: *AST.Node,
    hierarchy: AST.NodeList,
) !void {
    const annotation = try ASTAnnotations.ensure(tree, contract);
    switch (annotation.*) {
        .contract_definition => |*value| value.linearized_base_contracts = hierarchy,
        else => return error.InvalidAst,
    }
}

fn testSetReferencedDeclaration(
    tree: *AST.Tree,
    expression: *AST.Node,
    declaration: *const AST.Node,
    lookup: AST.VirtualLookup,
) !void {
    const annotation = try ASTAnnotations.ensure(tree, expression);
    switch (annotation.*) {
        .identifier => |*value| {
            value.referenced_declaration = declaration;
            try value.required_lookup.assign(lookup);
        },
        .member_access => |*value| {
            value.referenced_declaration = declaration;
            try value.required_lookup.assign(lookup);
        },
        .identifier_path => |*value| {
            value.referenced_declaration = declaration;
            try value.required_lookup.assign(lookup);
        },
        else => return error.InvalidAst,
    }
}

fn testCreateTypedVariable(
    tree: *AST.Tree,
    name: []const u8,
    type_ref: *const Types.Type,
    visibility: AST.Visibility,
) !*AST.Node {
    const type_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try TokenModule.ElementaryTypeNameToken.init(.UInt, 0, 0),
    } });
    const variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = name, .visibility = visibility },
        .type_name = type_name,
    } });
    try testSetVariableType(tree, variable, type_ref);
    return variable;
}

fn testCreateFunction(
    tree: *AST.Tree,
    name: []const u8,
    visibility: AST.Visibility,
    kind: AST.Token,
    marked_virtual: bool,
    implemented: bool,
    parameters: []const *AST.Node,
) !*AST.Node {
    const parameter_list = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, parameters),
    } });
    const return_list = try tree.createNode(.{}, .{ .parameter_list = .{} });
    const body = if (implemented)
        try tree.createNode(.{}, .{ .block = .{} })
    else
        null;
    return tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = name, .visibility = visibility },
            .parameters = parameter_list,
            .return_parameters = return_list,
            .marked_virtual = marked_virtual,
        },
        .kind = kind,
        .body = body,
    } });
}

test "syntax behavior preserves spellings and deterministic child order" {
    try std.testing.expectEqualStrings("external", try visibilityToString(.External));
    try std.testing.expectEqualStrings("transient", variableLocationToString(.Transient));
    try std.testing.expectEqualStrings("library", contractKindToString(.Library));

    var tree = try AST.Tree.init(std.testing.allocator, "1 + 2", "A.sol");
    defer tree.deinit();
    const one = try tree.createNode(.{}, .{ .literal = .{ .token = .Number, .value = "1" } });
    const two = try tree.createNode(.{}, .{ .literal = .{ .token = .Number, .value = "2" } });
    const add = try tree.createNode(.{}, .{ .binary_operation = .{
        .left = one,
        .operator = .Add,
        .right = two,
    } });
    const preorder = try collectPreorderAlloc(std.testing.allocator, add);
    defer std.testing.allocator.free(preorder);
    try std.testing.expectEqualSlices(i64, &.{ 3, 1, 2 }, &.{
        preorder[0].id,
        preorder[1].id,
        preorder[2].id,
    });
}

test "literal helpers preserve raw syntax semantics" {
    const cleaned = try literalValueWithoutUnderscoresAlloc(std.testing.allocator, .{
        .token = .Number,
        .value = "0x12_ab",
    });
    defer std.testing.allocator.free(cleaned);
    try std.testing.expectEqualStrings("0x12ab", cleaned);
    try std.testing.expect(!literalIsHexNumber(.{ .token = .Number, .value = "0Xff" }));
    try std.testing.expect(!literalIsHexNumber(.{ .token = .HexStringLiteral, .value = "ff" }));
    const checksummed: AST.Literal = .{
        .token = .Number,
        .value = "0x52908400098527886E0F7030069857D2E4169EE7",
    };
    try std.testing.expect(literalLooksLikeAddress(checksummed));
    try std.testing.expect(try literalPassesAddressChecksum(std.testing.allocator, checksummed));
    const padded = try literalChecksummedAddressAlloc(std.testing.allocator, .{
        .token = .Number,
        .value = "0x1",
    });
    defer std.testing.allocator.free(padded);
    try std.testing.expectEqualStrings(
        "0x0000000000000000000000000000000000000001",
        padded,
    );
    try std.testing.expect(TokenModule.isBinaryOp(.Add));

    var tree = try AST.Tree.init(std.testing.allocator, "uint", "Type.sol");
    defer tree.deinit();
    const embedded = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try TokenModule.ElementaryTypeNameToken.init(.UInt, 0, 0),
    } });
    const expression = try tree.createNode(.{}, .{ .elementary_type_name_expression = .{
        .type_name = embedded,
    } });
    var children: std.ArrayList(*const AST.Node) = .empty;
    defer children.deinit(std.testing.allocator);
    try appendChildren(std.testing.allocator, &children, expression);
    try std.testing.expectEqual(@as(usize, 0), children.items.len);
}

test "declaration visibility follows kind-specific upstream defaults" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "A.sol");
    defer tree.deinit();

    const parameters = try tree.createNode(.{}, .{ .parameter_list = .{} });
    const ordinary = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "f" },
            .parameters = parameters,
        },
    } });
    const external = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "g", .visibility = .External },
            .parameters = parameters,
        },
    } });
    const constructor = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{},
            .parameters = parameters,
        },
        .kind = .Constructor,
    } });
    const variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "value" },
    } });

    try std.testing.expect(isPublic(ordinary));
    try std.testing.expect(isVisibleInContract(ordinary));
    try std.testing.expect(isPublic(external));
    try std.testing.expect(!isVisibleInContract(external));
    try std.testing.expect(!isVisibleInContract(constructor));
    try std.testing.expect(effectiveVisibility(constructor) == null);
    try std.testing.expectEqual(AST.Visibility.Internal, effectiveVisibility(variable).?);
}

test "variable scope classification and data locations match AST.cpp" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Variables.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const bytes_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try TokenModule.ElementaryTypeNameToken.init(.Bytes, 0, 0),
    } });
    const uint_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try TokenModule.ElementaryTypeNameToken.init(.UInt, 0, 0),
    } });
    const external_parameter = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "input" },
        .type_name = bytes_name,
    } });
    const return_parameter = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "output" },
        .type_name = bytes_name,
    } });
    const parameter_list = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{external_parameter}),
    } });
    const return_list = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{return_parameter}),
    } });
    const body = try tree.createNode(.{}, .{ .block = .{} });
    const function = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "f", .visibility = .External },
            .parameters = parameter_list,
            .return_parameters = return_list,
        },
        .body = body,
    } });
    const contract = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "C" },
    } });
    const state_variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "stateValue", .visibility = .Public },
        .type_name = bytes_name,
    } });
    const scalar_parameter = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "number" },
        .type_name = uint_name,
    } });
    const internal_parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{scalar_parameter}),
    } });
    const internal_function = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "g", .visibility = .Internal },
            .parameters = internal_parameters,
            .return_parameters = try tree.createNode(.{}, .{ .parameter_list = .{} }),
        },
        .body = body,
    } });
    const local_variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "localValue" },
        .type_name = bytes_name,
    } });
    const catch_parameter = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "reason" },
        .type_name = bytes_name,
    } });
    const catch_list = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{catch_parameter}),
    } });
    const catch_clause = try tree.createNode(.{}, .{ .try_catch_clause = .{
        .parameters = catch_list,
        .block = body,
    } });

    try testSetVariableType(&tree, external_parameter, provider.bytesStorage());
    try testSetVariableType(&tree, return_parameter, provider.bytesStorage());
    try testSetVariableType(&tree, state_variable, provider.bytesStorage());
    try testSetVariableType(&tree, scalar_parameter, provider.uint256());
    try testSetVariableType(&tree, local_variable, provider.bytesStorage());
    try testSetVariableType(&tree, catch_parameter, provider.bytesStorage());
    try testSetScope(&tree, contract, null);
    try testSetScope(&tree, function, contract);
    try testSetScope(&tree, internal_function, contract);
    try testSetScope(&tree, external_parameter, function);
    try testSetScope(&tree, return_parameter, function);
    try testSetScope(&tree, scalar_parameter, internal_function);
    try testSetScope(&tree, state_variable, contract);
    try testSetScope(&tree, body, function);
    try testSetScope(&tree, local_variable, body);
    try testSetScope(&tree, catch_clause, body);
    try testSetScope(&tree, catch_parameter, catch_clause);

    try std.testing.expect(isCallableOrCatchParameter(external_parameter));
    try std.testing.expect(isExternalCallableParameter(external_parameter));
    try std.testing.expect(!isPublicCallableParameter(external_parameter));
    try std.testing.expect(isReturnParameter(return_parameter));
    try std.testing.expect(!isExternalCallableParameter(return_parameter));
    try std.testing.expect(isInternalCallableParameter(scalar_parameter));
    try std.testing.expect(isStateVariable(state_variable));
    try std.testing.expect(state_variable.isPartOfExternalInterface());
    try std.testing.expect(state_variable.isLValue());
    try std.testing.expect(isLocalOrReturn(local_variable));
    try std.testing.expect(isTryCatchParameter(catch_parameter));

    const external_locations = try allowedDataLocations(external_parameter);
    try std.testing.expect(external_locations.contains(.Memory));
    try std.testing.expect(external_locations.contains(.CallData));
    try std.testing.expect(!external_locations.contains(.Storage));
    const state_locations = try allowedDataLocations(state_variable);
    try std.testing.expect(state_locations.contains(.Unspecified));
    try std.testing.expect(state_locations.contains(.Transient));
    const scalar_locations = try allowedDataLocations(scalar_parameter);
    try std.testing.expectEqual(@as(usize, 1), scalar_locations.count());
    try std.testing.expect(scalar_locations.contains(.Unspecified));
    const local_locations = try allowedDataLocations(local_variable);
    try std.testing.expect(local_locations.contains(.Memory));
    try std.testing.expect(local_locations.contains(.Storage));
    try std.testing.expect(local_locations.contains(.CallData));
    const catch_locations = try allowedDataLocations(catch_parameter);
    try std.testing.expectEqual(@as(usize, 1), catch_locations.count());
    try std.testing.expect(catch_locations.contains(.Memory));
}

test "source-unit import closure is recursive, cycle-safe, and deterministic" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "A.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const import_ab = try tree.createNode(.{}, .{ .import_directive = .{
        .declaration = .{},
        .path = "B.sol",
    } });
    const import_bc = try tree.createNode(.{}, .{ .import_directive = .{
        .declaration = .{},
        .path = "C.sol",
    } });
    const import_ca = try tree.createNode(.{}, .{ .import_directive = .{
        .declaration = .{},
        .path = "A.sol",
    } });
    const a = try tree.createNode(.{}, .{ .source_unit = .{
        .nodes = try tree.ownSlice(*AST.Node, &.{import_ab}),
    } });
    const b = try tree.createNode(.{}, .{ .source_unit = .{
        .nodes = try tree.ownSlice(*AST.Node, &.{import_bc}),
    } });
    const c = try tree.createNode(.{}, .{ .source_unit = .{
        .nodes = try tree.ownSlice(*AST.Node, &.{import_ca}),
    } });

    const links = [_]struct { import: *AST.Node, target: *AST.Node }{
        .{ .import = import_ab, .target = b },
        .{ .import = import_bc, .target = c },
        .{ .import = import_ca, .target = a },
    };
    for (links) |link| {
        const annotation = try ASTAnnotations.ensure(&tree, link.import);
        annotation.import.source_unit = link.target;
    }
    const units = [_]struct { node: *AST.Node, path: []const u8 }{
        .{ .node = a, .path = "A.sol" },
        .{ .node = b, .path = "B.sol" },
        .{ .node = c, .path = "C.sol" },
    };
    for (units) |unit| {
        const annotation = try ASTAnnotations.ensure(&tree, unit.node);
        try annotation.source_unit.path.assign(unit.path);
    }
    try testSetScope(&tree, import_ab, a);
    try testSetScope(&tree, import_bc, b);
    try testSetScope(&tree, import_ca, c);

    const direct = try referencedSourceUnitsAlloc(
        std.testing.allocator,
        a,
        false,
        &.{},
    );
    defer std.testing.allocator.free(direct);
    try std.testing.expectEqualSlices(*const AST.Node, &.{b}, direct);
    const recursive = try referencedSourceUnitsAlloc(
        std.testing.allocator,
        a,
        true,
        &.{a},
    );
    defer std.testing.allocator.free(recursive);
    try std.testing.expectEqualSlices(*const AST.Node, &.{ b, c }, recursive);
    try std.testing.expect(sourceUnit(import_ab) == a);
    try std.testing.expectEqualStrings("A.sol", sourceUnitName(import_ab).?);

    const import_type = (try declarationType(&provider, import_ab)).?;
    try std.testing.expect(import_type.payload.Module.source_unit == b);
}

test "contract hierarchy, virtual dispatch, interfaces, and named calls are complete" {
    const CallGraph = @import("call_graph.zig").CallGraph;

    var tree = try AST.Tree.init(std.testing.allocator, "", "Contracts.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    const uint_type = provider.uint256();

    const base_a = try testCreateTypedVariable(&tree, "a", uint_type, .Default);
    const base_b = try testCreateTypedVariable(&tree, "b", uint_type, .Default);
    const derived_a = try testCreateTypedVariable(&tree, "a", uint_type, .Default);
    const derived_b = try testCreateTypedVariable(&tree, "b", uint_type, .Default);
    const base_function = try testCreateFunction(
        &tree,
        "f",
        .Public,
        .Function,
        true,
        true,
        &.{ base_a, base_b },
    );
    const derived_function = try testCreateFunction(
        &tree,
        "f",
        .Public,
        .Function,
        false,
        true,
        &.{ derived_a, derived_b },
    );
    const base_constructor = try testCreateFunction(
        &tree,
        "",
        .Default,
        .Constructor,
        false,
        true,
        &.{},
    );
    const derived_constructor = try testCreateFunction(
        &tree,
        "",
        .Default,
        .Constructor,
        false,
        true,
        &.{},
    );
    const fallback = try testCreateFunction(
        &tree,
        "",
        .External,
        .Fallback,
        false,
        true,
        &.{},
    );
    const receive = try testCreateFunction(
        &tree,
        "",
        .External,
        .Receive,
        false,
        true,
        &.{},
    );
    const state_variable = try testCreateTypedVariable(
        &tree,
        "stateValue",
        uint_type,
        .Public,
    );

    const event_parameter = try testCreateTypedVariable(&tree, "value", uint_type, .Default);
    const event_parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{event_parameter}),
    } });
    const base_event = try tree.createNode(.{}, .{ .event_definition = .{
        .callable = .{
            .declaration = .{ .name = "Changed" },
            .parameters = event_parameters,
        },
    } });
    const derived_event_parameter = try testCreateTypedVariable(
        &tree,
        "value",
        uint_type,
        .Default,
    );
    const derived_event_parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{derived_event_parameter}),
    } });
    const derived_event = try tree.createNode(.{}, .{ .event_definition = .{
        .callable = .{
            .declaration = .{ .name = "Changed" },
            .parameters = derived_event_parameters,
        },
    } });
    const error_parameter = try testCreateTypedVariable(&tree, "code", uint_type, .Default);
    const error_parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{error_parameter}),
    } });
    const base_error = try tree.createNode(.{}, .{ .error_definition = .{
        .callable = .{
            .declaration = .{ .name = "Failure" },
            .parameters = error_parameters,
        },
    } });

    const empty_parameters = try tree.createNode(.{}, .{ .parameter_list = .{} });
    const base_modifier = try tree.createNode(.{}, .{ .modifier_definition = .{
        .callable = .{
            .declaration = .{ .name = "onlyReady", .visibility = .Internal },
            .parameters = empty_parameters,
            .marked_virtual = true,
        },
        .body = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const derived_modifier = try tree.createNode(.{}, .{ .modifier_definition = .{
        .callable = .{
            .declaration = .{ .name = "onlyReady", .visibility = .Internal },
            .parameters = empty_parameters,
        },
        .body = try tree.createNode(.{}, .{ .block = .{} }),
    } });

    const base = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Base" },
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{
            base_function,
            base_constructor,
            fallback,
            base_event,
            base_error,
            base_modifier,
        }),
    } });
    const derived = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Derived" },
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{
            derived_function,
            derived_constructor,
            receive,
            state_variable,
            derived_event,
            derived_modifier,
        }),
    } });

    const library_parameter = try testCreateTypedVariable(&tree, "value", uint_type, .Default);
    const library_function = try testCreateFunction(
        &tree,
        "double",
        .Public,
        .Function,
        false,
        true,
        &.{library_parameter},
    );
    const library = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "Math" },
        .contract_kind = .Library,
        .sub_nodes = try tree.ownSlice(*AST.Node, &.{library_function}),
    } });
    const source = try tree.createNode(.{}, .{ .source_unit = .{
        .nodes = try tree.ownSlice(*AST.Node, &.{ base, derived, library }),
    } });
    tree.root = source;
    const source_annotation = try ASTAnnotations.ensure(&tree, source);
    try source_annotation.source_unit.path.assign("Contracts.sol");

    try testSetScope(&tree, base, source);
    try testSetScope(&tree, derived, source);
    try testSetScope(&tree, library, source);
    for (base.payload.contract_definition.sub_nodes) |member|
        try testSetScope(&tree, member, base);
    for (derived.payload.contract_definition.sub_nodes) |member|
        try testSetScope(&tree, member, derived);
    try testSetScope(&tree, library_function, library);
    for ([_]*AST.Node{ base_a, base_b }) |parameter|
        try testSetScope(&tree, parameter, base_function);
    for ([_]*AST.Node{ derived_a, derived_b }) |parameter|
        try testSetScope(&tree, parameter, derived_function);
    try testSetScope(&tree, event_parameter, base_event);
    try testSetScope(&tree, derived_event_parameter, derived_event);
    try testSetScope(&tree, error_parameter, base_error);
    try testSetScope(&tree, library_parameter, library_function);

    try testSetContractHierarchy(
        &tree,
        base,
        try tree.ownSlice(*AST.Node, &.{base}),
    );
    try testSetContractHierarchy(
        &tree,
        derived,
        try tree.ownSlice(*AST.Node, &.{ derived, base }),
    );
    try testSetContractHierarchy(
        &tree,
        library,
        try tree.ownSlice(*AST.Node, &.{library}),
    );

    try std.testing.expect(try contractDerivesFrom(derived, base));
    try std.testing.expect(contractCanBeDeployed(derived));
    try std.testing.expect(contractConstructor(derived) == derived_constructor);
    try std.testing.expect((try contractFallbackFunction(derived)) == fallback);
    try std.testing.expect((try contractReceiveFunction(derived)) == receive);
    try std.testing.expect((try superContract(derived, derived)) == base);
    try std.testing.expect((try nextConstructor(derived, derived)) == base_constructor);
    const filtered_functions = try filteredNodesAlloc(
        std.testing.allocator,
        derived.payload.contract_definition.sub_nodes,
        .function_definition,
    );
    defer std.testing.allocator.free(filtered_functions);
    try std.testing.expectEqual(@as(usize, 3), filtered_functions.len);
    const qualified_name = try fullyQualifiedContractNameAlloc(
        std.testing.allocator,
        derived,
    );
    defer std.testing.allocator.free(qualified_name);
    try std.testing.expectEqualStrings("Contracts.sol:Derived", qualified_name);
    const named_functions = try definedFunctionsByNameAlloc(
        std.testing.allocator,
        derived,
        "f",
    );
    defer std.testing.allocator.free(named_functions);
    try std.testing.expectEqualSlices(*const AST.Node, &.{derived_function}, named_functions);

    try std.testing.expect(
        try resolveFunctionVirtual(&provider, base_function, derived, null) == derived_function,
    );
    try std.testing.expect(
        try resolveModifierVirtual(base_modifier, derived, null) == derived_modifier,
    );
    try std.testing.expect(
        try resolveCallableVirtual(&provider, base_function, derived, null) == derived_function,
    );
    try std.testing.expect(
        try resolveCallableVirtual(&provider, base_event, derived, null) == base_event,
    );
    try addLocalVariable(&tree, derived_function, derived_a);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{derived_a},
        localVariables(derived_function).?,
    );
    try std.testing.expect(
        try typeNameType(derived_a.payload.variable_declaration.type_name.?) == uint_type,
    );
    const call_expression = try tree.createNode(.{}, .{ .identifier = .{ .name = "f" } });
    try testSetReferencedDeclaration(&tree, call_expression, base_function, .Virtual);
    const first_argument = try tree.createNode(.{}, .{ .literal = .{
        .token = .Number,
        .value = "2",
    } });
    const second_argument = try tree.createNode(.{}, .{ .literal = .{
        .token = .Number,
        .value = "1",
    } });
    const call = try tree.createNode(.{}, .{ .function_call = .{
        .expression = call_expression,
        .arguments = try tree.ownSlice(*AST.Node, &.{ first_argument, second_argument }),
        .names = try tree.ownSlice([]const u8, &.{ "b", "a" }),
    } });
    const expression_annotation = try ASTAnnotations.ensure(&tree, call_expression);
    expression_annotation.identifier.expression.type_ref = try provider.functionFromDefinition(
        derived_function,
        .Internal,
    );
    const call_annotation = try ASTAnnotations.ensure(&tree, call);
    try call_annotation.function_call.kind.assign(.FunctionCall);
    try std.testing.expect(
        (try resolveFunctionCall(&provider, call, derived)) == derived_function,
    );
    const sorted = try sortedFunctionCallArgumentsAlloc(
        &provider,
        std.testing.allocator,
        call,
    );
    defer std.testing.allocator.free(sorted);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{ second_argument, first_argument },
        sorted,
    );

    const super_expression = try tree.createNode(.{}, .{ .identifier = .{ .name = "super" } });
    const super_annotation = try ASTAnnotations.ensure(&tree, super_expression);
    super_annotation.identifier.expression.type_ref = try provider.typeType(
        try provider.contract(derived, true),
    );
    const super_member = try tree.createNode(.{}, .{ .member_access = .{
        .expression = super_expression,
        .member_name = "f",
        .member_location = .{},
    } });
    try testSetReferencedDeclaration(&tree, super_member, base_function, .Super);
    const super_call = try tree.createNode(.{}, .{ .function_call = .{
        .expression = super_member,
    } });
    try std.testing.expect(
        (try resolveFunctionCall(&provider, super_call, derived)) == base_function,
    );

    const signature = try functionExternalSignatureAlloc(
        &provider,
        std.testing.allocator,
        derived_function,
    );
    defer std.testing.allocator.free(signature);
    try std.testing.expectEqualStrings("f(uint256,uint256)", signature);
    const identifier_hex = try declarationExternalIdentifierHexAlloc(
        &provider,
        std.testing.allocator,
        derived_function,
    );
    defer std.testing.allocator.free(identifier_hex);
    try std.testing.expectEqual(@as(usize, 8), identifier_hex.len);
    try std.testing.expect((try declarationFunctionType(
        &provider,
        derived_function,
        true,
    )) != null);
    try std.testing.expect((try functionTypeViaContractName(
        &provider,
        derived_function,
        .Foreign,
    )).payload.Function.kind == .Declaration);
    try std.testing.expect((try functionTypeViaContractName(
        &provider,
        library_function,
        .Library,
    )).payload.Function.kind == .DelegateCall);
    try std.testing.expect((try declarationTypeViaContractName(
        &provider,
        state_variable,
        .Local,
    )) != null);

    const operation = try tree.createNode(.{}, .{ .unary_operation = .{
        .operator = .Sub,
        .sub_expression = first_argument,
        .is_prefix = true,
    } });
    const operation_annotation = try ASTAnnotations.ensure(&tree, operation);
    try operation_annotation.operation.user_defined_function.assign(library_function);
    try std.testing.expect((try operationUserDefinedFunctionType(
        &provider,
        operation,
    )).?.payload.Function.kind == .DelegateCall);

    const interface_list = try contractInterfaceFunctionListAlloc(
        &provider,
        std.testing.allocator,
        derived,
        true,
    );
    defer std.testing.allocator.free(interface_list);
    try std.testing.expectEqual(@as(usize, 2), interface_list.len);
    const interface_map = try contractInterfaceFunctionsAlloc(
        &provider,
        std.testing.allocator,
        derived,
        true,
    );
    defer std.testing.allocator.free(interface_map);
    try std.testing.expectEqual(@as(usize, 2), interface_map.len);
    try std.testing.expect(!interface_map[1].selector.lessThan(&interface_map[0].selector));
    try std.testing.expect((try contractInterfaceId(
        &provider,
        std.testing.allocator,
        derived,
    )) != 0);
    const defined_events = try contractDefinedInterfaceEventsAlloc(
        &provider,
        std.testing.allocator,
        derived,
    );
    defer std.testing.allocator.free(defined_events);
    try std.testing.expectEqualSlices(*const AST.Node, &.{derived_event}, defined_events);

    const used_event = base_event;
    const used_error = base_error;
    const derived_annotation = @constCast(contractAnnotation(derived).?);
    try derived_annotation.interface_events.append(tree.allocator(), used_event);
    try derived_annotation.interface_errors.append(tree.allocator(), used_error);
    var creation_graph = CallGraph.init(
        std.testing.allocator,
        @import("compatibility_id_resolver.zig").CompatibilityIdResolver.legacyNodeIds(),
    );
    defer creation_graph.deinit();
    var deployed_graph = CallGraph.init(
        std.testing.allocator,
        @import("compatibility_id_resolver.zig").CompatibilityIdResolver.legacyNodeIds(),
    );
    defer deployed_graph.deinit();
    try derived_annotation.creation_call_graph.assign(&creation_graph);
    try derived_annotation.deployed_call_graph.assign(&deployed_graph);
    const used_events = try contractUsedInterfaceEventsAlloc(
        std.testing.allocator,
        derived,
    );
    defer std.testing.allocator.free(used_events);
    try std.testing.expectEqualSlices(*const AST.Node, &.{used_event}, used_events);
    const all_events = try contractInterfaceEventsAlloc(
        std.testing.allocator,
        derived,
        true,
    );
    defer std.testing.allocator.free(all_events);
    try std.testing.expectEqual(@as(usize, 2), all_events.len);
    const all_errors = try contractInterfaceErrorsAlloc(
        std.testing.allocator,
        derived,
        true,
    );
    defer std.testing.allocator.free(all_errors);
    try std.testing.expectEqualSlices(*const AST.Node, &.{base_error}, all_errors);

    try std.testing.expect((try declarationType(&provider, derived)) != null);
    try std.testing.expect((try declarationType(&provider, base_modifier)) != null);
    try std.testing.expect((try declarationType(&provider, base_event)) != null);
    try std.testing.expect((try declarationType(&provider, base_error)) != null);
}

test "type declarations, struct calls, magic declarations, and try clauses project exactly" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Types.sol");
    defer tree.deinit();
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    const uint_type = provider.uint256();

    const first_member = try testCreateTypedVariable(&tree, "first", uint_type, .Default);
    const second_member = try testCreateTypedVariable(&tree, "second", uint_type, .Default);
    const structure = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "Pair" },
        .members = try tree.ownSlice(*AST.Node, &.{ first_member, second_member }),
    } });
    const structure_annotation = try ASTAnnotations.ensure(&tree, structure);
    structure_annotation.struct_declaration.recursive = false;
    try testSetScope(&tree, first_member, structure);
    try testSetScope(&tree, second_member, structure);
    try std.testing.expect(isStructMember(first_member));
    const structure_type_type = (try declarationType(&provider, structure)).?;
    try std.testing.expect(structure_type_type.category() == .TypeType);

    const constructor_expression = try tree.createNode(.{}, .{ .identifier = .{
        .name = "Pair",
    } });
    const constructor_expression_annotation = try ASTAnnotations.ensure(
        &tree,
        constructor_expression,
    );
    constructor_expression_annotation.identifier.expression.type_ref = structure_type_type;
    const first_argument = try tree.createNode(.{}, .{ .literal = .{
        .token = .Number,
        .value = "2",
    } });
    const second_argument = try tree.createNode(.{}, .{ .literal = .{
        .token = .Number,
        .value = "1",
    } });
    const constructor_call = try tree.createNode(.{}, .{ .function_call = .{
        .expression = constructor_expression,
        .arguments = try tree.ownSlice(*AST.Node, &.{ first_argument, second_argument }),
        .names = try tree.ownSlice([]const u8, &.{ "second", "first" }),
    } });
    const constructor_call_annotation = try ASTAnnotations.ensure(&tree, constructor_call);
    try constructor_call_annotation.function_call.kind.assign(.StructConstructorCall);
    const sorted = try sortedFunctionCallArgumentsAlloc(
        &provider,
        std.testing.allocator,
        constructor_call,
    );
    defer std.testing.allocator.free(sorted);
    try std.testing.expectEqualSlices(
        *const AST.Node,
        &.{ second_argument, first_argument },
        sorted,
    );

    const enum_value = try tree.createNode(.{}, .{ .enum_value = .{
        .declaration = .{ .name = "Ready" },
    } });
    const enumeration = try tree.createNode(.{}, .{ .enum_definition = .{
        .declaration = .{ .name = "Status" },
        .members = try tree.ownSlice(*AST.Node, &.{enum_value}),
    } });
    try testSetScope(&tree, enum_value, enumeration);
    try std.testing.expect(isEnumValue(enum_value));
    try std.testing.expect((try declarationType(&provider, enumeration)) != null);
    try std.testing.expect((try declarationType(&provider, enum_value)).?.category() == .Enum);

    const underlying_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try TokenModule.ElementaryTypeNameToken.init(.UInt, 0, 0),
    } });
    const underlying_annotation = try ASTAnnotations.ensure(&tree, underlying_name);
    underlying_annotation.type_name.type_ref = uint_type;
    const value_type = try tree.createNode(.{}, .{ .user_defined_value_type_definition = .{
        .declaration = .{ .name = "Amount" },
        .underlying_type = underlying_name,
    } });
    const value_type_meta = (try declarationType(&provider, value_type)).?;
    try std.testing.expect(value_type_meta.payload.TypeType.actual_type.category() == .UserDefinedValueType);

    const magic_function_type = try provider.function(
        &.{},
        &.{},
        &.{},
        &.{},
        .Internal,
        .Pure,
        null,
        .{},
    );
    const magic = try tree.createNode(.{}, .{ .magic_variable_declaration = .{
        .declaration = .{ .name = "magic" },
        .type_ref = @ptrCast(magic_function_type),
    } });
    try std.testing.expect((try declarationType(&provider, magic)).? == magic_function_type);
    try std.testing.expect((try declarationFunctionType(&provider, magic, true)).? == magic_function_type);

    const type_definition = try tree.createNode(.{}, .{ .type_definition = .{
        .declaration = .{ .name = "Experimental" },
    } });
    try std.testing.expect((try declarationType(&provider, type_definition)) == null);

    const external_call = try tree.createNode(.{}, .{ .identifier = .{ .name = "work" } });
    const success = try tree.createNode(.{}, .{ .try_catch_clause = .{
        .block = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const panic = try tree.createNode(.{}, .{ .try_catch_clause = .{
        .error_name = "Panic",
        .block = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const standard_error = try tree.createNode(.{}, .{ .try_catch_clause = .{
        .error_name = "Error",
        .block = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const fallback_clause = try tree.createNode(.{}, .{ .try_catch_clause = .{
        .block = try tree.createNode(.{}, .{ .block = .{} }),
    } });
    const try_statement: AST.TryStatement = .{
        .external_call = external_call,
        .clauses = try tree.ownSlice(*AST.Node, &.{
            success,
            panic,
            standard_error,
            fallback_clause,
        }),
    };
    try std.testing.expect((try trySuccessClause(try_statement)) == success);
    try std.testing.expect(tryPanicClause(try_statement) == panic);
    try std.testing.expect(tryErrorClause(try_statement) == standard_error);
    try std.testing.expect(tryFallbackClause(try_statement) == fallback_clause);
}

const Enums = @import("ast_enums.zig");

const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;

const YulAST = @import("../../libyul/ast.zig");

pub const Token = TokenModule.Token;

pub const ElementaryTypeNameToken = TokenModule.ElementaryTypeNameToken;

pub const VirtualLookup = Enums.VirtualLookup;

pub const StateMutability = Enums.StateMutability;

pub const Visibility = Enums.Visibility;

pub const Arithmetic = Enums.Arithmetic;

pub const ContractKind = Enums.ContractKind;

pub const NodeList = []const *Node;

pub const OptionalNodeList = []const ?*Node;

pub const StringList = []const []const u8;

pub const DeclarationData = struct {
    name: []const u8 = "",
    name_location: SourceLocation = .{},
    visibility: Visibility = .Default,

    pub fn effectiveVisibility(self: DeclarationData, default_value: Visibility) Visibility {
        return if (self.visibility == .Default) default_value else self.visibility;
    }
};

pub const CallableData = struct {
    declaration: DeclarationData,
    parameters: *Node,
    overrides: ?*Node = null,
    return_parameters: ?*Node = null,
    marked_virtual: bool = false,
};

pub const StatementData = struct {
    /// Raw NatSpec text, matching the upstream `Documented` mixin.
    documentation: ?[]const u8 = null,
};

pub const SymbolAlias = struct {
    symbol: *Node,
    alias: ?[]const u8 = null,
    location: SourceLocation = .{},
};

pub const FunctionAndOperator = struct {
    function_or_library: *Node,
    operator: ?Token = null,
};

pub const SourceUnit = struct {
    license: ?[]const u8 = null,
    nodes: NodeList = &.{},
    experimental_solidity: bool = false,
};

pub const PragmaDirective = struct {
    tokens: []const Token = &.{},
    literals: StringList = &.{},
};

pub const ImportDirective = struct {
    declaration: DeclarationData,
    path: []const u8,
    symbol_aliases: []const SymbolAlias = &.{},
};

pub const StructuredDocumentation = struct {
    text: []const u8,
};

pub const ContractDefinition = struct {
    declaration: DeclarationData,
    documentation: ?*Node = null,
    base_contracts: NodeList = &.{},
    sub_nodes: NodeList = &.{},
    contract_kind: ContractKind = .Contract,
    abstract: bool = false,
    storage_layout_specifier: ?*Node = null,
};

pub const StorageLayoutSpecifier = struct {
    base_slot_expression: *Node,
};

pub const IdentifierPath = struct {
    path: StringList,
    path_locations: []const SourceLocation,
};

pub const InheritanceSpecifier = struct {
    base_name: *Node,
    /// `null` means no parentheses; a present empty slice means `Base()`.
    arguments: ?NodeList = null,
};

pub const UsingForDirective = struct {
    functions_and_operators: []const FunctionAndOperator,
    uses_braces: bool,
    type_name: ?*Node,
    global: bool = false,
};

pub const StructDefinition = struct {
    declaration: DeclarationData,
    documentation: ?*Node = null,
    members: NodeList = &.{},
};

pub const EnumDefinition = struct {
    declaration: DeclarationData,
    documentation: ?*Node = null,
    members: NodeList = &.{},
};

pub const EnumValue = struct {
    declaration: DeclarationData,
    documentation: ?*Node = null,
};

pub const UserDefinedValueTypeDefinition = struct {
    declaration: DeclarationData,
    underlying_type: *Node,
};

pub const ParameterList = struct {
    parameters: NodeList = &.{},
};

pub const OverrideSpecifier = struct {
    overrides: NodeList = &.{},
};

pub const FunctionDefinition = struct {
    callable: CallableData,
    documentation: ?*Node = null,
    state_mutability: StateMutability = .NonPayable,
    free: bool = false,
    kind: Token = .Function,
    modifiers: NodeList = &.{},
    body: ?*Node = null,
    experimental_return_expression: ?*Node = null,

    pub fn implemented(self: FunctionDefinition) bool {
        return self.body != null;
    }

    pub fn ordinary(self: FunctionDefinition) bool {
        return self.kind == .Function;
    }
};

pub const VariableLocation = enum(c_int) {
    Unspecified,
    Storage,
    Transient,
    Memory,
    CallData,
};

pub const VariableMutability = enum(c_int) {
    Mutable,
    Immutable,
    Constant,
};

pub const ContractNameAccessKind = enum(c_int) {
    Local,
    Foreign,
    Library,
};

pub const VariableDeclaration = struct {
    declaration: DeclarationData,
    documentation: ?*Node = null,
    type_name: ?*Node = null,
    value: ?*Node = null,
    indexed: bool = false,
    mutability: VariableMutability = .Mutable,
    overrides: ?*Node = null,
    reference_location: VariableLocation = .Unspecified,
    experimental_type_expression: ?*Node = null,
};

pub const ModifierDefinition = struct {
    callable: CallableData,
    documentation: ?*Node = null,
    body: ?*Node = null,

    pub fn implemented(self: ModifierDefinition) bool {
        return self.body != null;
    }
};

pub const ModifierInvocation = struct {
    modifier_name: *Node,
    /// `null` means no parentheses; a present empty slice means `modifier()`.
    arguments: ?NodeList = null,
};

pub const EventDefinition = struct {
    callable: CallableData,
    documentation: ?*Node = null,
    anonymous: bool = false,
};

pub const ErrorDefinition = struct {
    callable: CallableData,
    documentation: ?*Node = null,
};

pub const MagicVariableDeclaration = struct {
    declaration: DeclarationData,
    type_ref: ?*const anyopaque = null,
};

pub const ElementaryTypeName = struct {
    type_name: ElementaryTypeNameToken,
    state_mutability: ?StateMutability = null,
};

pub const UserDefinedTypeName = struct {
    path_node: *Node,
};

pub const FunctionTypeName = struct {
    parameter_types: *Node,
    return_types: *Node,
    visibility: Visibility = .Default,
    state_mutability: StateMutability = .NonPayable,

    pub fn effectiveVisibility(self: FunctionTypeName) Visibility {
        return if (self.visibility == .Default) .Internal else self.visibility;
    }
};

pub const Mapping = struct {
    key_type: *Node,
    key_name: []const u8 = "",
    key_name_location: SourceLocation = .{},
    value_type: *Node,
    value_name: []const u8 = "",
    value_name_location: SourceLocation = .{},
};

pub const ArrayTypeName = struct {
    base_type: *Node,
    length: ?*Node = null,
};

pub const InlineAssembly = struct {
    statement: StatementData = .{},
    dialect: ?YulAST.Dialect = null,
    flags: ?[]const ?[]const u8 = null,
    operations: ?*YulAST.AST = null,
};

pub const Block = struct {
    statement: StatementData = .{},
    statements: NodeList = &.{},
    unchecked: bool = false,
};

pub const PlaceholderStatement = struct {
    statement: StatementData = .{},
};

pub const IfStatement = struct {
    statement: StatementData = .{},
    condition: *Node,
    true_body: *Node,
    false_body: ?*Node = null,
};

pub const TryCatchClause = struct {
    error_name: []const u8 = "",
    parameters: ?*Node = null,
    block: *Node,
};

pub const TryStatement = struct {
    statement: StatementData = .{},
    external_call: *Node,
    clauses: NodeList,
};

pub const WhileStatement = struct {
    statement: StatementData = .{},
    condition: *Node,
    body: *Node,
    is_do_while: bool = false,
};

pub const ForStatement = struct {
    statement: StatementData = .{},
    initialization_expression: ?*Node = null,
    condition: ?*Node = null,
    loop_expression: ?*Node = null,
    body: *Node,
};

pub const Continue = struct { statement: StatementData = .{} };

pub const Break = struct { statement: StatementData = .{} };

pub const Return = struct {
    statement: StatementData = .{},
    expression: ?*Node = null,
};

pub const Throw = struct { statement: StatementData = .{} };

pub const RevertStatement = struct {
    statement: StatementData = .{},
    error_call: *Node,
};

pub const EmitStatement = struct {
    statement: StatementData = .{},
    event_call: *Node,
};

pub const VariableDeclarationStatement = struct {
    statement: StatementData = .{},
    declarations: OptionalNodeList,
    initial_value: ?*Node = null,
};

pub const ExpressionStatement = struct {
    statement: StatementData = .{},
    expression: *Node,
};

pub const Conditional = struct {
    condition: *Node,
    true_expression: *Node,
    false_expression: *Node,
};

pub const Assignment = struct {
    left_hand_side: *Node,
    operator: Token,
    right_hand_side: *Node,
};

pub const TupleExpression = struct {
    components: OptionalNodeList,
    is_inline_array: bool = false,
};

pub const UnaryOperation = struct {
    operator: Token,
    sub_expression: *Node,
    is_prefix: bool,
};

pub const BinaryOperation = struct {
    left: *Node,
    operator: Token,
    right: *Node,
};

pub const FunctionCall = struct {
    expression: *Node,
    arguments: NodeList = &.{},
    names: StringList = &.{},
    name_locations: []const SourceLocation = &.{},
};

pub const FunctionCallOptions = struct {
    expression: *Node,
    options: NodeList = &.{},
    names: StringList = &.{},
};

pub const NewExpression = struct { type_name: *Node };

pub const MemberAccess = struct {
    expression: *Node,
    member_name: []const u8,
    member_location: SourceLocation,
};

pub const IndexAccess = struct {
    base: *Node,
    index: ?*Node = null,
};

pub const IndexRangeAccess = struct {
    base: *Node,
    start: ?*Node = null,
    end: ?*Node = null,
};

pub const Identifier = struct { name: []const u8 };

pub const ElementaryTypeNameExpression = struct { type_name: *Node };

pub const LiteralSubDenomination = enum(c_uint) {
    None = @intFromEnum(Token.Illegal),
    Wei = @intFromEnum(Token.SubWei),
    Gwei = @intFromEnum(Token.SubGwei),
    Ether = @intFromEnum(Token.SubEther),
    Second = @intFromEnum(Token.SubSecond),
    Minute = @intFromEnum(Token.SubMinute),
    Hour = @intFromEnum(Token.SubHour),
    Day = @intFromEnum(Token.SubDay),
    Week = @intFromEnum(Token.SubWeek),
    Year = @intFromEnum(Token.SubYear),
};

pub const Literal = struct {
    token: Token,
    value: []const u8,
    sub_denomination: LiteralSubDenomination = .None,
};

pub const TypeClassDefinition = struct {
    declaration: DeclarationData,
    documentation: ?*Node = null,
    type_variable: *Node,
    sub_nodes: NodeList = &.{},
};

pub const TypeClassInstantiation = struct {
    type_constructor: *Node,
    argument_sorts: ?*Node = null,
    type_class: *Node,
    sub_nodes: NodeList = &.{},
};

pub const TypeDefinition = struct {
    declaration: DeclarationData,
    arguments: ?*Node = null,
    type_expression: ?*Node = null,
};

pub const TypeClassNameValue = union(enum) {
    builtin: Token,
    identifier_path: *Node,
};

pub const TypeClassName = struct { name: TypeClassNameValue };

pub const Builtin = struct {
    name_parameter: []const u8,
    name_parameter_location: SourceLocation,
};

pub const ForAllQuantifier = struct {
    type_variable_declarations: *Node,
    quantified_declaration: *Node,
};

pub const Kind = enum {
    source_unit,
    pragma_directive,
    import_directive,
    structured_documentation,
    contract_definition,
    storage_layout_specifier,
    identifier_path,
    inheritance_specifier,
    using_for_directive,
    struct_definition,
    enum_definition,
    enum_value,
    user_defined_value_type_definition,
    parameter_list,
    override_specifier,
    function_definition,
    variable_declaration,
    modifier_definition,
    modifier_invocation,
    event_definition,
    error_definition,
    magic_variable_declaration,
    elementary_type_name,
    user_defined_type_name,
    function_type_name,
    mapping,
    array_type_name,
    inline_assembly,
    block,
    placeholder_statement,
    if_statement,
    try_catch_clause,
    try_statement,
    while_statement,
    for_statement,
    continue_statement,
    break_statement,
    return_statement,
    throw_statement,
    revert_statement,
    emit_statement,
    variable_declaration_statement,
    expression_statement,
    conditional,
    assignment,
    tuple_expression,
    unary_operation,
    binary_operation,
    function_call,
    function_call_options,
    new_expression,
    member_access,
    index_access,
    index_range_access,
    identifier,
    elementary_type_name_expression,
    literal,
    type_class_definition,
    type_class_instantiation,
    type_definition,
    type_class_name,
    builtin,
    for_all_quantifier,
};

pub const Payload = union(Kind) {
    source_unit: SourceUnit,
    pragma_directive: PragmaDirective,
    import_directive: ImportDirective,
    structured_documentation: StructuredDocumentation,
    contract_definition: ContractDefinition,
    storage_layout_specifier: StorageLayoutSpecifier,
    identifier_path: IdentifierPath,
    inheritance_specifier: InheritanceSpecifier,
    using_for_directive: UsingForDirective,
    struct_definition: StructDefinition,
    enum_definition: EnumDefinition,
    enum_value: EnumValue,
    user_defined_value_type_definition: UserDefinedValueTypeDefinition,
    parameter_list: ParameterList,
    override_specifier: OverrideSpecifier,
    function_definition: FunctionDefinition,
    variable_declaration: VariableDeclaration,
    modifier_definition: ModifierDefinition,
    modifier_invocation: ModifierInvocation,
    event_definition: EventDefinition,
    error_definition: ErrorDefinition,
    magic_variable_declaration: MagicVariableDeclaration,
    elementary_type_name: ElementaryTypeName,
    user_defined_type_name: UserDefinedTypeName,
    function_type_name: FunctionTypeName,
    mapping: Mapping,
    array_type_name: ArrayTypeName,
    inline_assembly: InlineAssembly,
    block: Block,
    placeholder_statement: PlaceholderStatement,
    if_statement: IfStatement,
    try_catch_clause: TryCatchClause,
    try_statement: TryStatement,
    while_statement: WhileStatement,
    for_statement: ForStatement,
    continue_statement: Continue,
    break_statement: Break,
    return_statement: Return,
    throw_statement: Throw,
    revert_statement: RevertStatement,
    emit_statement: EmitStatement,
    variable_declaration_statement: VariableDeclarationStatement,
    expression_statement: ExpressionStatement,
    conditional: Conditional,
    assignment: Assignment,
    tuple_expression: TupleExpression,
    unary_operation: UnaryOperation,
    binary_operation: BinaryOperation,
    function_call: FunctionCall,
    function_call_options: FunctionCallOptions,
    new_expression: NewExpression,
    member_access: MemberAccess,
    index_access: IndexAccess,
    index_range_access: IndexRangeAccess,
    identifier: Identifier,
    elementary_type_name_expression: ElementaryTypeNameExpression,
    literal: Literal,
    type_class_definition: TypeClassDefinition,
    type_class_instantiation: TypeClassInstantiation,
    type_definition: TypeDefinition,
    type_class_name: TypeClassName,
    builtin: Builtin,
    for_all_quantifier: ForAllQuantifier,
};

pub const Node = struct {
    id: i64,
    /// Stable syntax identity. `id` remains the compatibility projection used
    /// by existing output and code-generation consumers until they migrate.
    node_ref: NodeRef = .{
        .source = SourceId.init(0),
        .local_node = LocalNodeId.init(0),
    },
    location: SourceLocation,
    payload: Payload,
    semantic_context: ?*SemanticContext = null,
    /// Explicit adapter for detached nodes in focused tests. Parsed syntax
    /// stores semantic data in the revision-owned annotation table instead.
    annotation: ?*anyopaque = null,

    pub fn nodeKind(self: *const Node) Kind {
        return std.meta.activeTag(self.payload);
    }

    pub fn isExpression(self: *const Node) bool {
        return switch (self.payload) {
            .conditional,
            .assignment,
            .tuple_expression,
            .unary_operation,
            .binary_operation,
            .function_call,
            .function_call_options,
            .new_expression,
            .member_access,
            .index_access,
            .index_range_access,
            .identifier,
            .elementary_type_name_expression,
            .literal,
            .builtin,
            => true,
            else => false,
        };
    }

    pub fn isStatement(self: *const Node) bool {
        return switch (self.payload) {
            .inline_assembly,
            .block,
            .placeholder_statement,
            .if_statement,
            .try_statement,
            .while_statement,
            .for_statement,
            .continue_statement,
            .break_statement,
            .return_statement,
            .throw_statement,
            .revert_statement,
            .emit_statement,
            .variable_declaration_statement,
            .expression_statement,
            => true,
            else => false,
        };
    }

    pub fn isTypeName(self: *const Node) bool {
        return switch (self.payload) {
            .elementary_type_name,
            .user_defined_type_name,
            .function_type_name,
            .mapping,
            .array_type_name,
            => true,
            else => false,
        };
    }

    pub fn experimentalSolidityOnly(self: *const Node) bool {
        return switch (self.payload) {
            .type_class_definition,
            .type_class_instantiation,
            .type_definition,
            .type_class_name,
            .builtin,
            .for_all_quantifier,
            => true,
            else => false,
        };
    }

    pub fn declaration(self: *Node) ?*DeclarationData {
        return switch (self.payload) {
            .import_directive => |*value| &value.declaration,
            .contract_definition => |*value| &value.declaration,
            .struct_definition => |*value| &value.declaration,
            .enum_definition => |*value| &value.declaration,
            .enum_value => |*value| &value.declaration,
            .user_defined_value_type_definition => |*value| &value.declaration,
            .function_definition => |*value| &value.callable.declaration,
            .variable_declaration => |*value| &value.declaration,
            .modifier_definition => |*value| &value.callable.declaration,
            .event_definition => |*value| &value.callable.declaration,
            .error_definition => |*value| &value.callable.declaration,
            .magic_variable_declaration => |*value| &value.declaration,
            .type_class_definition => |*value| &value.declaration,
            .type_definition => |*value| &value.declaration,
            else => null,
        };
    }

    pub fn declarationConst(self: *const Node) ?*const DeclarationData {
        return @constCast(self).declaration();
    }

    /// Mirrors `Declaration::visibility()`. A default-visibility constructor
    /// has no valid upstream result because `FunctionDefinition::defaultVisibility`
    /// asserts for constructors, so it remains explicitly unavailable here.
    pub fn effectiveVisibility(self: *const Node) ?Visibility {
        const data = self.declarationConst() orelse return null;
        if (data.visibility != .Default) return data.visibility;
        return switch (self.payload) {
            .function_definition => |value| if (value.kind == .Constructor)
                null
            else if (value.free)
                .Internal
            else
                .Public,
            .variable_declaration, .modifier_definition => .Internal,
            else => .Public,
        };
    }

    pub fn isPublic(self: *const Node) bool {
        const visibility = self.effectiveVisibility() orelse return false;
        return @intFromEnum(visibility) >= @intFromEnum(Visibility.Public);
    }

    pub fn isVisibleInContract(self: *const Node) bool {
        if (self.nodeKind() == .function_definition and
            !self.payload.function_definition.ordinary()) return false;
        const visibility = self.effectiveVisibility() orelse return false;
        return visibility != .External;
    }

    pub fn isVisibleInDerivedContracts(self: *const Node) bool {
        switch (self.payload) {
            .struct_definition,
            .enum_definition,
            .event_definition,
            .error_definition,
            => return true,
            else => {},
        }
        const visibility = self.effectiveVisibility() orelse return false;
        return self.isVisibleInContract() and
            @intFromEnum(visibility) >= @intFromEnum(Visibility.Internal);
    }

    pub fn isVisibleAsLibraryMember(self: *const Node) bool {
        const visibility = self.effectiveVisibility() orelse return false;
        return @intFromEnum(visibility) >= @intFromEnum(Visibility.Internal);
    }

    pub fn isVisibleViaContractTypeAccess(self: *const Node) bool {
        return switch (self.payload) {
            .struct_definition,
            .enum_definition,
            .user_defined_value_type_definition,
            .event_definition,
            .error_definition,
            => true,
            .function_definition => |value| !value.free and self.isPartOfExternalInterface(),
            else => false,
        };
    }

    pub fn isVisibleViaContractName(
        self: *const Node,
        access_kind: ContractNameAccessKind,
    ) bool {
        return switch (access_kind) {
            .Local => if (self.effectiveVisibility()) |visibility|
                @intFromEnum(visibility) > @intFromEnum(Visibility.Private)
            else
                false,
            .Foreign => self.isVisibleViaContractTypeAccess(),
            .Library => self.isVisibleAsLibraryMember(),
        };
    }

    pub fn isPartOfExternalInterface(self: *const Node) bool {
        return switch (self.payload) {
            .function_definition => |value| value.ordinary() and self.isPublic(),
            .variable_declaration => self.isPublic(),
            else => false,
        };
    }

    pub fn isLValue(self: *const Node) bool {
        return switch (self.payload) {
            .variable_declaration => |value| value.mutability != .Constant,
            else => false,
        };
    }
};

/// Owns one compilation unit's source bytes, name, nodes, strings, and slice
/// buffers. The arena state itself is separately allocated so moving `Tree`
/// never invalidates allocator context pointers.
pub const Tree = struct {
    backing_allocator: std.mem.Allocator,
    arena_state: *std.heap.ArenaAllocator,
    semantic_context: *SemanticContext,
    source_id: SourceId,
    source: []const u8,
    source_name: []const u8,
    root: ?*Node = null,
    next_node_id: i64 = 0,
    next_local_node_id: u32 = 0,
    nodes: std.ArrayList(*Node) = .empty,
    owned_yul_asts: std.ArrayList(*YulAST.AST) = .empty,

    pub fn init(
        backing_allocator: std.mem.Allocator,
        source: []const u8,
        source_name: []const u8,
    ) std.mem.Allocator.Error!Tree {
        return initWithSourceId(
            backing_allocator,
            SourceId.init(0),
            source,
            source_name,
        );
    }

    pub fn initWithSourceId(
        backing_allocator: std.mem.Allocator,
        source_id: SourceId,
        source: []const u8,
        source_name: []const u8,
    ) std.mem.Allocator.Error!Tree {
        const arena_state = try backing_allocator.create(std.heap.ArenaAllocator);
        errdefer backing_allocator.destroy(arena_state);
        arena_state.* = std.heap.ArenaAllocator.init(backing_allocator);
        errdefer arena_state.deinit();
        const semantic_context = try backing_allocator.create(SemanticContext);
        errdefer backing_allocator.destroy(semantic_context);
        semantic_context.* = .{};
        const arena = arena_state.allocator();
        const owned_source = try arena.dupe(u8, source);
        const owned_source_name = try arena.dupe(u8, source_name);
        return .{
            .backing_allocator = backing_allocator,
            .arena_state = arena_state,
            .semantic_context = semantic_context,
            .source_id = source_id,
            .source = owned_source,
            .source_name = owned_source_name,
        };
    }

    pub fn deinit(self: *Tree) void {
        const backing_allocator = self.backing_allocator;
        const arena_state = self.arena_state;
        const semantic_context = self.semantic_context;
        ASTAnnotations.deinitTreeBinding(self);
        for (self.owned_yul_asts.items) |ast| {
            ast.deinit();
            backing_allocator.destroy(ast);
        }
        self.owned_yul_asts.deinit(backing_allocator);
        arena_state.deinit();
        backing_allocator.destroy(arena_state);
        backing_allocator.destroy(semantic_context);
        self.* = undefined;
    }

    pub fn allocator(self: *Tree) std.mem.Allocator {
        if (ASTAnnotations.semanticAllocator(self)) |semantic_allocator|
            return semantic_allocator;
        return self.syntaxAllocator();
    }

    pub fn syntaxAllocator(self: *Tree) std.mem.Allocator {
        return self.arena_state.allocator();
    }

    pub fn ownString(self: *Tree, value: []const u8) std.mem.Allocator.Error![]const u8 {
        return self.allocator().dupe(u8, value);
    }

    pub fn ownSlice(
        self: *Tree,
        comptime T: type,
        values: []const T,
    ) std.mem.Allocator.Error![]const T {
        return self.allocator().dupe(T, values);
    }

    pub fn nodesInCreationOrder(self: *const Tree) []const *Node {
        return self.nodes.items;
    }

    pub fn createNode(
        self: *Tree,
        location_value: SourceLocation,
        payload: Payload,
    ) CreateNodeError!*Node {
        const next_compatibility_id = std.math.add(i64, self.next_node_id, 1) catch
            return error.NodeIdOverflow;
        if (self.next_local_node_id == std.math.maxInt(u32))
            return error.NodeIdOverflow;
        const local_node_id = LocalNodeId.init(self.next_local_node_id);
        const node = try self.syntaxAllocator().create(Node);
        var location = location_value;
        if (location.source_name != null) location.source_name = self.source_name;
        node.* = .{
            .id = next_compatibility_id,
            .node_ref = .{
                .source = self.source_id,
                .local_node = local_node_id,
            },
            .location = location,
            .payload = payload,
            .semantic_context = self.semantic_context,
        };
        try self.nodes.append(self.syntaxAllocator(), node);
        self.next_node_id = next_compatibility_id;
        self.next_local_node_id += 1;
        return node;
    }

    /// Moves a separately allocated Yul tree under this Solidity tree's
    /// lifetime. Yul containers retain the backing allocator they were parsed
    /// with and are torn down before the Solidity arena.
    pub fn adoptYulAst(self: *Tree, ast: *YulAST.AST) std.mem.Allocator.Error!*YulAST.AST {
        const owned = try self.backing_allocator.create(YulAST.AST);
        errdefer self.backing_allocator.destroy(owned);
        try self.owned_yul_asts.append(self.backing_allocator, owned);
        owned.* = ast.*;
        ast.* = undefined;
        return owned;
    }
};

pub const CreateNodeError = std.mem.Allocator.Error || error{NodeIdOverflow};

test "closed AST hierarchy keeps arena-owned identity and source lifetime" {
    var tree = try Tree.init(std.testing.allocator, "contract C {}", "C.sol");
    defer tree.deinit();

    const name = try tree.ownString("C");
    const contract = try tree.createNode(
        .{ .start = 0, .end = 13, .source_name = tree.source_name },
        .{ .contract_definition = .{
            .declaration = .{
                .name = name,
                .name_location = .{ .start = 9, .end = 10, .source_name = tree.source_name },
            },
        } },
    );
    const nodes = try tree.ownSlice(*Node, &.{contract});
    tree.root = try tree.createNode(
        .{ .start = 0, .end = 13, .source_name = tree.source_name },
        .{ .source_unit = .{ .nodes = nodes } },
    );

    try std.testing.expectEqual(Kind.contract_definition, contract.nodeKind());
    try std.testing.expectEqualStrings("C", contract.declarationConst().?.name);
    try std.testing.expectEqual(@as(i64, 2), tree.root.?.id);
    try std.testing.expectEqualStrings("C.sol", tree.root.?.location.source_name.?);
}

test "source trees assign dense nominal local node identities" {
    const source_id = SourceId.init(17);
    var tree = try Tree.initWithSourceId(
        std.testing.allocator,
        source_id,
        "a b",
        "A.sol",
    );
    defer tree.deinit();

    const first = try tree.createNode(.{}, .{ .identifier = .{ .name = "a" } });
    const second = try tree.createNode(.{}, .{ .identifier = .{ .name = "b" } });
    try std.testing.expectEqual(source_id, first.node_ref.source);
    try std.testing.expectEqual(@as(u32, 0), first.node_ref.local_node.index());
    try std.testing.expectEqual(source_id, second.node_ref.source);
    try std.testing.expectEqual(@as(u32, 1), second.node_ref.local_node.index());
    try std.testing.expectEqual(@as(i64, 1), first.id);
    try std.testing.expectEqual(@as(i64, 2), second.id);
    try std.testing.expectEqualSlices(
        *Node,
        &.{ first, second },
        tree.nodesInCreationOrder(),
    );
}

test "syntax categories and null-versus-empty argument lists stay distinct" {
    var tree = try Tree.init(std.testing.allocator, "f; f();", "A.sol");
    defer tree.deinit();
    const path = try tree.createNode(
        .{ .start = 0, .end = 1, .source_name = tree.source_name },
        .{ .identifier_path = .{
            .path = try tree.ownSlice([]const u8, &.{try tree.ownString("f")}),
            .path_locations = try tree.ownSlice(SourceLocation, &.{.{
                .start = 0,
                .end = 1,
                .source_name = tree.source_name,
            }}),
        } },
    );
    const without_call = try tree.createNode(
        path.location,
        .{ .modifier_invocation = .{ .modifier_name = path, .arguments = null } },
    );
    const with_empty_call = try tree.createNode(
        path.location,
        .{ .modifier_invocation = .{ .modifier_name = path, .arguments = &.{} } },
    );
    try std.testing.expect(without_call.payload.modifier_invocation.arguments == null);
    try std.testing.expectEqual(
        @as(usize, 0),
        with_empty_call.payload.modifier_invocation.arguments.?.len,
    );
}
