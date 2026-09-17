// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Solidity AST JSON translated from `ASTJsonExporter.cpp`.
//!
//! Parsed export omits unavailable semantic members exactly like upstream's
//! null-member removal. Analyzed export retains the compilation-scoped type
//! provider and emits the complete annotation-backed surface.

const std = @import("std");
const AST = @import("ast.zig");
const ASTAnnotations = @import("ast_annotations.zig");
const ASTCpp = @import("ast.zig");
const ASTEnums = @import("ast_enums.zig");
const Types = @import("types.zig");
const TypeBehavior = @import("types.zig");
const TypeProviderModule = @import("type_provider.zig");
const JSON = @import("../../libsolutil/json.zig");
const Keccak256 = @import("../../libsolutil/keccak256.zig");
const TokenModule = @import("../../liblangutil/token.zig");
const YulJson = @import("../../libyul/asm_json_converter.zig");
const EVMDialect = @import("../../libyul/backends/evm/evm_dialect.zig");
const CompatibilityIds = @import("../../incremental/compatibility_ids.zig");
const CompatibilityIdResolver = @import("compatibility_id_resolver.zig").CompatibilityIdResolver;

const Json = JSON.Json;
const SourceLocation = @import("../../liblangutil/source_location.zig").SourceLocation;

pub const ExportError = YulJson.JsonError || TypeBehavior.BehaviorError || ASTCpp.AstError || error{
    InvalidAst,
    UnsupportedNode,
};

pub const SourceIndex = struct {
    name: []const u8,
    index: usize,
};

const Context = struct {
    in_event: bool = false,
};

/// Converts the closed arena-owned syntax tree without taking ownership of it.
/// Every string placed in the returned value remains borrowed from either the
/// tree or this exporter's allocator, so callers keep both alive until JSON is
/// printed or cloned.
pub const ASTJsonExporter = struct {
    allocator: std.mem.Allocator,
    source_indices: []const SourceIndex,
    absolute_path: ?[]const u8,
    compatibility_ids: CompatibilityIdResolver,
    type_provider: ?*TypeProviderModule.TypeProvider = null,
    analysis_complete: bool = false,

    pub fn init(
        allocator: std.mem.Allocator,
        source_indices: []const SourceIndex,
        absolute_path: ?[]const u8,
        compatibility_ids: CompatibilityIdResolver,
    ) ASTJsonExporter {
        return .{
            .allocator = allocator,
            .source_indices = source_indices,
            .absolute_path = absolute_path,
            .compatibility_ids = compatibility_ids,
        };
    }

    pub fn initAnalyzed(
        allocator: std.mem.Allocator,
        source_indices: []const SourceIndex,
        absolute_path: ?[]const u8,
        compatibility_ids: CompatibilityIdResolver,
        type_provider: *TypeProviderModule.TypeProvider,
    ) ASTJsonExporter {
        var exporter = init(allocator, source_indices, absolute_path, compatibility_ids);
        exporter.type_provider = type_provider;
        exporter.analysis_complete = true;
        return exporter;
    }

    pub fn toJson(self: *ASTJsonExporter, node: *const AST.Node) ExportError!Json {
        return self.nodeToJson(node, .{});
    }

    fn nodeToJson(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        context: Context,
    ) ExportError!Json {
        var result = try self.baseNode(node, nodeType(node));
        if (statementDocumentation(node)) |documentation|
            try putString(self.allocator, &result, "documentation", documentation);

        switch (node.payload) {
            .source_unit => |value| {
                if (value.license) |license| try putString(self.allocator, &result, "license", license);
                if (self.absolute_path) |path| try putString(self.allocator, &result, "absolutePath", path);
                try self.putExportedSymbols(node, &result);
                try self.putNodeList(&result, "nodes", value.nodes, .{});
                if (value.experimental_solidity)
                    try result.object.put(self.allocator, "experimentalSolidity", .{ .bool = true });
            },
            .pragma_directive => |value| try self.putStrings(&result, "literals", value.literals),
            .import_directive => |value| {
                try putString(self.allocator, &result, "file", value.path);
                if (ASTAnnotations.annotationConst(node)) |annotation_value|
                    switch (annotation_value.*) {
                        .import => |annotation| {
                            if (annotation.source_unit) |source_unit|
                                try self.putNodeId(&result, "sourceUnit", source_unit);
                            if (annotation.absolute_path.value) |path|
                                try putString(self.allocator, &result, "absolutePath", path);
                        },
                        else => {},
                    };
                try putString(self.allocator, &result, "unitAlias", value.declaration.name);
                try self.putLocation(&result, "nameLocation", value.declaration.name_location);
                var aliases = std.json.Array.init(self.allocator);
                for (value.symbol_aliases) |alias| {
                    var entry: Json = .{ .object = .empty };
                    try entry.object.put(self.allocator, "foreign", try self.nodeToJson(alias.symbol, .{}));
                    if (alias.alias) |name| try putString(self.allocator, &entry, "local", name);
                    try self.putLocation(&entry, "nameLocation", value.declaration.name_location);
                    try aliases.append(entry);
                }
                try result.object.put(self.allocator, "symbolAliases", .{ .array = aliases });
                try self.putScope(node, &result);
            },
            .structured_documentation => |value| try putString(self.allocator, &result, "text", value.text),
            .contract_definition => |value| {
                try putString(self.allocator, &result, "name", value.declaration.name);
                try self.putLocation(&result, "nameLocation", value.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
                try putString(self.allocator, &result, "contractKind", ASTCpp.contractKindToString(value.contract_kind));
                try result.object.put(self.allocator, "abstract", .{ .bool = value.abstract });
                try self.putNodeList(&result, "baseContracts", value.base_contracts, .{});
                if (self.analysis_complete)
                    try self.putAnalyzedContractAttributes(node, &result)
                else {
                    try result.object.put(self.allocator, "contractDependencies", emptyArray(self.allocator));
                    try result.object.put(self.allocator, "usedEvents", emptyArray(self.allocator));
                    try result.object.put(self.allocator, "usedErrors", emptyArray(self.allocator));
                }

                var nodes = std.json.Array.init(self.allocator);
                for (value.sub_nodes) |child| {
                    try nodes.append(try self.nodeToJson(child, .{}));
                }
                try result.object.put(self.allocator, "nodes", .{ .array = nodes });
                if (value.storage_layout_specifier) |storage|
                    try result.object.put(self.allocator, "storageLayout", try self.nodeToJson(storage, .{}));
                try self.putScope(node, &result);
            },
            .storage_layout_specifier => |value| {
                try result.object.put(
                    self.allocator,
                    "baseSlotExpression",
                    try self.nodeToJson(value.base_slot_expression, .{}),
                );
            },
            .identifier_path => |value| {
                const name = try joinPath(self.allocator, value.path);
                try result.object.put(self.allocator, "name", .{ .string = name });
                try self.putLocations(&result, "nameLocations", value.path_locations);
                if (identifierPathAnnotation(node)) |annotation|
                    if (annotation.referenced_declaration) |declaration|
                        try self.putNodeId(&result, "referencedDeclaration", declaration);
            },
            .inheritance_specifier => |value| {
                try result.object.put(self.allocator, "baseName", try self.nodeToJson(value.base_name, .{}));
                if (value.arguments) |arguments| try self.putNodeList(&result, "arguments", arguments, .{});
            },
            .using_for_directive => |value| {
                if (value.type_name) |type_name|
                    try result.object.put(self.allocator, "typeName", try self.nodeToJson(type_name, .{}));
                if (value.uses_braces) {
                    var functions = std.json.Array.init(self.allocator);
                    for (value.functions_and_operators) |entry| {
                        var function: Json = .{ .object = .empty };
                        if (entry.operator) |operator| {
                            try function.object.put(
                                self.allocator,
                                "definition",
                                try self.nodeToJson(entry.function_or_library, .{}),
                            );
                            try putString(
                                self.allocator,
                                &function,
                                "operator",
                                TokenModule.toString(operator) orelse return error.InvalidAst,
                            );
                        } else {
                            try function.object.put(
                                self.allocator,
                                "function",
                                try self.nodeToJson(entry.function_or_library, .{}),
                            );
                        }
                        try functions.append(function);
                    }
                    try result.object.put(self.allocator, "functionList", .{ .array = functions });
                } else {
                    if (value.functions_and_operators.len != 1 or
                        value.functions_and_operators[0].operator != null)
                        return error.InvalidAst;
                    try result.object.put(
                        self.allocator,
                        "libraryName",
                        try self.nodeToJson(value.functions_and_operators[0].function_or_library, .{}),
                    );
                }
                try result.object.put(self.allocator, "global", .{ .bool = value.global });
            },
            .struct_definition => |value| {
                try putString(self.allocator, &result, "name", value.declaration.name);
                try self.putLocation(&result, "nameLocation", value.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
                try putString(self.allocator, &result, "visibility", "public");
                try self.putNodeList(&result, "members", value.members, .{});
                try self.putCanonicalName(node, &result);
                try self.putScope(node, &result);
            },
            .enum_definition => |value| {
                try putString(self.allocator, &result, "name", value.declaration.name);
                try self.putLocation(&result, "nameLocation", value.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
                try self.putNodeList(&result, "members", value.members, .{});
                try self.putCanonicalName(node, &result);
            },
            .enum_value => |value| {
                try putString(self.allocator, &result, "name", value.declaration.name);
                try self.putLocation(&result, "nameLocation", value.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
            },
            .user_defined_value_type_definition => |value| {
                try putString(self.allocator, &result, "name", value.declaration.name);
                try self.putLocation(&result, "nameLocation", value.declaration.name_location);
                try result.object.put(
                    self.allocator,
                    "underlyingType",
                    try self.nodeToJson(value.underlying_type, .{}),
                );
                try self.putCanonicalName(node, &result);
            },
            .parameter_list => |value| try self.putNodeList(&result, "parameters", value.parameters, context),
            .override_specifier => |value| try self.putNodeList(&result, "overrides", value.overrides, .{}),
            .function_definition => |value| {
                try putString(self.allocator, &result, "name", value.callable.declaration.name);
                try self.putLocation(&result, "nameLocation", value.callable.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
                const kind = if (value.free)
                    "freeFunction"
                else
                    TokenModule.toString(value.kind) orelse return error.InvalidAst;
                try putString(self.allocator, &result, "kind", kind);
                try putString(
                    self.allocator,
                    &result,
                    "stateMutability",
                    ASTEnums.stateMutabilityToString(value.state_mutability),
                );
                try result.object.put(self.allocator, "virtual", .{ .bool = value.callable.marked_virtual });
                if (value.callable.overrides) |overrides|
                    try result.object.put(self.allocator, "overrides", try self.nodeToJson(overrides, .{}));
                try result.object.put(
                    self.allocator,
                    "parameters",
                    try self.nodeToJson(value.callable.parameters, .{}),
                );
                if (value.callable.return_parameters) |returns|
                    try result.object.put(self.allocator, "returnParameters", try self.nodeToJson(returns, .{}));
                try self.putNodeList(&result, "modifiers", value.modifiers, .{});
                if (value.body) |body|
                    try result.object.put(self.allocator, "body", try self.nodeToJson(body, .{}));
                try result.object.put(self.allocator, "implemented", .{ .bool = value.implemented() });

                if (value.kind == .Constructor) {
                    if (nodeContract(node)) |contract|
                        try putString(
                            self.allocator,
                            &result,
                            "visibility",
                            if (contract.payload.contract_definition.abstract) "internal" else "public",
                        );
                } else {
                    const visibility = value.callable.declaration.effectiveVisibility(
                        if (value.free) .Internal else .Public,
                    );
                    try putString(
                        self.allocator,
                        &result,
                        "visibility",
                        ASTCpp.visibilityToString(visibility) catch return error.InvalidAst,
                    );
                }
                if (self.analysis_complete and node.isPartOfExternalInterface()) {
                    const provider = self.type_provider orelse return error.InvalidAst;
                    const selector = try ASTCpp.declarationExternalIdentifierHexAlloc(
                        provider,
                        self.allocator,
                        node,
                    );
                    try putString(self.allocator, &result, "functionSelector", selector);
                }
                if (callableAnnotation(node)) |annotation|
                    if (annotation.base_functions.items.len != 0)
                        try self.putSortedNodeIds(
                            &result,
                            "baseFunctions",
                            annotation.base_functions.items,
                        );
                try self.putScope(node, &result);
            },
            .variable_declaration => |value| {
                try putString(self.allocator, &result, "name", value.declaration.name);
                try self.putLocation(&result, "nameLocation", value.declaration.name_location);
                if (value.type_name) |type_name|
                    try result.object.put(self.allocator, "typeName", try self.nodeToJson(type_name, .{}));
                try result.object.put(
                    self.allocator,
                    "constant",
                    .{ .bool = value.mutability == .Constant },
                );
                try putString(self.allocator, &result, "mutability", ASTCpp.mutabilityToString(value.mutability));
                const state_variable = ASTCpp.isStateVariable(node);
                try result.object.put(self.allocator, "stateVariable", .{ .bool = state_variable });
                try putString(
                    self.allocator,
                    &result,
                    "storageLocation",
                    ASTCpp.variableLocationToString(value.reference_location),
                );
                if (value.overrides) |overrides|
                    try result.object.put(self.allocator, "overrides", try self.nodeToJson(overrides, .{}));
                const visibility = value.declaration.effectiveVisibility(.Internal);
                try putString(
                    self.allocator,
                    &result,
                    "visibility",
                    ASTCpp.visibilityToString(visibility) catch return error.InvalidAst,
                );
                if (value.value) |initial_value|
                    try result.object.put(self.allocator, "value", try self.nodeToJson(initial_value, .{}));
                const variable_annotation = variableAnnotation(node);
                try result.object.put(
                    self.allocator,
                    "typeDescriptions",
                    try self.typePointerToJson(
                        if (variable_annotation) |annotation| annotation.type_ref else null,
                        true,
                    ),
                );
                if (self.analysis_complete and state_variable and node.isPublic()) {
                    const provider = self.type_provider orelse return error.InvalidAst;
                    const selector = try ASTCpp.declarationExternalIdentifierHexAlloc(
                        provider,
                        self.allocator,
                        node,
                    );
                    try putString(self.allocator, &result, "functionSelector", selector);
                }
                if (state_variable)
                    if (value.documentation) |documentation|
                        try result.object.put(
                            self.allocator,
                            "documentation",
                            try self.nodeToJson(documentation, .{}),
                        );
                if (context.in_event)
                    try result.object.put(self.allocator, "indexed", .{ .bool = value.indexed });
                if (variable_annotation) |annotation|
                    if (annotation.base_functions.items.len != 0)
                        try self.putSortedNodeIds(
                            &result,
                            "baseFunctions",
                            annotation.base_functions.items,
                        );
                try self.putScope(node, &result);
            },
            .modifier_definition => |value| {
                try putString(self.allocator, &result, "name", value.callable.declaration.name);
                try self.putLocation(&result, "nameLocation", value.callable.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
                try putString(self.allocator, &result, "visibility", "internal");
                try result.object.put(
                    self.allocator,
                    "parameters",
                    try self.nodeToJson(value.callable.parameters, .{}),
                );
                try result.object.put(self.allocator, "virtual", .{ .bool = value.callable.marked_virtual });
                if (value.callable.overrides) |overrides|
                    try result.object.put(self.allocator, "overrides", try self.nodeToJson(overrides, .{}));
                if (value.body) |body|
                    try result.object.put(self.allocator, "body", try self.nodeToJson(body, .{}));
                if (callableAnnotation(node)) |annotation|
                    if (annotation.base_functions.items.len != 0)
                        try self.putSortedNodeIds(
                            &result,
                            "baseModifiers",
                            annotation.base_functions.items,
                        );
            },
            .modifier_invocation => |value| {
                try result.object.put(
                    self.allocator,
                    "modifierName",
                    try self.nodeToJson(value.modifier_name, .{}),
                );
                if (value.arguments) |arguments| try self.putNodeList(&result, "arguments", arguments, .{});
                if (identifierPathAnnotation(value.modifier_name)) |annotation|
                    if (annotation.referenced_declaration) |declaration|
                        switch (declaration.nodeKind()) {
                            .modifier_definition => try putString(
                                self.allocator,
                                &result,
                                "kind",
                                "modifierInvocation",
                            ),
                            .contract_definition => try putString(
                                self.allocator,
                                &result,
                                "kind",
                                "baseConstructorSpecifier",
                            ),
                            else => {},
                        };
            },
            .event_definition => |value| {
                try putString(self.allocator, &result, "name", value.callable.declaration.name);
                try self.putLocation(&result, "nameLocation", value.callable.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
                try result.object.put(
                    self.allocator,
                    "parameters",
                    try self.nodeToJson(value.callable.parameters, .{ .in_event = true }),
                );
                try result.object.put(self.allocator, "anonymous", .{ .bool = value.anonymous });
                if (self.analysis_complete) {
                    const provider = self.type_provider orelse return error.InvalidAst;
                    const event_type = try provider.functionFromEvent(node);
                    const signature = try TypeBehavior.externalSignatureAlloc(
                        provider,
                        self.allocator,
                        event_type.payload.Function,
                    );
                    const digest = Keccak256.keccak256(signature);
                    const rendered = digest.hex();
                    const selector = try self.allocator.dupe(u8, &rendered);
                    try putString(self.allocator, &result, "eventSelector", selector);
                }
            },
            .error_definition => |value| {
                try putString(self.allocator, &result, "name", value.callable.declaration.name);
                try self.putLocation(&result, "nameLocation", value.callable.declaration.name_location);
                if (value.documentation) |documentation|
                    try result.object.put(self.allocator, "documentation", try self.nodeToJson(documentation, .{}));
                try result.object.put(
                    self.allocator,
                    "parameters",
                    try self.nodeToJson(value.callable.parameters, .{}),
                );
                if (self.analysis_complete) {
                    const provider = self.type_provider orelse return error.InvalidAst;
                    const error_type = try provider.functionFromError(node);
                    const selector = try TypeBehavior.externalIdentifierHexAlloc(
                        provider,
                        self.allocator,
                        error_type.payload.Function,
                    );
                    try putString(self.allocator, &result, "errorSelector", selector);
                }
            },
            .magic_variable_declaration => return error.UnsupportedNode,
            .elementary_type_name => |value| {
                const name = try value.type_name.renderAlloc(self.allocator, false);
                try result.object.put(self.allocator, "name", .{ .string = name });
                try result.object.put(
                    self.allocator,
                    "typeDescriptions",
                    try self.typePointerToJson(typeNameType(node), true),
                );
                if (value.state_mutability) |mutability|
                    try putString(
                        self.allocator,
                        &result,
                        "stateMutability",
                        ASTEnums.stateMutabilityToString(mutability),
                    );
            },
            .user_defined_type_name => |value| {
                try result.object.put(self.allocator, "pathNode", try self.nodeToJson(value.path_node, .{}));
                if (identifierPathAnnotation(value.path_node)) |annotation|
                    if (annotation.referenced_declaration) |declaration|
                        try self.putNodeId(&result, "referencedDeclaration", declaration);
                try result.object.put(
                    self.allocator,
                    "typeDescriptions",
                    try self.typePointerToJson(typeNameType(node), true),
                );
            },
            .function_type_name => |value| {
                const visibility = if (value.visibility == .Default) AST.Visibility.Internal else value.visibility;
                try putString(
                    self.allocator,
                    &result,
                    "visibility",
                    ASTCpp.visibilityToString(visibility) catch return error.InvalidAst,
                );
                try putString(
                    self.allocator,
                    &result,
                    "stateMutability",
                    ASTEnums.stateMutabilityToString(value.state_mutability),
                );
                try result.object.put(
                    self.allocator,
                    "parameterTypes",
                    try self.nodeToJson(value.parameter_types, .{}),
                );
                try result.object.put(
                    self.allocator,
                    "returnParameterTypes",
                    try self.nodeToJson(value.return_types, .{}),
                );
                try result.object.put(
                    self.allocator,
                    "typeDescriptions",
                    try self.typePointerToJson(typeNameType(node), true),
                );
            },
            .mapping => |value| {
                try result.object.put(self.allocator, "keyType", try self.nodeToJson(value.key_type, .{}));
                try putString(self.allocator, &result, "keyName", value.key_name);
                try self.putLocation(&result, "keyNameLocation", value.key_name_location);
                try result.object.put(self.allocator, "valueType", try self.nodeToJson(value.value_type, .{}));
                try putString(self.allocator, &result, "valueName", value.value_name);
                try self.putLocation(&result, "valueNameLocation", value.value_name_location);
                try result.object.put(
                    self.allocator,
                    "typeDescriptions",
                    try self.typePointerToJson(typeNameType(node), true),
                );
            },
            .array_type_name => |value| {
                try result.object.put(self.allocator, "baseType", try self.nodeToJson(value.base_type, .{}));
                if (value.length) |length|
                    try result.object.put(self.allocator, "length", try self.nodeToJson(length, .{}));
                try result.object.put(
                    self.allocator,
                    "typeDescriptions",
                    try self.typePointerToJson(typeNameType(node), true),
                );
            },
            .inline_assembly => |value| {
                const operations = value.operations orelse return error.InvalidAst;
                const dialect_value = value.dialect orelse return error.InvalidAst;
                var converter = YulJson.AsmJsonConverter.init(
                    self.allocator,
                    dialect_value,
                    self.sourceIndex(node.location),
                );
                try result.object.put(
                    self.allocator,
                    "AST",
                    try converter.convertBlock(operations.root()),
                );
                try result.object.put(
                    self.allocator,
                    "externalReferences",
                    try self.inlineAssemblyExternalReferences(node),
                );
                const evm_dialect = EVMDialect.fromDialect(dialect_value) orelse return error.InvalidAst;
                try putString(self.allocator, &result, "evmVersion", evm_dialect.evmVersion().name());
                if (value.flags) |flags| {
                    var array = std.json.Array.init(self.allocator);
                    for (flags) |flag| {
                        if (flag) |present|
                            try array.append(.{ .string = present })
                        else
                            try array.append(.null);
                    }
                    try result.object.put(self.allocator, "flags", .{ .array = array });
                }
            },
            .block => |value| try self.putNodeList(&result, "statements", value.statements, .{}),
            .placeholder_statement, .continue_statement, .break_statement, .throw_statement => {},
            .if_statement => |value| {
                try result.object.put(self.allocator, "condition", try self.nodeToJson(value.condition, .{}));
                try result.object.put(self.allocator, "trueBody", try self.nodeToJson(value.true_body, .{}));
                if (value.false_body) |body|
                    try result.object.put(self.allocator, "falseBody", try self.nodeToJson(body, .{}));
            },
            .try_catch_clause => |value| {
                try putString(self.allocator, &result, "errorName", value.error_name);
                if (value.parameters) |parameters|
                    try result.object.put(self.allocator, "parameters", try self.nodeToJson(parameters, .{}));
                try result.object.put(self.allocator, "block", try self.nodeToJson(value.block, .{}));
            },
            .try_statement => |value| {
                try result.object.put(
                    self.allocator,
                    "externalCall",
                    try self.nodeToJson(value.external_call, .{}),
                );
                try self.putNodeList(&result, "clauses", value.clauses, .{});
            },
            .while_statement => |value| {
                try result.object.put(self.allocator, "condition", try self.nodeToJson(value.condition, .{}));
                try result.object.put(self.allocator, "body", try self.nodeToJson(value.body, .{}));
            },
            .for_statement => |value| {
                if (value.initialization_expression) |expression|
                    try result.object.put(
                        self.allocator,
                        "initializationExpression",
                        try self.nodeToJson(expression, .{}),
                    );
                if (value.condition) |condition|
                    try result.object.put(self.allocator, "condition", try self.nodeToJson(condition, .{}));
                if (value.loop_expression) |expression|
                    try result.object.put(
                        self.allocator,
                        "loopExpression",
                        try self.nodeToJson(expression, .{}),
                    );
                try result.object.put(self.allocator, "body", try self.nodeToJson(value.body, .{}));
                if (forStatementAnnotation(node)) |annotation|
                    if (annotation.is_simple_counter_loop.value) |is_simple|
                        try result.object.put(
                            self.allocator,
                            "isSimpleCounterLoop",
                            .{ .bool = is_simple },
                        );
            },
            .return_statement => |value| {
                if (value.expression) |expression|
                    try result.object.put(
                        self.allocator,
                        "expression",
                        try self.nodeToJson(expression, .{}),
                    );
                if (returnAnnotation(node)) |annotation|
                    if (annotation.function_return_parameters) |parameters|
                        try self.putNodeId(
                            &result,
                            "functionReturnParameters",
                            parameters,
                        );
            },
            .revert_statement => |value| try result.object.put(
                self.allocator,
                "errorCall",
                try self.nodeToJson(value.error_call, .{}),
            ),
            .emit_statement => |value| try result.object.put(
                self.allocator,
                "eventCall",
                try self.nodeToJson(value.event_call, .{}),
            ),
            .variable_declaration_statement => |value| {
                var assignments = std.json.Array.init(self.allocator);
                var declarations = std.json.Array.init(self.allocator);
                for (value.declarations) |declaration| {
                    if (declaration) |present| {
                        try assignments.append(.{ .integer = try self.nodeId(present) });
                        try declarations.append(try self.nodeToJson(present, .{}));
                    } else {
                        try assignments.append(.null);
                        try declarations.append(.null);
                    }
                }
                try result.object.put(self.allocator, "assignments", .{ .array = assignments });
                try result.object.put(self.allocator, "declarations", .{ .array = declarations });
                if (value.initial_value) |initial_value|
                    try result.object.put(
                        self.allocator,
                        "initialValue",
                        try self.nodeToJson(initial_value, .{}),
                    );
            },
            .expression_statement => |value| try result.object.put(
                self.allocator,
                "expression",
                try self.nodeToJson(value.expression, .{}),
            ),
            .conditional => |value| {
                try result.object.put(self.allocator, "condition", try self.nodeToJson(value.condition, .{}));
                try result.object.put(
                    self.allocator,
                    "trueExpression",
                    try self.nodeToJson(value.true_expression, .{}),
                );
                try result.object.put(
                    self.allocator,
                    "falseExpression",
                    try self.nodeToJson(value.false_expression, .{}),
                );
                try self.putExpressionAttributes(node, &result);
            },
            .assignment => |value| {
                try putString(
                    self.allocator,
                    &result,
                    "operator",
                    TokenModule.toString(value.operator) orelse return error.InvalidAst,
                );
                try result.object.put(
                    self.allocator,
                    "leftHandSide",
                    try self.nodeToJson(value.left_hand_side, .{}),
                );
                try result.object.put(
                    self.allocator,
                    "rightHandSide",
                    try self.nodeToJson(value.right_hand_side, .{}),
                );
                try self.putExpressionAttributes(node, &result);
            },
            .tuple_expression => |value| {
                try result.object.put(self.allocator, "isInlineArray", .{ .bool = value.is_inline_array });
                try self.putOptionalNodeList(&result, "components", value.components);
                try self.putExpressionAttributes(node, &result);
            },
            .unary_operation => |value| {
                try result.object.put(self.allocator, "prefix", .{ .bool = value.is_prefix });
                try putString(
                    self.allocator,
                    &result,
                    "operator",
                    TokenModule.toString(value.operator) orelse return error.InvalidAst,
                );
                try result.object.put(
                    self.allocator,
                    "subExpression",
                    try self.nodeToJson(value.sub_expression, .{}),
                );
                try self.putUserDefinedOperation(node, &result);
                try self.putExpressionAttributes(node, &result);
            },
            .binary_operation => |value| {
                try putString(
                    self.allocator,
                    &result,
                    "operator",
                    TokenModule.toString(value.operator) orelse return error.InvalidAst,
                );
                try result.object.put(self.allocator, "leftExpression", try self.nodeToJson(value.left, .{}));
                try result.object.put(self.allocator, "rightExpression", try self.nodeToJson(value.right, .{}));
                const common_type = if (binaryOperationAnnotation(node)) |annotation|
                    annotation.common_type
                else
                    null;
                try result.object.put(
                    self.allocator,
                    "commonType",
                    try self.typePointerToJson(common_type, false),
                );
                try self.putUserDefinedOperation(node, &result);
                try self.putExpressionAttributes(node, &result);
            },
            .function_call => |value| {
                try result.object.put(
                    self.allocator,
                    "expression",
                    try self.nodeToJson(value.expression, .{}),
                );
                try self.putStrings(&result, "names", value.names);
                try self.putLocations(&result, "nameLocations", value.name_locations);
                try self.putNodeList(&result, "arguments", value.arguments, .{});
                const call_annotation = functionCallAnnotation(node);
                try result.object.put(
                    self.allocator,
                    "tryCall",
                    .{ .bool = if (call_annotation) |annotation| annotation.try_call else false },
                );
                if (call_annotation) |annotation|
                    if (annotation.kind.value) |kind|
                        try putString(
                            self.allocator,
                            &result,
                            "kind",
                            functionCallKind(kind),
                        );
                try self.putExpressionAttributes(node, &result);
            },
            .function_call_options => |value| {
                try result.object.put(
                    self.allocator,
                    "expression",
                    try self.nodeToJson(value.expression, .{}),
                );
                try self.putStrings(&result, "names", value.names);
                try self.putNodeList(&result, "options", value.options, .{});
                try self.putExpressionAttributes(node, &result);
            },
            .new_expression => |value| {
                try result.object.put(self.allocator, "typeName", try self.nodeToJson(value.type_name, .{}));
                try self.putExpressionAttributes(node, &result);
            },
            .member_access => |value| {
                try putString(self.allocator, &result, "memberName", value.member_name);
                try self.putLocation(&result, "memberLocation", value.member_location);
                try result.object.put(
                    self.allocator,
                    "expression",
                    try self.nodeToJson(value.expression, .{}),
                );
                if (memberAccessAnnotation(node)) |annotation|
                    if (annotation.referenced_declaration) |declaration|
                        try self.putNodeId(&result, "referencedDeclaration", declaration);
                try self.putExpressionAttributes(node, &result);
            },
            .index_access => |value| {
                try result.object.put(
                    self.allocator,
                    "baseExpression",
                    try self.nodeToJson(value.base, .{}),
                );
                if (value.index) |index|
                    try result.object.put(
                        self.allocator,
                        "indexExpression",
                        try self.nodeToJson(index, .{}),
                    );
                try self.putExpressionAttributes(node, &result);
            },
            .index_range_access => |value| {
                try result.object.put(
                    self.allocator,
                    "baseExpression",
                    try self.nodeToJson(value.base, .{}),
                );
                if (value.start) |start|
                    try result.object.put(
                        self.allocator,
                        "startExpression",
                        try self.nodeToJson(start, .{}),
                    );
                if (value.end) |end|
                    try result.object.put(
                        self.allocator,
                        "endExpression",
                        try self.nodeToJson(end, .{}),
                    );
                try self.putExpressionAttributes(node, &result);
            },
            .identifier => |value| {
                try putString(self.allocator, &result, "name", value.name);
                const annotation = identifierAnnotation(node);
                if (annotation) |identifier_annotation|
                    if (identifier_annotation.referenced_declaration) |declaration|
                        try self.putNodeId(&result, "referencedDeclaration", declaration);
                try self.putSortedNodeIds(
                    &result,
                    "overloadedDeclarations",
                    if (annotation) |identifier_annotation|
                        identifier_annotation.overloaded_declarations.items
                    else
                        &.{},
                );
                const expression = if (annotation) |identifier_annotation|
                    &identifier_annotation.expression
                else
                    null;
                try result.object.put(
                    self.allocator,
                    "typeDescriptions",
                    try self.typePointerToJson(
                        if (expression) |entry| entry.type_ref else null,
                        false,
                    ),
                );
                try self.putArgumentTypes(expression, &result);
            },
            .elementary_type_name_expression => |value| {
                try result.object.put(self.allocator, "typeName", try self.nodeToJson(value.type_name, .{}));
                try self.putExpressionAttributes(node, &result);
            },
            .literal => |value| {
                try putString(self.allocator, &result, "kind", literalKind(value.token) orelse return error.InvalidAst);
                if (std.unicode.utf8ValidateSlice(value.value))
                    try putString(self.allocator, &result, "value", value.value);
                const hex_value = try hexAlloc(self.allocator, value.value);
                try result.object.put(self.allocator, "hexValue", .{ .string = hex_value });
                if (value.sub_denomination != .None) {
                    const token: AST.Token = @enumFromInt(@intFromEnum(value.sub_denomination));
                    try putString(
                        self.allocator,
                        &result,
                        "subdenomination",
                        TokenModule.toString(token) orelse return error.InvalidAst,
                    );
                }
                try self.putExpressionAttributes(node, &result);
            },
            .type_class_definition,
            .type_class_instantiation,
            .type_definition,
            .type_class_name,
            .builtin,
            .for_all_quantifier,
            => return error.UnsupportedNode,
        }
        return result;
    }

    fn putExportedSymbols(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        result: *Json,
    ) ExportError!void {
        const annotation = ASTAnnotations.annotationConst(node) orelse return;
        const exported = switch (annotation.*) {
            .source_unit => |value| value.exported_symbols.value,
            else => return,
        } orelse return;
        var symbols: Json = .{ .object = .empty };
        for (exported) |entry| {
            var declarations = std.json.Array.init(self.allocator);
            for (entry.declarations) |declaration|
                try declarations.append(.{ .integer = try self.nodeId(declaration) });
            try symbols.object.put(
                self.allocator,
                entry.name,
                .{ .array = declarations },
            );
        }
        try result.object.put(self.allocator, "exportedSymbols", symbols);
    }

    fn putAnalyzedContractAttributes(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        result: *Json,
    ) ExportError!void {
        const annotation_value = ASTAnnotations.annotationConst(node) orelse return error.InvalidAst;
        const annotation = switch (annotation_value.*) {
            .contract_definition => |*value| value,
            else => return error.InvalidAst,
        };
        if (annotation.type_declaration.canonical_name.value) |canonical|
            try putString(self.allocator, result, "canonicalName", canonical);
        if (annotation.unimplemented_declarations) |unimplemented|
            try result.object.put(
                self.allocator,
                "fullyImplemented",
                .{ .bool = unimplemented.len == 0 },
            );
        if (annotation.linearized_base_contracts.len != 0)
            try self.putNodeIds(
                result,
                "linearizedBaseContracts",
                annotation.linearized_base_contracts,
            );
        var dependencies = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (annotation.contract_dependencies.items) |dependency|
            try dependencies.append(.{ .integer = try self.nodeId(dependency.contract) });
        try result.object.put(
            self.allocator,
            "contractDependencies",
            .{ .array = dependencies },
        );
        const interface_events = try ASTCpp.contractInterfaceEventsAlloc(
            self.allocator,
            node,
            false,
        );
        defer self.allocator.free(interface_events);
        try self.putSortedNodeIds(result, "usedEvents", interface_events);
        const interface_errors = try ASTCpp.contractInterfaceErrorsAlloc(
            self.allocator,
            node,
            false,
        );
        defer self.allocator.free(interface_errors);
        try self.putSortedNodeIds(result, "usedErrors", interface_errors);
        if (annotation.internal_function_ids.items.len != 0) {
            var identifiers: Json = .{ .object = .empty };
            for (annotation.internal_function_ids.items) |entry| {
                const key = try std.fmt.allocPrint(
                    self.allocator,
                    "{d}",
                    .{try self.nodeId(entry.function)},
                );
                try identifiers.object.put(
                    self.allocator,
                    key,
                    .{ .integer = std.math.cast(i64, entry.id) orelse return error.InvalidAst },
                );
            }
            try result.object.put(self.allocator, "internalFunctionIDs", identifiers);
        }
    }

    fn putCanonicalName(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        result: *Json,
    ) ExportError!void {
        const annotation = ASTAnnotations.annotationConst(node) orelse return;
        const canonical_name = switch (annotation.*) {
            .contract_definition => |value| value.type_declaration.canonical_name.value,
            .struct_declaration => |value| value.type_declaration.canonical_name.value,
            .type_declaration => |value| value.canonical_name.value,
            .type_class_definition => |value| value.type_declaration.canonical_name.value,
            else => null,
        };
        if (canonical_name) |name| try putString(self.allocator, result, "canonicalName", name);
    }

    fn putScope(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        result: *Json,
    ) ExportError!void {
        const scopable = ASTAnnotations.scopableForNodeConst(node) orelse return;
        if (scopable.scope) |scope| try self.putNodeId(result, "scope", scope);
    }

    fn putNodeIds(
        self: *ASTJsonExporter,
        result: *Json,
        name: []const u8,
        nodes: []const *const AST.Node,
    ) ExportError!void {
        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (nodes) |node| try values.append(.{ .integer = try self.nodeId(node) });
        try result.object.put(self.allocator, name, .{ .array = values });
    }

    fn putSortedNodeIds(
        self: *ASTJsonExporter,
        result: *Json,
        name: []const u8,
        nodes: []const *const AST.Node,
    ) ExportError!void {
        var identifiers: std.ArrayList(i64) = .empty;
        defer identifiers.deinit(self.allocator);
        for (nodes) |node| try identifiers.append(self.allocator, try self.nodeId(node));
        std.mem.sort(i64, identifiers.items, {}, std.sort.asc(i64));
        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (identifiers.items) |identifier| try values.append(.{ .integer = identifier });
        try result.object.put(self.allocator, name, .{ .array = values });
    }

    fn typePointerToJson(
        self: *ASTJsonExporter,
        type_ref: ?*const Types.Type,
        without_data_location: bool,
    ) ExportError!Json {
        var result: Json = .{ .object = .empty };
        const concrete = type_ref orelse return result;
        const type_string = try TypeBehavior.toStringAlloc(
            self.allocator,
            concrete,
            without_data_location,
        );
        const type_identifier = try TypeBehavior.compatibilityIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            concrete,
        );
        try putString(self.allocator, &result, "typeString", type_string);
        try putString(self.allocator, &result, "typeIdentifier", type_identifier);
        return result;
    }

    fn putArgumentTypes(
        self: *ASTJsonExporter,
        annotation: ?*const ASTAnnotations.ExpressionAnnotation,
        result: *Json,
    ) ExportError!void {
        const arguments = (annotation orelse return).arguments orelse return;
        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (arguments.types.items) |opaque_type| {
            const concrete: *const Types.Type = @ptrCast(@alignCast(opaque_type));
            try values.append(try self.typePointerToJson(concrete, false));
        }
        try result.object.put(self.allocator, "argumentTypes", .{ .array = values });
    }

    fn putUserDefinedOperation(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        result: *Json,
    ) ExportError!void {
        const annotation = operationAnnotation(node) orelse return;
        const maybe_function = annotation.user_defined_function.value orelse return;
        if (maybe_function) |function|
            try self.putNodeId(result, "function", function);
    }

    fn inlineAssemblyExternalReferences(
        self: *ASTJsonExporter,
        node: *const AST.Node,
    ) ExportError!Json {
        const annotation_value = ASTAnnotations.annotationConst(node) orelse
            return emptyArray(self.allocator);
        const annotation = switch (annotation_value.*) {
            .inline_assembly => |*value| value,
            else => return error.InvalidAst,
        };
        const Entry = struct {
            name: []const u8,
            reference: *const ASTAnnotations.InlineAssemblyExternalReference,

            fn lessThan(_: void, left: @This(), right: @This()) bool {
                const order = std.mem.order(u8, left.name, right.name);
                if (order != .eq) return order == .lt;
                const left_location = if (left.reference.identifier.debug_data) |debug|
                    debug.native_location
                else
                    SourceLocation{};
                const right_location = if (right.reference.identifier.debug_data) |debug|
                    debug.native_location
                else
                    SourceLocation{};
                if (left_location.start != right_location.start)
                    return left_location.start < right_location.start;
                return left_location.end < right_location.end;
            }
        };
        var entries: std.ArrayList(Entry) = .empty;
        defer entries.deinit(self.allocator);
        for (annotation.external_references.items) |*reference|
            try entries.append(self.allocator, .{
                .name = try reference.identifier.name.str(),
                .reference = reference,
            });
        std.mem.sort(Entry, entries.items, {}, Entry.lessThan);

        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (entries.items) |entry| {
            const reference = entry.reference;
            var value: Json = .{ .object = .empty };
            const location = if (reference.identifier.debug_data) |debug|
                debug.native_location
            else
                SourceLocation{};
            try self.putLocation(&value, "src", location);
            if (reference.info.declaration) |declaration|
                try self.putNodeId(&value, "declaration", declaration);
            try value.object.put(
                self.allocator,
                "isSlot",
                .{ .bool = std.mem.eql(u8, reference.info.suffix, "slot") },
            );
            try value.object.put(
                self.allocator,
                "isOffset",
                .{ .bool = std.mem.eql(u8, reference.info.suffix, "offset") },
            );
            if (reference.info.suffix.len != 0)
                try putString(self.allocator, &value, "suffix", reference.info.suffix);
            const value_size: i64 = if (reference.info.value_size == std.math.maxInt(usize))
                -1
            else
                std.math.cast(i64, reference.info.value_size) orelse return error.InvalidAst;
            try value.object.put(self.allocator, "valueSize", .{ .integer = value_size });
            try values.append(value);
        }
        return .{ .array = values };
    }

    fn baseNode(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        kind: []const u8,
    ) ExportError!Json {
        var result: Json = .{ .object = .empty };
        try result.object.put(self.allocator, "id", .{ .integer = try self.nodeId(node) });
        try self.putLocation(&result, "src", node.location);
        try putString(self.allocator, &result, "nodeType", kind);
        return result;
    }

    fn putNodeList(
        self: *ASTJsonExporter,
        object: *Json,
        name: []const u8,
        nodes: AST.NodeList,
        context: Context,
    ) ExportError!void {
        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (nodes) |node| try values.append(try self.nodeToJson(node, context));
        try object.object.put(self.allocator, name, .{ .array = values });
    }

    fn putOptionalNodeList(
        self: *ASTJsonExporter,
        object: *Json,
        name: []const u8,
        nodes: AST.OptionalNodeList,
    ) ExportError!void {
        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (nodes) |node| {
            if (node) |present|
                try values.append(try self.nodeToJson(present, .{}))
            else
                try values.append(.null);
        }
        try object.object.put(self.allocator, name, .{ .array = values });
    }

    fn putStrings(
        self: *ASTJsonExporter,
        object: *Json,
        name: []const u8,
        strings: AST.StringList,
    ) ExportError!void {
        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (strings) |string| try values.append(.{ .string = string });
        try object.object.put(self.allocator, name, .{ .array = values });
    }

    fn putLocations(
        self: *ASTJsonExporter,
        object: *Json,
        name: []const u8,
        locations: []const SourceLocation,
    ) ExportError!void {
        var values = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (locations) |location| {
            const rendered = try self.locationString(location);
            try values.append(.{ .string = rendered });
        }
        try object.object.put(self.allocator, name, .{ .array = values });
    }

    fn putLocation(
        self: *ASTJsonExporter,
        object: *Json,
        name: []const u8,
        location: SourceLocation,
    ) ExportError!void {
        const rendered = try self.locationString(location);
        try object.object.put(self.allocator, name, .{ .string = rendered });
    }

    fn locationString(self: *ASTJsonExporter, location: SourceLocation) ExportError![]const u8 {
        const length: i64 = if (location.start >= 0 and location.end >= 0)
            @as(i64, location.end) - @as(i64, location.start)
        else
            -1;
        var source_index: i64 = -1;
        if (location.source_name) |source_name| {
            for (self.source_indices) |entry| {
                if (std.mem.eql(u8, source_name, entry.name)) {
                    source_index = std.math.cast(i64, entry.index) orelse return error.InvalidAst;
                    break;
                }
            }
        }
        return std.fmt.allocPrint(
            self.allocator,
            "{d}:{d}:{d}",
            .{ location.start, length, source_index },
        );
    }

    fn sourceIndex(self: *const ASTJsonExporter, location: SourceLocation) ?usize {
        const source_name = location.source_name orelse return null;
        for (self.source_indices) |entry|
            if (std.mem.eql(u8, source_name, entry.name)) return entry.index;
        return null;
    }

    fn putExpressionAttributes(
        self: *ASTJsonExporter,
        node: *const AST.Node,
        result: *Json,
    ) ExportError!void {
        const annotation = expressionAnnotation(node);
        try result.object.put(
            self.allocator,
            "typeDescriptions",
            try self.typePointerToJson(
                if (annotation) |value| value.type_ref else null,
                false,
            ),
        );
        try self.putArgumentTypes(annotation, result);
        if (annotation) |value| {
            if (value.is_lvalue.value) |is_lvalue|
                try result.object.put(self.allocator, "isLValue", .{ .bool = is_lvalue });
            if (value.is_pure.value) |is_pure|
                try result.object.put(self.allocator, "isPure", .{ .bool = is_pure });
            if (value.is_constant.value) |is_constant|
                try result.object.put(self.allocator, "isConstant", .{ .bool = is_constant });
            if (self.analysis_complete)
                try result.object.put(
                    self.allocator,
                    "lValueRequested",
                    .{ .bool = value.will_be_written_to },
                );
        } else if (self.analysis_complete) {
            try result.object.put(self.allocator, "lValueRequested", .{ .bool = false });
        }
    }

    fn nodeId(self: *const ASTJsonExporter, node: *const AST.Node) ExportError!i64 {
        return self.compatibility_ids.id(node) orelse error.InvalidAst;
    }

    fn putNodeId(
        self: *const ASTJsonExporter,
        object: *Json,
        name: []const u8,
        node: *const AST.Node,
    ) ExportError!void {
        try object.object.put(
            self.allocator,
            name,
            .{ .integer = try self.nodeId(node) },
        );
    }
};

fn expressionAnnotation(node: *const AST.Node) ?*const ASTAnnotations.ExpressionAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .expression => |*value| value,
        .identifier => |*value| &value.expression,
        .member_access => |*value| &value.expression,
        .operation => |*value| &value.expression,
        .binary_operation => |*value| &value.operation.expression,
        .function_call => |*value| &value.expression,
        else => null,
    };
}

fn identifierAnnotation(node: *const AST.Node) ?*const ASTAnnotations.IdentifierAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .identifier => |*value| value,
        else => null,
    };
}

fn identifierPathAnnotation(node: *const AST.Node) ?*const ASTAnnotations.IdentifierPathAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .identifier_path => |*value| value,
        else => null,
    };
}

fn memberAccessAnnotation(node: *const AST.Node) ?*const ASTAnnotations.MemberAccessAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .member_access => |*value| value,
        else => null,
    };
}

fn operationAnnotation(node: *const AST.Node) ?*const ASTAnnotations.OperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .operation => |*value| value,
        .binary_operation => |*value| &value.operation,
        else => null,
    };
}

fn binaryOperationAnnotation(node: *const AST.Node) ?*const ASTAnnotations.BinaryOperationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .binary_operation => |*value| value,
        else => null,
    };
}

fn functionCallAnnotation(node: *const AST.Node) ?*const ASTAnnotations.FunctionCallAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .function_call => |*value| value,
        else => null,
    };
}

fn variableAnnotation(node: *const AST.Node) ?*const ASTAnnotations.VariableDeclarationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .variable_declaration => |*value| value,
        else => null,
    };
}

fn callableAnnotation(node: *const AST.Node) ?*const ASTAnnotations.CallableDeclarationAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .documented_callable => |*value| &value.callable,
        .callable_declaration => |*value| value,
        else => null,
    };
}

fn typeNameType(node: *const AST.Node) ?*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .type_name => |value| value.type_ref,
        else => null,
    };
}

fn forStatementAnnotation(node: *const AST.Node) ?*const ASTAnnotations.ForStatementAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .for_statement => |*value| value,
        else => null,
    };
}

fn returnAnnotation(node: *const AST.Node) ?*const ASTAnnotations.ReturnAnnotation {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    return switch (annotation.*) {
        .return_statement => |*value| value,
        else => null,
    };
}

fn nodeContract(node: *const AST.Node) ?*const AST.Node {
    const annotation = ASTAnnotations.annotationConst(node) orelse return null;
    const scopable = ASTAnnotations.scopableConst(annotation) orelse return null;
    return scopable.contract;
}

fn functionCallKind(kind: ASTAnnotations.FunctionCallKind) []const u8 {
    return switch (kind) {
        .FunctionCall => "functionCall",
        .TypeConversion => "typeConversion",
        .StructConstructorCall => "structConstructorCall",
    };
}

fn nodeType(node: *const AST.Node) []const u8 {
    return switch (node.payload) {
        .source_unit => "SourceUnit",
        .pragma_directive => "PragmaDirective",
        .import_directive => "ImportDirective",
        .structured_documentation => "StructuredDocumentation",
        .contract_definition => "ContractDefinition",
        .storage_layout_specifier => "StorageLayoutSpecifier",
        .identifier_path => "IdentifierPath",
        .inheritance_specifier => "InheritanceSpecifier",
        .using_for_directive => "UsingForDirective",
        .struct_definition => "StructDefinition",
        .enum_definition => "EnumDefinition",
        .enum_value => "EnumValue",
        .user_defined_value_type_definition => "UserDefinedValueTypeDefinition",
        .parameter_list => "ParameterList",
        .override_specifier => "OverrideSpecifier",
        .function_definition => "FunctionDefinition",
        .variable_declaration => "VariableDeclaration",
        .modifier_definition => "ModifierDefinition",
        .modifier_invocation => "ModifierInvocation",
        .event_definition => "EventDefinition",
        .error_definition => "ErrorDefinition",
        .magic_variable_declaration => "VariableDeclaration",
        .elementary_type_name => "ElementaryTypeName",
        .user_defined_type_name => "UserDefinedTypeName",
        .function_type_name => "FunctionTypeName",
        .mapping => "Mapping",
        .array_type_name => "ArrayTypeName",
        .inline_assembly => "InlineAssembly",
        .block => |value| if (value.unchecked) "UncheckedBlock" else "Block",
        .placeholder_statement => "PlaceholderStatement",
        .if_statement => "IfStatement",
        .try_catch_clause => "TryCatchClause",
        .try_statement => "TryStatement",
        .while_statement => |value| if (value.is_do_while) "DoWhileStatement" else "WhileStatement",
        .for_statement => "ForStatement",
        .continue_statement => "Continue",
        .break_statement => "Break",
        .return_statement => "Return",
        .throw_statement => "Throw",
        .revert_statement => "RevertStatement",
        .emit_statement => "EmitStatement",
        .variable_declaration_statement => "VariableDeclarationStatement",
        .expression_statement => "ExpressionStatement",
        .conditional => "Conditional",
        .assignment => "Assignment",
        .tuple_expression => "TupleExpression",
        .unary_operation => "UnaryOperation",
        .binary_operation => "BinaryOperation",
        .function_call => "FunctionCall",
        .function_call_options => "FunctionCallOptions",
        .new_expression => "NewExpression",
        .member_access => "MemberAccess",
        .index_access => "IndexAccess",
        .index_range_access => "IndexRangeAccess",
        .identifier => "Identifier",
        .elementary_type_name_expression => "ElementaryTypeNameExpression",
        .literal => "Literal",
        .type_class_definition => "TypeClassDefinition",
        .type_class_instantiation => "TypeClassInstantiation",
        .type_definition => "TypeDefinition",
        .type_class_name => "TypeClassName",
        .builtin => "Builtin",
        .for_all_quantifier => "ForAllQuantifier",
    };
}

fn statementDocumentation(node: *const AST.Node) ?[]const u8 {
    return switch (node.payload) {
        .inline_assembly => |value| value.statement.documentation,
        .block => |value| value.statement.documentation,
        .placeholder_statement => |value| value.statement.documentation,
        .if_statement => |value| value.statement.documentation,
        .try_statement => |value| value.statement.documentation,
        .while_statement => |value| value.statement.documentation,
        .for_statement => |value| value.statement.documentation,
        .continue_statement => |value| value.statement.documentation,
        .break_statement => |value| value.statement.documentation,
        .return_statement => |value| value.statement.documentation,
        .throw_statement => |value| value.statement.documentation,
        .revert_statement => |value| value.statement.documentation,
        .emit_statement => |value| value.statement.documentation,
        .variable_declaration_statement => |value| value.statement.documentation,
        .expression_statement => |value| value.statement.documentation,
        else => null,
    };
}

fn literalKind(token: AST.Token) ?[]const u8 {
    return switch (token) {
        .Number => "number",
        .StringLiteral => "string",
        .UnicodeStringLiteral => "unicodeString",
        .HexStringLiteral => "hexString",
        .TrueLiteral, .FalseLiteral => "bool",
        else => null,
    };
}

fn joinPath(allocator: std.mem.Allocator, parts: AST.StringList) std.mem.Allocator.Error![]u8 {
    var length: usize = if (parts.len == 0) 0 else parts.len - 1;
    for (parts) |part| length += part.len;
    const result = try allocator.alloc(u8, length);
    var offset: usize = 0;
    for (parts, 0..) |part, index| {
        if (index != 0) {
            result[offset] = '.';
            offset += 1;
        }
        @memcpy(result[offset..][0..part.len], part);
        offset += part.len;
    }
    return result;
}

fn hexAlloc(allocator: std.mem.Allocator, input: []const u8) std.mem.Allocator.Error![]u8 {
    const digits = "0123456789abcdef";
    const output = try allocator.alloc(u8, input.len * 2);
    for (input, 0..) |byte, index| {
        output[index * 2] = digits[byte >> 4];
        output[index * 2 + 1] = digits[byte & 0x0f];
    }
    return output;
}

fn putString(
    allocator: std.mem.Allocator,
    object: *Json,
    name: []const u8,
    value: []const u8,
) std.mem.Allocator.Error!void {
    try object.object.put(allocator, name, .{ .string = value });
}

fn emptyArray(allocator: std.mem.Allocator) Json {
    return .{ .array = std.json.Array.init(allocator) };
}

test "AST JSON uses projected compatibility IDs" {
    const source_id = CompatibilityIds.SourceId.init(17);
    var tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        source_id,
        "/// text",
        "input.sol",
    );
    defer tree.deinit();
    tree.next_node_id = 40;
    const node = try tree.createNode(.{}, .{
        .structured_documentation = .{ .text = "text" },
    });

    var projection = try CompatibilityIds.CompatibilityIdProjection.initAlloc(
        std.testing.allocator,
        &.{.{ .source = source_id, .node_count = 1 }},
    );
    defer projection.deinit();

    var arena_state = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena_state.deinit();
    var exporter = ASTJsonExporter.init(
        arena_state.allocator(),
        &.{},
        null,
        .init(&projection),
    );
    const json = try exporter.toJson(node);
    try std.testing.expectEqual(@as(i64, 41), node.id);
    try std.testing.expectEqual(@as(i64, 1), json.object.get("id").?.integer);
}
