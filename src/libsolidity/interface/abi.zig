// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Contract ABI JSON generation translated from `ABI.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const ASTEnums = @import("../ast/ast_enums.zig");
const ASTImplementation = @import("../ast/ast.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const ContractLevelChecker = @import("../analysis/contract_level_checker.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const JSON = @import("../../libsolutil/json.zig");

pub const GenerateError = ContractLevelChecker.CheckError;
const Json = JSON.Json;

const ABIEntry = struct {
    value: Json,
    kind: []const u8,
    name: []const u8,

    fn lessThan(_: void, left: ABIEntry, right: ABIEntry) bool {
        const kind_order = std.mem.order(u8, left.kind, right.kind);
        if (kind_order != .eq) return kind_order == .lt;
        return std.mem.order(u8, left.name, right.name) == .lt;
    }
};

pub const ABI = struct {
    pub fn generate(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
        tree: *AST.Tree,
        contract: *AST.Node,
    ) GenerateError!Json {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        var entries: std.ArrayList(ABIEntry) = .empty;
        defer entries.deinit(allocator);
        try appendFunctions(allocator, type_provider, contract, &entries);
        try appendConstructor(allocator, tree, contract, &entries);
        try appendFallbackAndReceive(allocator, contract, &entries);
        try appendEvents(allocator, compatibility_ids, tree, contract, &entries);
        try appendErrors(allocator, compatibility_ids, tree, contract, &entries);
        std.sort.insertion(ABIEntry, entries.items, {}, ABIEntry.lessThan);

        var output = std.json.Array.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        try output.ensureTotalCapacity(entries.items.len);
        for (entries.items) |entry| try output.append(entry.value);
        return .{ .array = output };
    }
};

fn appendFunctions(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    contract: *AST.Node,
    entries: *std.ArrayList(ABIEntry),
) GenerateError!void {
    const library = contract.payload.contract_definition.contract_kind == .Library;
    const functions = try ASTImplementation.contractInterfaceFunctionsAlloc(
        type_provider,
        allocator,
        contract,
        true,
    );
    defer allocator.free(functions);
    for (functions) |function| {
        const member = @constCast(
            function.function_type.payload.Function.declaration orelse return error.InvalidAst,
        );
        if (member.nodeKind() == .function_definition) {
            if (library and try libraryFunctionExcluded(member)) continue;
            try entries.append(allocator, .{
                .value = try functionABI(allocator, member, library),
                .kind = "function",
                .name = member.payload.function_definition.callable.declaration.name,
            });
        } else if (member.nodeKind() == .variable_declaration) {
            try entries.append(allocator, .{
                .value = try getterABI(allocator, member, library),
                .kind = "function",
                .name = member.payload.variable_declaration.declaration.name,
            });
        } else {
            return error.InvalidAst;
        }
    }
}

fn functionABI(
    allocator: std.mem.Allocator,
    function: *const AST.Node,
    library: bool,
) GenerateError!Json {
    const value = function.payload.function_definition;
    var method: Json = .{ .object = .empty };
    try putString(allocator, &method, "type", "function");
    try putString(allocator, &method, "name", value.callable.declaration.name);
    try putString(
        allocator,
        &method,
        "stateMutability",
        ASTEnums.stateMutabilityToString(value.state_mutability),
    );
    try method.object.put(
        allocator,
        "inputs",
        try formatParameterList(allocator, value.callable.parameters, library),
    );
    try method.object.put(
        allocator,
        "outputs",
        if (value.callable.return_parameters) |parameters|
            try formatParameterList(allocator, parameters, library)
        else
            .{ .array = std.json.Array.init(allocator) },
    );
    return method;
}

fn getterABI(
    allocator: std.mem.Allocator,
    variable: *const AST.Node,
    library: bool,
) GenerateError!Json {
    var method: Json = .{ .object = .empty };
    try putString(allocator, &method, "type", "function");
    try putString(
        allocator,
        &method,
        "name",
        variable.payload.variable_declaration.declaration.name,
    );
    try putString(allocator, &method, "stateMutability", "view");

    var inputs = std.json.Array.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
    var current = try variableType(variable);
    var return_name: []const u8 = "";
    while (true) switch (current.payload) {
        .Mapping => |mapping| {
            try inputs.append(try formatType(
                allocator,
                mapping.key_name,
                mapping.key_type,
                library,
            ));
            current = mapping.value_type;
            return_name = mapping.value_name;
        },
        .Array => |array| {
            if (array.isByteArrayOrString()) break;
            try inputs.append(try formatSyntheticUint256(allocator, ""));
            current = array.base_type;
            return_name = "";
        },
        else => break,
    };
    try method.object.put(allocator, "inputs", .{ .array = inputs });

    var outputs = std.json.Array.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
    if (current.category() == .Struct) {
        const structure = current.payload.Struct;
        for (structure.declaration.payload.struct_definition.members) |member| {
            const member_type = try variableType(member);
            if (member_type.category() == .Mapping) continue;
            if (member_type.asArray()) |array|
                if (!array.isByteArrayOrString()) continue;
            try outputs.append(try formatType(
                allocator,
                member.payload.variable_declaration.declaration.name,
                member_type,
                library,
            ));
        }
    } else try outputs.append(try formatType(allocator, return_name, current, library));
    try method.object.put(allocator, "outputs", .{ .array = outputs });
    return method;
}

fn appendConstructor(
    allocator: std.mem.Allocator,
    _: *AST.Tree,
    contract: *const AST.Node,
    entries: *std.ArrayList(ABIEntry),
) GenerateError!void {
    if (contract.payload.contract_definition.abstract) return;
    for (contract.payload.contract_definition.sub_nodes) |member| {
        if (member.nodeKind() != .function_definition or
            member.payload.function_definition.kind != .Constructor) continue;
        const function = member.payload.function_definition;
        var method: Json = .{ .object = .empty };
        try putString(allocator, &method, "type", "constructor");
        try putString(
            allocator,
            &method,
            "stateMutability",
            ASTEnums.stateMutabilityToString(function.state_mutability),
        );
        try method.object.put(
            allocator,
            "inputs",
            try formatParameterList(allocator, function.callable.parameters, false),
        );
        try entries.append(allocator, .{
            .value = method,
            .kind = "constructor",
            .name = "",
        });
        return;
    }
}

fn appendFallbackAndReceive(
    allocator: std.mem.Allocator,
    contract: *const AST.Node,
    entries: *std.ArrayList(ABIEntry),
) GenerateError!void {
    const annotation = try contractAnnotation(contract);
    const hierarchy = if (annotation.linearized_base_contracts.len == 0)
        @as([]const *AST.Node, &.{@constCast(contract)})
    else
        annotation.linearized_base_contracts;
    const kinds = [_]AST.Token{ .Fallback, .Receive };
    for (kinds) |kind| {
        for (hierarchy) |base| {
            var found = false;
            for (base.payload.contract_definition.sub_nodes) |member| {
                if (member.nodeKind() != .function_definition or
                    member.payload.function_definition.kind != kind) continue;
                var method: Json = .{ .object = .empty };
                const kind_name = if (kind == .Fallback) "fallback" else "receive";
                try putString(allocator, &method, "type", kind_name);
                try putString(
                    allocator,
                    &method,
                    "stateMutability",
                    ASTEnums.stateMutabilityToString(
                        member.payload.function_definition.state_mutability,
                    ),
                );
                try entries.append(allocator, .{
                    .value = method,
                    .kind = kind_name,
                    .name = "",
                });
                found = true;
                break;
            }
            if (found) break;
        }
    }
}

fn appendEvents(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    _: *AST.Tree,
    contract: *const AST.Node,
    entries: *std.ArrayList(ABIEntry),
) GenerateError!void {
    var declarations: std.ArrayList(*const AST.Node) = .empty;
    defer declarations.deinit(allocator);
    try collectInterfaceDeclarations(
        allocator,
        compatibility_ids,
        contract,
        .event_definition,
        &declarations,
    );
    const annotation = try contractAnnotation(contract);
    if (annotation.creation_call_graph.value) |graph|
        for (graph.emitted_events.items) |event|
            try appendUniqueNode(allocator, compatibility_ids, &declarations, event);
    if (annotation.deployed_call_graph.value) |graph|
        for (graph.emitted_events.items) |event|
            try appendUniqueNode(allocator, compatibility_ids, &declarations, event);
    for (declarations.items) |event_node| {
        const event = event_node.payload.event_definition;
        var value: Json = .{ .object = .empty };
        try putString(allocator, &value, "type", "event");
        try putString(allocator, &value, "name", event.callable.declaration.name);
        try value.object.put(allocator, "anonymous", .{ .bool = event.anonymous });
        var parameters = std.json.Array.init(allocator);
        for (event.callable.parameters.payload.parameter_list.parameters) |parameter| {
            var formatted = try formatType(allocator, parameterName(parameter), try variableType(parameter), false);
            try formatted.object.put(
                allocator,
                "indexed",
                .{ .bool = parameter.payload.variable_declaration.indexed },
            );
            try parameters.append(formatted);
        }
        try value.object.put(allocator, "inputs", .{ .array = parameters });
        try entries.append(allocator, .{
            .value = value,
            .kind = "event",
            .name = event.callable.declaration.name,
        });
    }
}

fn appendErrors(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    _: *AST.Tree,
    contract: *const AST.Node,
    entries: *std.ArrayList(ABIEntry),
) GenerateError!void {
    var declarations: std.ArrayList(*const AST.Node) = .empty;
    defer declarations.deinit(allocator);
    try collectInterfaceDeclarations(
        allocator,
        compatibility_ids,
        contract,
        .error_definition,
        &declarations,
    );
    const annotation = try contractAnnotation(contract);
    if (annotation.creation_call_graph.value) |graph|
        for (graph.used_errors.items) |error_node|
            try appendUniqueNode(allocator, compatibility_ids, &declarations, error_node);
    if (annotation.deployed_call_graph.value) |graph|
        for (graph.used_errors.items) |error_node|
            try appendUniqueNode(allocator, compatibility_ids, &declarations, error_node);
    for (declarations.items) |error_node| {
        const definition = error_node.payload.error_definition;
        var value: Json = .{ .object = .empty };
        try putString(allocator, &value, "type", "error");
        try putString(allocator, &value, "name", definition.callable.declaration.name);
        try value.object.put(
            allocator,
            "inputs",
            try formatParameterList(allocator, definition.callable.parameters, false),
        );
        try entries.append(allocator, .{
            .value = value,
            .kind = "error",
            .name = definition.callable.declaration.name,
        });
    }
}

fn formatParameterList(
    allocator: std.mem.Allocator,
    parameters_node: *const AST.Node,
    library: bool,
) GenerateError!Json {
    if (parameters_node.nodeKind() != .parameter_list) return error.InvalidAst;
    var parameters = std.json.Array.init(allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
    for (parameters_node.payload.parameter_list.parameters) |parameter|
        try parameters.append(try formatType(
            allocator,
            parameterName(parameter),
            try variableType(parameter),
            library,
        ));
    return .{ .array = parameters };
}

fn formatType(
    allocator: std.mem.Allocator,
    name: []const u8,
    solidity_type: *const Types.Type,
    library: bool,
) GenerateError!Json {
    return formatTypeAtLocation(allocator, name, solidity_type, library, null);
}

fn formatTypeAtLocation(
    allocator: std.mem.Allocator,
    name: []const u8,
    solidity_type: *const Types.Type,
    library: bool,
    inherited_location: ?Types.DataLocation,
) GenerateError!Json {
    var result: Json = .{ .object = .empty };
    try putString(allocator, &result, "name", name);
    try result.object.put(
        allocator,
        "internalType",
        .{ .string = try TypeBehavior.toStringAlloc(allocator, solidity_type, true) },
    );
    try appendABIType(
        allocator,
        &result,
        solidity_type,
        library,
        inherited_location,
        0,
    );
    return result;
}

fn appendABIType(
    allocator: std.mem.Allocator,
    result: *Json,
    type_ref: *const Types.Type,
    library: bool,
    inherited_location: ?Types.DataLocation,
    depth: usize,
) GenerateError!void {
    if (depth >= 256) return error.InvalidAst;
    const effective_location: ?Types.DataLocation = if (type_ref.asReference()) |reference|
        inherited_location orelse reference.location
    else
        null;
    if (library and effective_location == .Storage) {
        const canonical = try TypeBehavior.canonicalNameAlloc(allocator, type_ref);
        const abi_name = try std.fmt.allocPrint(allocator, "{s} storage", .{canonical});
        try result.object.put(allocator, "type", .{ .string = abi_name });
        return;
    }
    switch (type_ref.payload) {
        .Contract, .Enum => if (library)
            try result.object.put(
                allocator,
                "type",
                .{ .string = try TypeBehavior.canonicalNameAlloc(allocator, type_ref) },
            )
        else
            try putString(allocator, result, "type", if (type_ref.category() == .Enum) "uint8" else "address"),
        .UserDefinedValueType => |value| try appendABIType(
            allocator,
            result,
            value.underlying_type orelse return error.InvalidAst,
            library,
            null,
            depth + 1,
        ),
        .Struct => |structure| {
            try putString(allocator, result, "type", "tuple");
            var components = std.json.Array.init(allocator);
            for (structure.declaration.payload.struct_definition.members) |member|
                try components.append(try formatTypeAtLocation(
                    allocator,
                    parameterName(member),
                    try variableType(member),
                    library,
                    effective_location,
                ));
            try result.object.put(allocator, "components", .{ .array = components });
        },
        .Array => |array| switch (array.kind) {
            .String => try putString(allocator, result, "type", "string"),
            .Bytes => try putString(allocator, result, "type", "bytes"),
            .Ordinary => {
                var subtype: Json = .{ .object = .empty };
                try appendABIType(
                    allocator,
                    &subtype,
                    array.base_type,
                    library,
                    effective_location,
                    depth + 1,
                );
                const base_name = subtype.object.get("type") orelse return error.InvalidAst;
                const suffix = if (array.length) |length|
                    try std.fmt.allocPrint(allocator, "[{d}]", .{length})
                else
                    try allocator.dupe(u8, "[]");
                const name = try std.fmt.allocPrint(allocator, "{s}{s}", .{ base_name.string, suffix });
                try result.object.put(allocator, "type", .{ .string = name });
                if (subtype.object.get("components")) |components|
                    try result.object.put(allocator, "components", components);
            },
        },
        .Address, .Integer, .Bool, .FixedPoint, .FixedBytes, .Function => try result.object.put(
            allocator,
            "type",
            .{ .string = try TypeBehavior.canonicalNameAlloc(allocator, type_ref) },
        ),
        else => return error.InvalidAst,
    }
}

fn formatSyntheticUint256(allocator: std.mem.Allocator, name: []const u8) !Json {
    var result: Json = .{ .object = .empty };
    try putString(allocator, &result, "name", name);
    try putString(allocator, &result, "internalType", "uint256");
    try putString(allocator, &result, "type", "uint256");
    return result;
}

fn collectInterfaceDeclarations(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const AST.Node,
    kind: AST.Kind,
    output: *std.ArrayList(*const AST.Node),
) GenerateError!void {
    const annotation = try contractAnnotation(contract);
    const hierarchy = if (annotation.linearized_base_contracts.len == 0)
        @as([]const *AST.Node, &.{@constCast(contract)})
    else
        annotation.linearized_base_contracts;
    for (hierarchy) |base|
        for (base.payload.contract_definition.sub_nodes) |member|
            if (member.nodeKind() == kind)
                try appendUniqueNode(allocator, compatibility_ids, output, member);
}

fn appendUniqueNode(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    output: *std.ArrayList(*const AST.Node),
    node: *const AST.Node,
) !void {
    for (output.items) |existing| if (existing == node) return;
    try output.append(allocator, node);
    std.sort.insertion(*const AST.Node, output.items, compatibility_ids, struct {
        fn lessThan(
            resolver: CompatibilityIdResolver,
            left: *const AST.Node,
            right: *const AST.Node,
        ) bool {
            return resolver.id(left).? < resolver.id(right).?;
        }
    }.lessThan);
}

fn libraryFunctionExcluded(function: *const AST.Node) GenerateError!bool {
    if (@intFromEnum(function.payload.function_definition.state_mutability) >
        @intFromEnum(AST.StateMutability.View)) return true;
    const callable = function.payload.function_definition.callable;
    for (callable.parameters.payload.parameter_list.parameters) |parameter|
        if (TypeBehavior.dataStoredIn(try variableType(parameter), .Storage)) return true;
    if (callable.return_parameters) |parameters|
        for (parameters.payload.parameter_list.parameters) |parameter|
            if (TypeBehavior.dataStoredIn(try variableType(parameter), .Storage)) return true;
    return false;
}

fn variableType(variable: *const AST.Node) GenerateError!*const Types.Type {
    if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
    const annotation = ASTAnnotations.annotationConst(variable) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |value| value.type_ref orelse error.InvalidAst,
        else => error.InvalidAst,
    };
}

fn contractAnnotation(
    contract: *const AST.Node,
) GenerateError!*const ASTAnnotations.ContractDefinitionAnnotation {
    const annotation = ASTAnnotations.annotationConst(contract) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidAst,
    };
}

fn parameterName(parameter: *const AST.Node) []const u8 {
    return parameter.payload.variable_declaration.declaration.name;
}

fn putString(
    allocator: std.mem.Allocator,
    object: *Json,
    key: []const u8,
    value: []const u8,
) !void {
    try object.object.put(allocator, key, .{ .string = try allocator.dupe(u8, value) });
}
