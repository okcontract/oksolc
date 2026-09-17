// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared Solidity-to-Yul IR behavior translated from
//! `libsolidity/codegen/ir/Common.cpp`.

const std = @import("std");
const AST = @import("../../ast/ast.zig");
const ASTAnnotations = @import("../../ast/ast_annotations.zig");
const CompatibilityIdResolver = @import("../../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../../ast/types.zig");
const TypeBehavior = @import("../../ast/types.zig");
const AsmPrinter = @import("../../../libyul/asm_printer.zig");
const SourceLocation = @import("../../../liblangutil/source_location.zig").SourceLocation;
const CompatibilityIds = @import("../../../incremental/compatibility_ids.zig");

pub const CommonError = TypeBehavior.QueryError || AsmPrinter.PrintError || error{
    InvalidAst,
};

pub fn yulArityFromType(function_type: Types.FunctionType) TypeBehavior.QueryError!YulArity {
    var input_size: usize = 0;
    for (function_type.parameter_types) |parameter| {
        input_size = std.math.add(
            usize,
            input_size,
            try TypeBehavior.sizeOnStack(parameter),
        ) catch return error.Overflow;
    }
    var output_size: usize = 0;
    for (function_type.return_parameter_types) |parameter| {
        output_size = std.math.add(
            usize,
            output_size,
            try TypeBehavior.sizeOnStack(parameter),
        ) catch return error.Overflow;
    }
    return .{ .in = input_size, .out = output_size };
}

pub fn externalFunctionABIWrapperAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    declaration: *const AST.Node,
) CommonError![]u8 {
    if (declaration.nodeKind() == .function_definition and
        declaration.payload.function_definition.kind == .Constructor)
        return error.InvalidAst;
    const name = (declaration.declarationConst() orelse return error.InvalidAst).name;
    return std.fmt.allocPrint(
        allocator,
        "external_fun_{s}_{d}",
        .{ name, try compatibilityId(compatibility_ids, declaration) },
    );
}

pub fn functionAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    function: *const AST.Node,
) CommonError![]u8 {
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    const definition = function.payload.function_definition;
    if (definition.kind == .Constructor) {
        const annotation = ASTAnnotations.annotationConst(function) orelse
            return error.InvalidAst;
        const scope = ASTAnnotations.scopableConst(annotation) orelse
            return error.InvalidAst;
        return constructorAlloc(
            allocator,
            compatibility_ids,
            scope.contract orelse return error.InvalidAst,
        );
    }
    return std.fmt.allocPrint(
        allocator,
        "fun_{s}_{d}",
        .{ definition.callable.declaration.name, try compatibilityId(compatibility_ids, function) },
    );
}

pub fn getterFunctionAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    variable: *const AST.Node,
) CommonError![]u8 {
    if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
    return std.fmt.allocPrint(
        allocator,
        "getter_fun_{s}_{d}",
        .{
            variable.payload.variable_declaration.declaration.name,
            try compatibilityId(compatibility_ids, variable),
        },
    );
}

pub fn modifierInvocationAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    invocation: *const AST.Node,
) CommonError![]u8 {
    if (invocation.nodeKind() != .modifier_invocation) return error.InvalidAst;
    const name_node = invocation.payload.modifier_invocation.modifier_name;
    const modifier_name = switch (name_node.payload) {
        .identifier_path => |path| if (path.path.len == 0)
            return error.InvalidAst
        else
            path.path[path.path.len - 1],
        .identifier => |identifier| identifier.name,
        else => return error.InvalidAst,
    };
    if (modifier_name.len == 0) return error.InvalidAst;
    return std.fmt.allocPrint(
        allocator,
        "modifier_{s}_{d}",
        .{ modifier_name, try compatibilityId(compatibility_ids, invocation) },
    );
}

pub fn functionWithModifierInnerAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    function: *const AST.Node,
) CommonError![]u8 {
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    return std.fmt.allocPrint(
        allocator,
        "fun_{s}_{d}_inner",
        .{
            function.payload.function_definition.callable.declaration.name,
            try compatibilityId(compatibility_ids, function),
        },
    );
}

pub fn creationObjectAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const AST.Node,
) CommonError![]u8 {
    const data = try contractData(contract);
    return std.fmt.allocPrint(
        allocator,
        "{s}_{d}",
        .{ data.declaration.name, try compatibilityId(compatibility_ids, contract) },
    );
}

pub fn deployedObjectAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const AST.Node,
) CommonError![]u8 {
    const data = try contractData(contract);
    return std.fmt.allocPrint(
        allocator,
        "{s}_{d}_deployed",
        .{ data.declaration.name, try compatibilityId(compatibility_ids, contract) },
    );
}

pub fn internalDispatchAlloc(
    allocator: std.mem.Allocator,
    arity: YulArity,
) std.mem.Allocator.Error![]u8 {
    return std.fmt.allocPrint(
        allocator,
        "dispatch_internal_in_{d}_out_{d}",
        .{ arity.in, arity.out },
    );
}

pub fn constructorAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const AST.Node,
) CommonError![]u8 {
    const data = try contractData(contract);
    return std.fmt.allocPrint(
        allocator,
        "constructor_{s}_{d}",
        .{ data.declaration.name, try compatibilityId(compatibility_ids, contract) },
    );
}

pub fn libraryAddressImmutable() []const u8 {
    return "library_deploy_address";
}

pub fn constantValueFunctionAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    variable: *const AST.Node,
) CommonError![]u8 {
    if (variable.nodeKind() != .variable_declaration or
        variable.payload.variable_declaration.mutability != .Constant)
        return error.InvalidAst;
    return std.fmt.allocPrint(
        allocator,
        "constant_{s}_{d}",
        .{
            variable.payload.variable_declaration.declaration.name,
            try compatibilityId(compatibility_ids, variable),
        },
    );
}

pub fn localVariableDeclarationAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    declaration: *const AST.Node,
) CommonError![]u8 {
    if (declaration.nodeKind() != .variable_declaration) return error.InvalidAst;
    return std.fmt.allocPrint(
        allocator,
        "var_{s}_{d}",
        .{
            declaration.payload.variable_declaration.declaration.name,
            try compatibilityId(compatibility_ids, declaration),
        },
    );
}

pub fn localVariableExpressionAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    expression: *const AST.Node,
) CommonError![]u8 {
    if (!expression.isExpression()) return error.InvalidAst;
    return std.fmt.allocPrint(
        allocator,
        "expr_{d}",
        .{try compatibilityId(compatibility_ids, expression)},
    );
}

pub fn trySuccessConditionVariableAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    expression: *const AST.Node,
) CommonError![]u8 {
    const annotation = ASTAnnotations.annotationConst(expression) orelse
        return error.InvalidAst;
    switch (annotation.*) {
        .function_call => |call| if (!call.try_call) return error.InvalidAst,
        else => return error.InvalidAst,
    }
    return std.fmt.allocPrint(
        allocator,
        "trySuccessCondition_{d}",
        .{try compatibilityId(compatibility_ids, expression)},
    );
}

pub fn tupleComponentAlloc(
    allocator: std.mem.Allocator,
    index: usize,
) std.mem.Allocator.Error![]u8 {
    return std.fmt.allocPrint(allocator, "component_{d}", .{index + 1});
}

pub fn zeroValueAlloc(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    type_ref: *const Types.Type,
    variable_name: []const u8,
) CommonError![]u8 {
    const identifier = try TypeBehavior.compatibilityIdentifierAlloc(
        allocator,
        compatibility_ids,
        type_ref,
    );
    defer allocator.free(identifier);
    return std.fmt.allocPrint(allocator, "zero_{s}{s}", .{ identifier, variable_name });
}

pub fn dispenseLocationCommentAlloc(
    allocator: std.mem.Allocator,
    location: SourceLocation,
    context: LocationCommentContext,
) CommonError![]u8 {
    const source_name = location.source_name orelse return error.InvalidAst;
    try context.markSourceUsed(source_name);
    const debug_info = try AsmPrinter.formatSourceLocation(
        allocator,
        location,
        context.source_index_to_name,
        context.debug_info_selection,
        context.solidity_source_provider,
    );
    defer allocator.free(debug_info);
    if (debug_info.len == 0) return allocator.alloc(u8, 0);
    return std.fmt.allocPrint(allocator, "/// {s}", .{debug_info});
}

pub fn dispenseNodeLocationCommentAlloc(
    allocator: std.mem.Allocator,
    node: *const AST.Node,
    context: LocationCommentContext,
) CommonError![]u8 {
    return dispenseLocationCommentAlloc(allocator, node.location, context);
}

fn compatibilityId(
    resolver: CompatibilityIdResolver,
    node: *const AST.Node,
) CommonError!i64 {
    return resolver.id(node) orelse error.InvalidAst;
}

fn contractData(contract: *const AST.Node) CommonError!*const AST.ContractDefinition {
    if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
    return &contract.payload.contract_definition;
}

test "IR names retain stable Solidity declaration IDs" {
    const parameters = AST.Node{
        .id = 1,
        .location = .{},
        .payload = .{ .parameter_list = .{} },
    };
    const function = AST.Node{
        .id = 42,
        .location = .{},
        .payload = .{ .function_definition = .{
            .callable = .{
                .declaration = .{ .name = "f" },
                .parameters = @constCast(&parameters),
            },
        } },
    };
    const contract = AST.Node{
        .id = 7,
        .location = .{},
        .payload = .{ .contract_definition = .{
            .declaration = .{ .name = "C" },
        } },
    };

    const compatibility_ids = CompatibilityIdResolver.legacyNodeIds();
    const function_name = try functionAlloc(
        std.testing.allocator,
        compatibility_ids,
        &function,
    );
    defer std.testing.allocator.free(function_name);
    try std.testing.expectEqualStrings("fun_f_42", function_name);
    const external_name = try externalFunctionABIWrapperAlloc(
        std.testing.allocator,
        compatibility_ids,
        &function,
    );
    defer std.testing.allocator.free(external_name);
    try std.testing.expectEqualStrings("external_fun_f_42", external_name);
    const deployed_name = try deployedObjectAlloc(
        std.testing.allocator,
        compatibility_ids,
        &contract,
    );
    defer std.testing.allocator.free(deployed_name);
    try std.testing.expectEqualStrings("C_7_deployed", deployed_name);
    const dispatch = try internalDispatchAlloc(std.testing.allocator, .{ .in = 3, .out = 2 });
    defer std.testing.allocator.free(dispatch);
    try std.testing.expectEqualStrings("dispatch_internal_in_3_out_2", dispatch);
}

test "IR names use the revision compatibility projection" {
    const source_id = CompatibilityIds.SourceId.init(9);
    var tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        source_id,
        "contract C {}",
        "C.sol",
    );
    defer tree.deinit();
    tree.next_node_id = 100;
    const contract = try tree.createNode(.{}, .{ .contract_definition = .{
        .declaration = .{ .name = "C" },
    } });
    var projection = try CompatibilityIds.CompatibilityIdProjection.initAlloc(
        std.testing.allocator,
        &.{.{ .source = source_id, .node_count = 1 }},
    );
    defer projection.deinit();

    const deployed = try deployedObjectAlloc(
        std.testing.allocator,
        .init(&projection),
        contract,
    );
    defer std.testing.allocator.free(deployed);
    try std.testing.expectEqual(@as(i64, 101), contract.id);
    try std.testing.expectEqualStrings("C_1_deployed", deployed);
}

test "Yul arity recursively counts Solidity stack layouts" {
    const uint_type = Types.Type{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    const dynamic_calldata = Types.Type{ .payload = .{ .Array = .{
        .reference = .{ .location = .CallData },
        .base_type = &uint_type,
    } } };
    const arity = try yulArityFromType(.{
        .parameter_types = &.{ &dynamic_calldata, &uint_type },
        .return_parameter_types = &.{&dynamic_calldata},
    });
    try std.testing.expect(arity.eql(.{ .in = 3, .out = 2 }));
}

test "location comments mark their source before rendering" {
    const Marker = struct {
        used: bool = false,

        fn mark(raw: *anyopaque, name: []const u8) !void {
            const self: *@This() = @ptrCast(@alignCast(raw));
            if (!std.mem.eql(u8, name, "C.sol")) return error.InvalidAst;
            self.used = true;
        }
    };
    var marker: Marker = .{};
    const rendered = try dispenseLocationCommentAlloc(
        std.testing.allocator,
        .{ .start = 2, .end = 5, .source_name = "C.sol" },
        .{
            .marker_context = &marker,
            .mark_source_used_fn = Marker.mark,
            .source_index_to_name = &.{.{ .index = 4, .name = "C.sol" }},
            .debug_info_selection = .{ .location = true },
        },
    );
    defer std.testing.allocator.free(rendered);
    try std.testing.expect(marker.used);
    try std.testing.expectEqualStrings("/// @src 4:2:5", rendered);
}

const CharStreamProvider = @import("../../../liblangutil/char_stream_provider.zig").CharStreamProvider;

const DebugInfoSelection = @import("../../../liblangutil/debug_info_selection.zig").DebugInfoSelection;

/// Number of input and output Yul stack words in a generated function.
pub const YulArity = struct {
    in: usize,
    out: usize,

    pub fn eql(self: YulArity, other: YulArity) bool {
        return self.in == other.in and self.out == other.out;
    }

    pub fn lessThan(_: void, left: YulArity, right: YulArity) bool {
        return left.in < right.in or (left.in == right.in and left.out < right.out);
    }
};

/// Narrow manual interface used by location-comment generation. It keeps the
/// shared helper independent of the concrete IR generation context while
/// retaining upstream's source-use side effect.
pub const LocationCommentContext = struct {
    marker_context: *anyopaque,
    mark_source_used_fn: *const fn (
        *anyopaque,
        []const u8,
    ) (std.mem.Allocator.Error || error{InvalidAst})!void,
    source_index_to_name: []const AsmPrinter.SourceIndexName,
    debug_info_selection: DebugInfoSelection,
    solidity_source_provider: ?CharStreamProvider = null,

    pub fn markSourceUsed(self: LocationCommentContext, name: []const u8) !void {
        try self.mark_source_used_fn(self.marker_context, name);
    }
};
