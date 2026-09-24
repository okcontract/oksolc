// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Stateful Solidity-to-Yul generation context translated from
//! `IRGenerationContext.cpp`.

const std = @import("std");
const AST = @import("../../ast/ast.zig");
const ASTAnnotations = @import("../../ast/ast_annotations.zig");
const CompatibilityIdResolver = @import("../../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const Types = @import("../../ast/types.zig");
const TypeBehavior = @import("../../ast/types.zig");
const TypeProviderModule = @import("../../ast/type_provider.zig");
const EVMVersion = @import("../../../liblangutil/evm_version.zig").EVMVersion;
const CharStreamProvider = @import("../../../liblangutil/char_stream_provider.zig").CharStreamProvider;
const DebugInfoSelection = @import("../../../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const AsmPrinter = @import("../../../libyul/asm_printer.zig");
const DebugSettings = @import("../../interface/debug_settings.zig");
const CollectorModule = @import("../multi_use_yul_function_collector.zig");
const ABIFunctionsModule = @import("../abi_functions.zig");
const YulUtilFunctionsModule = @import("../yul_util_functions.zig");
const Common = @import("common.zig");
const IRVariableModule = @import("ir_variable.zig");

pub const general_purpose_memory_start: usize = 128;

pub const ExecutionContext = enum(c_int) {
    Creation,
    Deployed,
};

pub const StorageLocation = struct {
    storage_offset: u256,
    byte_offset: u32,
    location: AST.VariableLocation,
};

pub const ContextError = TypeBehavior.QueryError || IRVariableModule.VariableError ||
    Common.CommonError || error{
    InvalidAst,
    FunctionQueueEmpty,
    MostDerivedContractNotSet,
    DuplicateLocalVariable,
    UnknownLocalVariable,
    InvalidImmutableVariable,
    DuplicateImmutableVariable,
    UnknownImmutableVariable,
    ReservedMemoryConsumed,
    InvalidReservedMemory,
    DuplicateInternalDispatchInitialization,
};

pub const DispatchQueue = std.ArrayList(*const AST.Node);

pub const InternalDispatchMap = struct {
    allocator: std.mem.Allocator,
    entries: std.AutoHashMapUnmanaged(Common.YulArity, DispatchQueue) = .empty,

    pub fn init(allocator: std.mem.Allocator) InternalDispatchMap {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *InternalDispatchMap) void {
        var iterator = self.entries.valueIterator();
        while (iterator.next()) |queue| queue.deinit(self.allocator);
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn empty(self: *const InternalDispatchMap) bool {
        return self.entries.count() == 0;
    }

    pub fn ensureArity(
        self: *InternalDispatchMap,
        arity: Common.YulArity,
    ) std.mem.Allocator.Error!*DispatchQueue {
        const result = try self.entries.getOrPut(self.allocator, arity);
        if (!result.found_existing) result.value_ptr.* = .empty;
        return result.value_ptr;
    }
};

pub const IRGenerationContext = struct {
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    evm_version: EVMVersion,
    execution_context: ExecutionContext,
    revert_strings: DebugSettings.RevertStrings,
    // Owned immutable inventory; used_source_names borrows its name buffers.
    source_index_to_name: []const AsmPrinter.SourceIndexName,
    debug_info_selection: DebugInfoSelection,
    solidity_source_provider: ?CharStreamProvider,
    used_source_names: std.StringHashMapUnmanaged(void) = .empty,
    most_derived_contract: ?*const AST.Node = null,
    local_variables: std.AutoHashMapUnmanaged(*const AST.Node, IRVariableModule.IRVariable) = .empty,
    immutable_variables: std.AutoHashMapUnmanaged(*const AST.Node, usize) = .empty,
    reserved_memory: ?usize = 0,
    state_variables: std.AutoHashMapUnmanaged(*const AST.Node, StorageLocation) = .empty,
    functions: CollectorModule.MultiUseYulFunctionCollector,
    variable_counter: usize = 0,
    arithmetic: AST.Arithmetic = .Checked,
    memory_unsafe_inline_assembly_seen: bool = false,
    function_generation_queue: DispatchQueue = .empty,
    internal_dispatch_map: InternalDispatchMap,
    sub_objects: std.ArrayList(*const AST.Node) = .empty,

    pub fn init(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
        evm_version: EVMVersion,
        execution_context: ExecutionContext,
        revert_strings: DebugSettings.RevertStrings,
        source_index_to_name: []const AsmPrinter.SourceIndexName,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
    ) std.mem.Allocator.Error!IRGenerationContext {
        const owned_sources = try allocator.alloc(
            AsmPrinter.SourceIndexName,
            source_index_to_name.len,
        );
        var initialized: usize = 0;
        errdefer {
            for (owned_sources[0..initialized]) |entry| allocator.free(entry.name);
            allocator.free(owned_sources);
        }
        for (source_index_to_name, owned_sources) |source, *target| {
            target.* = .{
                .index = source.index,
                .name = try allocator.dupe(u8, source.name),
            };
            initialized += 1;
        }
        return .{
            .allocator = allocator,
            .type_provider = type_provider,
            .compatibility_ids = compatibility_ids,
            .evm_version = evm_version,
            .execution_context = execution_context,
            .revert_strings = revert_strings,
            .source_index_to_name = owned_sources,
            .debug_info_selection = debug_info_selection,
            .solidity_source_provider = solidity_source_provider,
            .functions = CollectorModule.MultiUseYulFunctionCollector.init(allocator),
            .internal_dispatch_map = InternalDispatchMap.init(allocator),
        };
    }

    pub fn deinit(self: *IRGenerationContext) void {
        self.used_source_names.deinit(self.allocator);
        for (self.source_index_to_name) |entry| self.allocator.free(entry.name);
        self.allocator.free(self.source_index_to_name);
        self.resetLocalVariables();
        self.local_variables.deinit(self.allocator);
        self.immutable_variables.deinit(self.allocator);
        self.state_variables.deinit(self.allocator);
        self.functions.deinit();
        self.function_generation_queue.deinit(self.allocator);
        self.internal_dispatch_map.deinit();
        self.sub_objects.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn functionCollector(
        self: *IRGenerationContext,
    ) *CollectorModule.MultiUseYulFunctionCollector {
        return &self.functions;
    }

    pub fn executionContext(self: *const IRGenerationContext) ExecutionContext {
        return self.execution_context;
    }

    pub fn utils(self: *IRGenerationContext) YulUtilFunctionsModule.YulUtilFunctions {
        var result = YulUtilFunctionsModule.YulUtilFunctions.init(
            self.allocator,
            self.type_provider,
            self.compatibility_ids,
            self.evm_version,
            self.revert_strings,
            &self.functions,
        );
        result.storage_to_memory_abi_encoder = .{
            .context = self,
            .generate_fn = generateStorageToMemoryABIEncoder,
        };
        result.calldata_to_memory_abi_decoder = .{
            .context = self,
            .generate_fn = generateCalldataToMemoryABIDecoder,
        };
        return result;
    }

    pub fn abiFunctions(self: *IRGenerationContext) ABIFunctionsModule.ABIFunctions {
        return ABIFunctionsModule.ABIFunctions.init(
            self.allocator,
            self.type_provider,
            self.compatibility_ids,
            self.evm_version,
            self.revert_strings,
            &self.functions,
        );
    }

    pub fn enqueueFunctionForCodeGeneration(
        self: *IRGenerationContext,
        function: *const AST.Node,
    ) ContextError![]u8 {
        const name = try Common.functionAlloc(
            self.allocator,
            self.compatibility_ids,
            function,
        );
        errdefer self.allocator.free(name);
        if (!self.functions.contains(name))
            try self.function_generation_queue.append(self.allocator, function);
        return name;
    }

    pub fn dequeueFunctionForCodeGeneration(
        self: *IRGenerationContext,
    ) ContextError!*const AST.Node {
        if (self.function_generation_queue.items.len == 0)
            return error.FunctionQueueEmpty;
        return self.function_generation_queue.orderedRemove(0);
    }

    pub fn functionGenerationQueueEmpty(self: *const IRGenerationContext) bool {
        return self.function_generation_queue.items.len == 0;
    }

    pub fn setMostDerivedContract(
        self: *IRGenerationContext,
        contract: *const AST.Node,
    ) ContextError!void {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        self.most_derived_contract = contract;
    }

    pub fn mostDerivedContract(self: *const IRGenerationContext) ContextError!*const AST.Node {
        return self.most_derived_contract orelse error.MostDerivedContractNotSet;
    }

    pub fn addLocalVariable(
        self: *IRGenerationContext,
        declaration: *const AST.Node,
    ) ContextError!*const IRVariableModule.IRVariable {
        if (self.local_variables.contains(declaration))
            return error.DuplicateLocalVariable;
        var variable = try IRVariableModule.IRVariable.fromDeclaration(
            self.allocator,
            self.compatibility_ids,
            declaration,
        );
        errdefer variable.deinit();
        try self.local_variables.put(self.allocator, declaration, variable);
        return self.local_variables.getPtr(declaration).?;
    }

    pub fn isLocalVariable(
        self: *const IRGenerationContext,
        declaration: *const AST.Node,
    ) bool {
        return self.local_variables.contains(declaration);
    }

    pub fn localVariable(
        self: *const IRGenerationContext,
        declaration: *const AST.Node,
    ) ContextError!*const IRVariableModule.IRVariable {
        return self.local_variables.getPtr(declaration) orelse error.UnknownLocalVariable;
    }

    pub fn resetLocalVariables(self: *IRGenerationContext) void {
        var iterator = self.local_variables.valueIterator();
        while (iterator.next()) |variable| variable.deinit();
        self.local_variables.clearRetainingCapacity();
    }

    pub fn registerImmutableVariable(
        self: *IRGenerationContext,
        variable: *const AST.Node,
    ) ContextError!void {
        if (self.execution_context == .Deployed or
            variable.nodeKind() != .variable_declaration or
            variable.payload.variable_declaration.mutability != .Immutable)
            return error.InvalidImmutableVariable;
        if (self.immutable_variables.contains(variable))
            return error.DuplicateImmutableVariable;
        const type_ref = try variableType(variable);
        if (!TypeBehavior.isValueType(type_ref) or
            try TypeBehavior.sizeOnStack(type_ref) != 1)
            return error.InvalidImmutableVariable;
        const reserved = self.reserved_memory orelse return error.ReservedMemoryConsumed;
        const offset = std.math.add(
            usize,
            general_purpose_memory_start,
            reserved,
        ) catch return error.Overflow;
        try self.immutable_variables.put(self.allocator, variable, offset);
        self.reserved_memory = std.math.add(usize, reserved, 32) catch return error.Overflow;
    }

    pub fn immutableMemoryOffset(
        self: *const IRGenerationContext,
        variable: *const AST.Node,
    ) ContextError!usize {
        return self.immutable_variables.get(variable) orelse error.UnknownImmutableVariable;
    }

    pub fn immutableMemoryOffsetRelative(
        self: *const IRGenerationContext,
        variable: *const AST.Node,
    ) ContextError!usize {
        const absolute = try self.immutableMemoryOffset(variable);
        if (absolute < general_purpose_memory_start) return error.InvalidReservedMemory;
        return absolute - general_purpose_memory_start;
    }

    pub fn reservedMemorySize(self: *const IRGenerationContext) ContextError!usize {
        return self.reserved_memory orelse error.ReservedMemoryConsumed;
    }

    pub fn reservedMemory(self: *IRGenerationContext) ContextError!usize {
        const reserved = self.reserved_memory orelse return error.ReservedMemoryConsumed;
        const immutable_size = std.math.mul(
            usize,
            self.immutable_variables.count(),
            32,
        ) catch return error.Overflow;
        const valid = (self.execution_context == .Creation and reserved == immutable_size) or
            (self.execution_context == .Deployed and reserved == 0);
        if (!valid) return error.InvalidReservedMemory;
        self.reserved_memory = null;
        return reserved;
    }

    pub fn immutableRegistered(
        self: *const IRGenerationContext,
        variable: *const AST.Node,
    ) bool {
        return self.immutable_variables.contains(variable);
    }

    pub fn addStateVariable(
        self: *IRGenerationContext,
        variable: *const AST.Node,
        storage_offset: u256,
        byte_offset: u32,
        location: AST.VariableLocation,
    ) std.mem.Allocator.Error!void {
        try self.state_variables.put(self.allocator, variable, .{
            .storage_offset = storage_offset,
            .byte_offset = byte_offset,
            .location = location,
        });
    }

    pub fn isStateVariable(
        self: *const IRGenerationContext,
        variable: *const AST.Node,
    ) bool {
        return self.state_variables.contains(variable);
    }

    pub fn storageLocationOfStateVariable(
        self: *const IRGenerationContext,
        variable: *const AST.Node,
    ) ContextError!StorageLocation {
        return self.state_variables.get(variable) orelse error.InvalidAst;
    }

    pub fn newYulVariable(self: *IRGenerationContext) ContextError![]u8 {
        self.variable_counter = std.math.add(usize, self.variable_counter, 1) catch
            return error.Overflow;
        return std.fmt.allocPrint(self.allocator, "_{d}", .{self.variable_counter});
    }

    pub fn initializeInternalDispatch(
        self: *IRGenerationContext,
        incoming: *InternalDispatchMap,
    ) ContextError!void {
        if (!self.internal_dispatch_map.empty())
            return error.DuplicateInternalDispatchInitialization;
        var iterator = incoming.entries.valueIterator();
        while (iterator.next()) |queue| {
            for (queue.items) |function| {
                const name = try self.enqueueFunctionForCodeGeneration(function);
                self.allocator.free(name);
            }
        }
        self.internal_dispatch_map.deinit();
        self.internal_dispatch_map = incoming.*;
        incoming.* = InternalDispatchMap.init(self.allocator);
    }

    pub fn consumeInternalDispatchMap(
        self: *IRGenerationContext,
    ) InternalDispatchMap {
        const result = self.internal_dispatch_map;
        self.internal_dispatch_map = InternalDispatchMap.init(self.allocator);
        return result;
    }

    pub fn internalDispatchClean(self: *const IRGenerationContext) bool {
        return self.internal_dispatch_map.empty();
    }

    pub fn internalFunctionCalledThroughDispatch(
        self: *IRGenerationContext,
        arity: Common.YulArity,
    ) std.mem.Allocator.Error!void {
        _ = try self.internal_dispatch_map.ensureArity(arity);
    }

    pub fn addToInternalDispatch(
        self: *IRGenerationContext,
        function: *const AST.Node,
    ) ContextError!void {
        const arity = try functionArity(function);
        const queue = try self.internal_dispatch_map.ensureArity(arity);
        for (queue.items) |existing| if (existing == function) return;
        try queue.append(self.allocator, function);
        const name = try self.enqueueFunctionForCodeGeneration(function);
        self.allocator.free(name);
    }

    pub fn setArithmetic(self: *IRGenerationContext, arithmetic: AST.Arithmetic) void {
        self.arithmetic = arithmetic;
    }

    pub fn addSubObject(
        self: *IRGenerationContext,
        contract: *const AST.Node,
    ) ContextError!void {
        if (contract.nodeKind() != .contract_definition) return error.InvalidAst;
        for (self.sub_objects.items) |existing| if (existing == contract) return;
        try self.sub_objects.append(self.allocator, contract);
    }

    pub fn setMemoryUnsafeInlineAssemblySeen(self: *IRGenerationContext) void {
        self.memory_unsafe_inline_assembly_seen = true;
    }

    pub fn memoryUnsafeInlineAssemblySeen(self: *const IRGenerationContext) bool {
        return self.memory_unsafe_inline_assembly_seen;
    }

    pub fn markSourceUsed(
        self: *IRGenerationContext,
        name: []const u8,
    ) (std.mem.Allocator.Error || error{InvalidAst})!void {
        if (self.used_source_names.contains(name)) return;
        for (self.source_index_to_name) |entry| {
            // Borrow the context's stable owner, never the caller's buffer.
            if (std.mem.eql(u8, name, entry.name))
                return self.used_source_names.put(self.allocator, entry.name, {});
        }
        return error.InvalidAst;
    }

    pub fn sourceUsed(self: *const IRGenerationContext, name: []const u8) bool {
        return self.used_source_names.contains(name);
    }

    fn generateStorageToMemoryABIEncoder(
        raw: *anyopaque,
        from_type: *const Types.Type,
        to_type: *const Types.Type,
    ) YulUtilFunctionsModule.UtilError![]u8 {
        const self: *IRGenerationContext = @ptrCast(@alignCast(raw));
        var abi = self.abiFunctions();
        return abi.abiEncodeAndReturnUpdatedPosFunction(
            from_type,
            to_type,
            .{},
        ) catch |err| switch (err) {
            error.InvalidTypeList => return error.InvalidType,
            else => return @errorCast(err),
        };
    }

    fn generateCalldataToMemoryABIDecoder(
        raw: *anyopaque,
        to_type: *const Types.Type,
    ) YulUtilFunctionsModule.UtilError![]u8 {
        const self: *IRGenerationContext = @ptrCast(@alignCast(raw));
        var abi = self.abiFunctions();
        return switch (to_type.payload) {
            .Array => abi.abiDecodingFunctionArrayAvailableLength(to_type, false),
            .Struct => abi.abiDecodingFunctionStruct(to_type, false),
            else => error.InvalidType,
        } catch |err| switch (err) {
            error.InvalidTypeList => return error.InvalidType,
            else => return @errorCast(err),
        };
    }

    pub fn locationCommentContext(self: *IRGenerationContext) Common.LocationCommentContext {
        return .{
            .marker_context = self,
            .mark_source_used_fn = markSourceUsedErased,
            .source_index_to_name = self.source_index_to_name,
            .debug_info_selection = self.debug_info_selection,
            .solidity_source_provider = self.solidity_source_provider,
        };
    }

    fn markSourceUsedErased(
        raw: *anyopaque,
        name: []const u8,
    ) (std.mem.Allocator.Error || error{InvalidAst})!void {
        const self: *IRGenerationContext = @ptrCast(@alignCast(raw));
        return self.markSourceUsed(name);
    }
};

fn variableType(variable: *const AST.Node) ContextError!*const Types.Type {
    const annotation = ASTAnnotations.annotationConst(variable) orelse return error.InvalidAst;
    return switch (annotation.*) {
        .variable_declaration => |entry| entry.type_ref,
        else => null,
    } orelse error.InvalidAst;
}

fn functionArity(function: *const AST.Node) ContextError!Common.YulArity {
    if (function.nodeKind() != .function_definition) return error.InvalidAst;
    const definition = function.payload.function_definition;
    var arity: Common.YulArity = .{ .in = 0, .out = 0 };
    const parameters = definition.callable.parameters;
    if (parameters.nodeKind() != .parameter_list) return error.InvalidAst;
    for (parameters.payload.parameter_list.parameters) |parameter| {
        arity.in = std.math.add(
            usize,
            arity.in,
            try TypeBehavior.sizeOnStack(try variableType(parameter)),
        ) catch return error.Overflow;
    }
    if (definition.callable.return_parameters) |returns| {
        if (returns.nodeKind() != .parameter_list) return error.InvalidAst;
        for (returns.payload.parameter_list.parameters) |parameter| {
            arity.out = std.math.add(
                usize,
                arity.out,
                try TypeBehavior.sizeOnStack(try variableType(parameter)),
            ) catch return error.Overflow;
        }
    }
    return arity;
}

test "context owns locals, state locations, source use, and temporary names" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var tree = try AST.Tree.init(std.testing.allocator, "uint x;", "C.sol");
    defer tree.deinit();
    const variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "x" },
    } });
    const annotation = try ASTAnnotations.ensure(&tree, variable);
    const uint_type = try tree.allocator().create(Types.Type);
    uint_type.* = .{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    annotation.variable_declaration.type_ref = uint_type;

    var context = try IRGenerationContext.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Creation,
        .Default,
        &.{.{ .index = 0, .name = "C.sol" }},
        .{ .location = true },
        null,
    );
    defer context.deinit();
    const local = try context.addLocalVariable(variable);
    try std.testing.expectEqualStrings("var_x_1", local.base_name);
    try std.testing.expect(context.isLocalVariable(variable));
    try context.addStateVariable(variable, 9, 3, .Unspecified);
    try std.testing.expectEqual(
        StorageLocation{
            .storage_offset = 9,
            .byte_offset = 3,
            .location = .Unspecified,
        },
        try context.storageLocationOfStateVariable(variable),
    );
    const first = try context.newYulVariable();
    defer std.testing.allocator.free(first);
    const second = try context.newYulVariable();
    defer std.testing.allocator.free(second);
    try std.testing.expectEqualStrings("_1", first);
    try std.testing.expectEqualStrings("_2", second);

    const comment = try Common.dispenseLocationCommentAlloc(
        std.testing.allocator,
        .{ .start = 0, .end = 4, .source_name = "C.sol" },
        context.locationCommentContext(),
    );
    defer std.testing.allocator.free(comment);
    try std.testing.expectEqualStrings("/// @src 0:0:4", comment);
    try std.testing.expect(context.sourceUsed("C.sol"));
}

test "creation context reserves immutable memory once" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    var tree = try AST.Tree.init(std.testing.allocator, "uint immutable x;", "C.sol");
    defer tree.deinit();
    const variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "x" },
        .mutability = .Immutable,
    } });
    const annotation = try ASTAnnotations.ensure(&tree, variable);
    const uint_type = try tree.allocator().create(Types.Type);
    uint_type.* = .{ .payload = .{ .Integer = .{
        .bits = 256,
        .modifier = .Unsigned,
    } } };
    annotation.variable_declaration.type_ref = uint_type;

    var context = try IRGenerationContext.init(
        std.testing.allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        EVMVersion.current(),
        .Creation,
        .Default,
        &.{.{ .index = 0, .name = "C.sol" }},
        .{},
        null,
    );
    defer context.deinit();
    try context.registerImmutableVariable(variable);
    try std.testing.expectEqual(general_purpose_memory_start, try context.immutableMemoryOffset(variable));
    try std.testing.expectEqual(@as(usize, 0), try context.immutableMemoryOffsetRelative(variable));
    try std.testing.expectEqual(@as(usize, 32), try context.reservedMemorySize());
    try std.testing.expectEqual(@as(usize, 32), try context.reservedMemory());
    try std.testing.expectError(error.ReservedMemoryConsumed, context.reservedMemory());
}

test "IR source inventory survives caller buffers and rejects unknown names" {
    const allocator = std.testing.allocator;
    var type_provider = try TypeProviderModule.TypeProvider.init(allocator);
    defer type_provider.deinit();
    var source_name = "C.sol".*;
    var context = try IRGenerationContext.init(
        allocator,
        &type_provider,
        CompatibilityIdResolver.legacyNodeIds(),
        .current(),
        .Creation,
        .Default,
        &.{ .{ .index = 19, .name = &source_name }, .{ .index = 1000, .name = "D.sol" }, .{ .index = 0, .name = "" } },
        .{},
        null,
    );
    defer context.deinit();
    @memset(&source_name, '?');
    {
        const incoming = try allocator.dupe(u8, "C.sol");
        defer allocator.free(incoming);
        try context.markSourceUsed(incoming);
        @memset(incoming, '!');
    }
    try std.testing.expect(context.sourceUsed("C.sol"));
    try std.testing.expect(!context.sourceUsed("D.sol"));
    try std.testing.expectError(error.InvalidAst, context.markSourceUsed("unknown.sol"));
    try context.markSourceUsed("");
    try context.markSourceUsed("C.sol");
    try std.testing.expectEqual(@as(u32, 2), context.used_source_names.count());
    try std.testing.expectEqual(@as(usize, 19), context.source_index_to_name[0].index);
}

test "IR source inventory and map growth clean up every allocation failure" {
    var type_provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer type_provider.deinit();
    const Check = struct {
        fn run(allocator: std.mem.Allocator, provider: *TypeProviderModule.TypeProvider) !void {
            var context = try IRGenerationContext.init(
                allocator,
                provider,
                CompatibilityIdResolver.legacyNodeIds(),
                .current(),
                .Deployed,
                .Default,
                &.{ .{ .index = 0, .name = "a" }, .{ .index = 7, .name = "b" }, .{ .index = 12, .name = "c" }, .{ .index = 15, .name = "d" }, .{ .index = 100, .name = "e" }, .{ .index = 101, .name = "f" }, .{ .index = 300, .name = "g" }, .{ .index = 500, .name = "h" }, .{ .index = 900, .name = "i" } },
                .{},
                null,
            );
            defer context.deinit();
            for (context.source_index_to_name, 0..) |entry, index| {
                context.markSourceUsed(entry.name) catch |err| {
                    try std.testing.expectEqual(index, context.used_source_names.count());
                    for (context.source_index_to_name[0..index]) |previous|
                        try std.testing.expect(context.sourceUsed(previous.name));
                    return err;
                };
                try std.testing.expect(context.sourceUsed(entry.name));
            }
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Check.run, .{&type_provider});
}

test "IR source use borrows inventory keys without per-name allocation" {
    var provider = try TypeProviderModule.TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var counting = std.testing.FailingAllocator.init(std.testing.allocator, .{});
    const allocator = counting.allocator();
    var context = try IRGenerationContext.init(
        allocator,
        &provider,
        CompatibilityIdResolver.legacyNodeIds(),
        .current(),
        .Creation,
        .Default,
        &.{ .{ .index = 0, .name = "contracts/A.sol" }, .{ .index = 9, .name = "contracts/B.sol" }, .{ .index = 31, .name = "lib/C.sol" } },
        .{},
        null,
    );
    defer context.deinit();
    try context.used_source_names.ensureTotalCapacity(allocator, 3);
    counting.fail_index = counting.alloc_index;
    counting.resize_fail_index = counting.resize_index;
    for (context.source_index_to_name) |source| {
        try context.markSourceUsed(source.name);
        try context.markSourceUsed(source.name);
        try std.testing.expect(context.used_source_names.getKey(source.name).?.ptr == source.name.ptr);
    }
    try std.testing.expectError(error.InvalidAst, context.markSourceUsed("missing.sol"));
    try std.testing.expect(!counting.has_induced_failure);
}
