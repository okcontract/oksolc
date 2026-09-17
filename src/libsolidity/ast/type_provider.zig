// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Compilation-scoped type factory translated from `TypeProvider.cpp`.
//!
//! Unlike upstream's process-global singleton, each provider owns a separate
//! arena.  The arena state itself is heap allocated so moving `TypeProvider`
//! cannot invalidate allocator context pointers.  All returned type pointers
//! remain stable until `deinit`.

const std = @import("std");
const Types = @import("types.zig");
const AST = @import("ast.zig");
const ASTAnnotations = @import("ast_annotations.zig");
const TokenModule = @import("../../liblangutil/token.zig");
const Numeric = @import("../../libsolutil/numeric.zig");

pub const ProviderError = std.mem.Allocator.Error || error{
    InvalidBase,
    InvalidInteger,
    InvalidElementaryType,
    InvalidIntegerType,
    InvalidFixedBytesType,
    InvalidFixedPointType,
    InvalidDataLocation,
    InvalidStateMutability,
    InvalidFunctionType,
    InvalidMetaType,
    NotReferenceType,
    UnsupportedTransientReference,
};

const FixedPointKey = packed struct {
    bits: u16,
    digits: u8,
    signed: bool,
};

const RationalOwner = struct {
    numerator: Types.BigInt,
    denominator: Types.BigInt,

    fn deinit(self: *RationalOwner) void {
        self.numerator.deinit();
        self.denominator.deinit();
        self.* = undefined;
    }
};

const UserDefinedValueTypeState = struct {
    underlying_type: ?*const Types.Type = null,
    instances: std.ArrayList(*Types.Type) = .empty,

    fn deinit(self: *UserDefinedValueTypeState, allocator: std.mem.Allocator) void {
        self.instances.deinit(allocator);
        self.* = undefined;
    }
};

pub const TypeProvider = struct {
    backing_allocator: std.mem.Allocator,
    arena_state: *std.heap.ArenaAllocator,

    bool_type: *const Types.Type,
    inaccessible_type: *const Types.Type,
    empty_tuple_type: *const Types.Type,
    payable_address_type: *const Types.Type,
    address_type: *const Types.Type,
    integer_types: [2][32]*const Types.Type,
    fixed_bytes_types: [32]*const Types.Type,
    magic_types: [5]*const Types.Type,
    bytes_storage_type: *const Types.Type,
    bytes_memory_type: *const Types.Type,
    bytes_calldata_type: *const Types.Type,
    string_storage_type: *const Types.Type,
    string_memory_type: *const Types.Type,
    string_calldata_type: *const Types.Type,

    fixed_points: std.AutoHashMap(FixedPointKey, *const Types.Type),
    string_literals: std.StringHashMap(*const Types.Type),
    user_defined_value_types: std.AutoHashMap(*const AST.Node, UserDefinedValueTypeState),
    rational_owners: std.ArrayList(*RationalOwner) = .empty,

    pub fn init(backing_allocator: std.mem.Allocator) ProviderError!TypeProvider {
        const arena_state = try backing_allocator.create(std.heap.ArenaAllocator);
        arena_state.* = std.heap.ArenaAllocator.init(backing_allocator);

        // Ownership transfers before the next fallible operation. The single
        // cleanup below owns both the arena contents and its backing object.
        var self: TypeProvider = .{
            .backing_allocator = backing_allocator,
            .arena_state = arena_state,
            .bool_type = undefined,
            .inaccessible_type = undefined,
            .empty_tuple_type = undefined,
            .payable_address_type = undefined,
            .address_type = undefined,
            .integer_types = undefined,
            .fixed_bytes_types = undefined,
            .magic_types = undefined,
            .bytes_storage_type = undefined,
            .bytes_memory_type = undefined,
            .bytes_calldata_type = undefined,
            .string_storage_type = undefined,
            .string_memory_type = undefined,
            .string_calldata_type = undefined,
            .fixed_points = std.AutoHashMap(FixedPointKey, *const Types.Type).init(backing_allocator),
            .string_literals = std.StringHashMap(*const Types.Type).init(backing_allocator),
            .user_defined_value_types = std.AutoHashMap(
                *const AST.Node,
                UserDefinedValueTypeState,
            ).init(backing_allocator),
        };
        errdefer self.deinit();

        self.bool_type = try self.createType(.{ .Bool = {} });
        self.inaccessible_type = try self.createType(.{ .InaccessibleDynamic = {} });
        self.empty_tuple_type = try self.createType(.{ .Tuple = .{} });
        self.payable_address_type = try self.createType(.{ .Address = .{
            .state_mutability = .Payable,
        } });
        self.address_type = try self.createType(.{ .Address = .{
            .state_mutability = .NonPayable,
        } });

        for (0..32) |index| {
            const bits: u16 = @intCast((index + 1) * 8);
            self.integer_types[@as(usize, @intCast(@intFromEnum(Types.IntegerModifier.Unsigned)))][index] =
                try self.createType(.{ .Integer = .{
                    .bits = bits,
                    .modifier = .Unsigned,
                } });
            self.integer_types[@as(usize, @intCast(@intFromEnum(Types.IntegerModifier.Signed)))][index] =
                try self.createType(.{ .Integer = .{
                    .bits = bits,
                    .modifier = .Signed,
                } });
            self.fixed_bytes_types[index] = try self.createType(.{ .FixedBytes = .{
                .bytes = @intCast(index + 1),
            } });
        }

        inline for (.{
            Types.MagicKind.Block,
            Types.MagicKind.Message,
            Types.MagicKind.Transaction,
            Types.MagicKind.ABI,
            Types.MagicKind.Error,
        }, 0..) |kind, index| {
            self.magic_types[index] = try self.createType(.{ .Magic = .{ .kind = kind } });
        }

        const byte_type = self.fixed_bytes_types[0];
        self.bytes_storage_type = try self.createByteStringType(.Storage, .Bytes, byte_type);
        self.bytes_memory_type = try self.createByteStringType(.Memory, .Bytes, byte_type);
        self.bytes_calldata_type = try self.createByteStringType(.CallData, .Bytes, byte_type);
        self.string_storage_type = try self.createByteStringType(.Storage, .String, byte_type);
        self.string_memory_type = try self.createByteStringType(.Memory, .String, byte_type);
        self.string_calldata_type = try self.createByteStringType(.CallData, .String, byte_type);
        return self;
    }

    pub fn deinit(self: *TypeProvider) void {
        const backing_allocator = self.backing_allocator;
        const arena_state = self.arena_state;
        for (self.rational_owners.items) |owner| owner.deinit();
        self.rational_owners.deinit(backing_allocator);
        var user_defined_value_types = self.user_defined_value_types.valueIterator();
        while (user_defined_value_types.next()) |state|
            state.deinit(backing_allocator);
        self.user_defined_value_types.deinit();
        self.string_literals.deinit();
        self.fixed_points.deinit();
        arena_state.deinit();
        backing_allocator.destroy(arena_state);
        self.* = undefined;
    }

    pub fn allocator(self: *TypeProvider) std.mem.Allocator {
        return self.arena_state.allocator();
    }

    fn createType(
        self: *TypeProvider,
        payload: Types.Payload,
    ) std.mem.Allocator.Error!*const Types.Type {
        const result = try self.allocator().create(Types.Type);
        result.* = .{ .payload = payload };
        return result;
    }

    fn createByteStringType(
        self: *TypeProvider,
        location: Types.DataLocation,
        kind: Types.ArrayKind,
        byte_type: *const Types.Type,
    ) std.mem.Allocator.Error!*const Types.Type {
        return self.createType(.{ .Array = .{
            .reference = .{
                .location = location,
                .storage_pointer = true,
            },
            .kind = kind,
            .base_type = byte_type,
            .length = null,
        } });
    }

    pub fn boolean(self: *const TypeProvider) *const Types.Type {
        return self.bool_type;
    }

    pub fn inaccessibleDynamic(self: *const TypeProvider) *const Types.Type {
        return self.inaccessible_type;
    }

    pub fn emptyTuple(self: *const TypeProvider) *const Types.Type {
        return self.empty_tuple_type;
    }

    pub fn payableAddress(self: *const TypeProvider) *const Types.Type {
        return self.payable_address_type;
    }

    pub fn address(self: *const TypeProvider) *const Types.Type {
        return self.address_type;
    }

    pub fn integer(
        self: *const TypeProvider,
        bits: u16,
        integer_modifier: Types.IntegerModifier,
    ) ProviderError!*const Types.Type {
        if (bits == 0 or bits > 256 or bits % 8 != 0) return error.InvalidIntegerType;
        return self.integer_types[@as(usize, @intCast(@intFromEnum(integer_modifier)))][bits / 8 - 1];
    }

    pub fn uint(self: *const TypeProvider, bits: u16) ProviderError!*const Types.Type {
        return self.integer(bits, .Unsigned);
    }

    pub fn uint256(self: *const TypeProvider) *const Types.Type {
        return self.integer_types[@as(usize, @intCast(@intFromEnum(Types.IntegerModifier.Unsigned)))][31];
    }

    pub fn int256(self: *const TypeProvider) *const Types.Type {
        return self.integer_types[@as(usize, @intCast(@intFromEnum(Types.IntegerModifier.Signed)))][31];
    }

    pub fn byte(self: *const TypeProvider) *const Types.Type {
        return self.fixed_bytes_types[0];
    }

    pub fn fixedBytes(
        self: *const TypeProvider,
        bytes: u8,
    ) ProviderError!*const Types.Type {
        if (bytes == 0 or bytes > 32) return error.InvalidFixedBytesType;
        return self.fixed_bytes_types[bytes - 1];
    }

    pub fn fixedPoint(
        self: *TypeProvider,
        bits: u16,
        digits: u8,
        fixed_modifier: Types.FixedPointModifier,
    ) ProviderError!*const Types.Type {
        if (bits < 8 or bits > 256 or bits % 8 != 0 or digits > 80)
            return error.InvalidFixedPointType;
        const key: FixedPointKey = .{
            .bits = bits,
            .digits = digits,
            .signed = fixed_modifier == .Signed,
        };
        if (self.fixed_points.get(key)) |existing| return existing;
        const result = try self.createType(.{ .FixedPoint = .{
            .total_bits = bits,
            .fractional_digits = digits,
            .modifier = fixed_modifier,
        } });
        try self.fixed_points.put(key, result);
        return result;
    }

    pub fn bytesStorage(self: *const TypeProvider) *const Types.Type {
        return self.bytes_storage_type;
    }

    pub fn bytesMemory(self: *const TypeProvider) *const Types.Type {
        return self.bytes_memory_type;
    }

    pub fn bytesCalldata(self: *const TypeProvider) *const Types.Type {
        return self.bytes_calldata_type;
    }

    pub fn stringStorage(self: *const TypeProvider) *const Types.Type {
        return self.string_storage_type;
    }

    pub fn stringMemory(self: *const TypeProvider) *const Types.Type {
        return self.string_memory_type;
    }

    pub fn stringCalldata(self: *const TypeProvider) *const Types.Type {
        return self.string_calldata_type;
    }

    pub fn byteString(
        self: *TypeProvider,
        location: Types.DataLocation,
        is_string: bool,
    ) ProviderError!*const Types.Type {
        if (location == .Transient) return error.UnsupportedTransientReference;
        return if (is_string) switch (location) {
            .Storage => self.string_storage_type,
            .Memory => self.string_memory_type,
            .CallData => self.string_calldata_type,
            .Transient => unreachable,
        } else switch (location) {
            .Storage => self.bytes_storage_type,
            .Memory => self.bytes_memory_type,
            .CallData => self.bytes_calldata_type,
            .Transient => unreachable,
        };
    }

    pub fn array(
        self: *TypeProvider,
        location: Types.DataLocation,
        base_type: *const Types.Type,
    ) ProviderError!*const Types.Type {
        return self.arrayWithLength(location, base_type, null);
    }

    pub fn arrayWithLength(
        self: *TypeProvider,
        location: Types.DataLocation,
        base_type: *const Types.Type,
        length: ?u256,
    ) ProviderError!*const Types.Type {
        if (location == .Transient) return error.UnsupportedTransientReference;
        const localized_base = try self.withLocationIfReference(location, base_type, false);
        return self.createType(.{ .Array = .{
            .reference = .{ .location = location },
            .base_type = localized_base,
            .length = length,
        } });
    }

    pub fn arraySlice(
        self: *TypeProvider,
        array_type: *const Types.Type,
    ) ProviderError!*const Types.Type {
        if (array_type.category() != .Array) return error.InvalidElementaryType;
        return self.createType(.{ .ArraySlice = .{ .array_type = array_type } });
    }

    pub fn withLocation(
        self: *TypeProvider,
        type_ref: *const Types.Type,
        location: Types.DataLocation,
        is_pointer: bool,
    ) ProviderError!*const Types.Type {
        if (location == .Transient) return error.UnsupportedTransientReference;
        const reference = type_ref.asReference() orelse return error.NotReferenceType;
        if (reference.location == location and reference.isPointer() ==
            (location != .Storage or is_pointer)) return type_ref;

        return switch (type_ref.payload) {
            .Array => |array_value| blk: {
                if (array_value.kind != .Ordinary and
                    (location != .Storage or is_pointer))
                {
                    break :blk self.byteString(location, array_value.kind == .String);
                }
                const localized_base = try self.withLocationIfReference(
                    location,
                    array_value.base_type,
                    false,
                );
                break :blk self.createType(.{ .Array = .{
                    .reference = .{
                        .location = location,
                        .storage_pointer = if (location == .Storage) is_pointer else true,
                    },
                    .kind = array_value.kind,
                    .base_type = localized_base,
                    .length = array_value.length,
                } });
            },
            .Struct => |struct_value| self.createType(.{ .Struct = .{
                .reference = .{
                    .location = location,
                    .storage_pointer = if (location == .Storage) is_pointer else true,
                },
                .declaration = struct_value.declaration,
            } }),
            else => error.NotReferenceType,
        };
    }

    pub fn withLocationIfReference(
        self: *TypeProvider,
        location: Types.DataLocation,
        type_ref: *const Types.Type,
        is_pointer: bool,
    ) ProviderError!*const Types.Type {
        if (type_ref.asReference() == null) return type_ref;
        return self.withLocation(type_ref, location, is_pointer);
    }

    pub fn tuple(
        self: *TypeProvider,
        components: []const ?*const Types.Type,
    ) ProviderError!*const Types.Type {
        if (components.len == 0) return self.empty_tuple_type;
        const owned = try self.allocator().dupe(?*const Types.Type, components);
        return self.createType(.{ .Tuple = .{ .components = owned } });
    }

    pub fn tupleOfTypes(
        self: *TypeProvider,
        components: []const *const Types.Type,
    ) ProviderError!*const Types.Type {
        if (components.len == 0) return self.empty_tuple_type;
        const owned = try self.allocator().alloc(?*const Types.Type, components.len);
        for (components, 0..) |component, index| owned[index] = component;
        return self.createType(.{ .Tuple = .{ .components = owned } });
    }

    pub fn function(
        self: *TypeProvider,
        parameter_types: []const *const Types.Type,
        return_parameter_types: []const *const Types.Type,
        parameter_names: []const []const u8,
        return_parameter_names: []const []const u8,
        kind: Types.FunctionKind,
        state_mutability: Types.StateMutability,
        declaration: ?*const AST.Node,
        options: Types.FunctionOptions,
    ) ProviderError!*const Types.Type {
        if (parameter_types.len != parameter_names.len or
            return_parameter_types.len != return_parameter_names.len or
            (options.has_bound_first_argument and parameter_types.len == 0))
            return error.InvalidFunctionType;
        const owned_parameters = try self.allocator().dupe(*const Types.Type, parameter_types);
        const owned_returns = try self.allocator().dupe(*const Types.Type, return_parameter_types);
        const owned_parameter_names = try self.copyNames(parameter_names);
        const owned_return_names = try self.copyNames(return_parameter_names);
        return self.createType(.{ .Function = .{
            .parameter_types = owned_parameters,
            .return_parameter_types = owned_returns,
            .parameter_names = owned_parameter_names,
            .return_parameter_names = owned_return_names,
            .kind = kind,
            .state_mutability = state_mutability,
            .declaration = declaration,
            .options = options,
        } });
    }

    pub fn functionFromDefinition(
        self: *TypeProvider,
        definition: *const AST.Node,
        kind: Types.FunctionKind,
    ) ProviderError!*const Types.Type {
        if (definition.nodeKind() != .function_definition or
            (kind != .Internal and kind != .External and kind != .Declaration))
            return error.InvalidFunctionType;
        const value = definition.payload.function_definition;
        var parameters = try self.parameterTypesAndNamesAlloc(value.callable.parameters);
        defer parameters.deinit(self.backing_allocator);
        var returns = try self.parameterTypesAndNamesAlloc(value.callable.return_parameters);
        defer returns.deinit(self.backing_allocator);
        const state_mutability = if (kind == .Internal and
            value.state_mutability == .Payable)
            Types.StateMutability.NonPayable
        else
            value.state_mutability;
        return self.function(
            parameters.types,
            returns.types,
            parameters.names,
            returns.names,
            kind,
            state_mutability,
            definition,
            .{},
        );
    }

    pub fn functionFromVariable(
        self: *TypeProvider,
        variable: *const AST.Node,
    ) ProviderError!*const Types.Type {
        if (variable.nodeKind() != .variable_declaration)
            return error.InvalidFunctionType;
        var current = try annotatedVariableType(variable);
        var parameter_types: std.ArrayList(*const Types.Type) = .empty;
        defer parameter_types.deinit(self.backing_allocator);
        var parameter_names: std.ArrayList([]const u8) = .empty;
        defer parameter_names.deinit(self.backing_allocator);
        var return_name: []const u8 = "";
        while (true) switch (current.payload) {
            .Mapping => |mapping_type| {
                try parameter_types.append(self.backing_allocator, mapping_type.key_type);
                try parameter_names.append(self.backing_allocator, mapping_type.key_name);
                current = mapping_type.value_type;
                return_name = mapping_type.value_name;
            },
            .Array => |array_type| {
                if (array_type.isByteArrayOrString()) break;
                try parameter_types.append(self.backing_allocator, self.uint256());
                try parameter_names.append(self.backing_allocator, "");
                current = array_type.base_type;
            },
            else => break,
        };

        var return_types: std.ArrayList(*const Types.Type) = .empty;
        defer return_types.deinit(self.backing_allocator);
        var return_names: std.ArrayList([]const u8) = .empty;
        defer return_names.deinit(self.backing_allocator);
        if (current.category() == .Struct) {
            const structure = current.payload.Struct;
            if (structure.declaration.nodeKind() != .struct_definition)
                return error.InvalidFunctionType;
            for (structure.declaration.payload.struct_definition.members) |member| {
                const raw_member = try annotatedVariableType(member);
                const member_type = try self.withLocationIfReference(
                    structure.reference.location,
                    raw_member,
                    true,
                );
                if (member_type.category() == .Mapping) continue;
                if (member_type.asArray()) |array_type|
                    if (!array_type.isByteArrayOrString()) continue;
                try return_types.append(
                    self.backing_allocator,
                    try self.withLocationIfReference(.Memory, member_type, false),
                );
                try return_names.append(
                    self.backing_allocator,
                    member.payload.variable_declaration.declaration.name,
                );
            }
        } else {
            try return_types.append(
                self.backing_allocator,
                try self.withLocationIfReference(.Memory, current, false),
            );
            try return_names.append(self.backing_allocator, return_name);
        }
        return self.function(
            parameter_types.items,
            return_types.items,
            parameter_names.items,
            return_names.items,
            .External,
            .View,
            variable,
            .{},
        );
    }

    pub fn functionFromEvent(
        self: *TypeProvider,
        event: *const AST.Node,
    ) ProviderError!*const Types.Type {
        if (event.nodeKind() != .event_definition) return error.InvalidFunctionType;
        var parameters = try self.parameterTypesAndNamesAlloc(
            event.payload.event_definition.callable.parameters,
        );
        defer parameters.deinit(self.backing_allocator);
        return self.function(
            parameters.types,
            &.{},
            parameters.names,
            &.{},
            .Event,
            .NonPayable,
            event,
            .{},
        );
    }

    pub fn functionFromError(
        self: *TypeProvider,
        error_definition: *const AST.Node,
    ) ProviderError!*const Types.Type {
        if (error_definition.nodeKind() != .error_definition)
            return error.InvalidFunctionType;
        var parameters = try self.parameterTypesAndNamesAlloc(
            error_definition.payload.error_definition.callable.parameters,
        );
        defer parameters.deinit(self.backing_allocator);
        const returns = [_]*const Types.Type{try self.magic(.Error)};
        const return_names = [_][]const u8{""};
        return self.function(
            parameters.types,
            &returns,
            parameters.names,
            &return_names,
            .Error,
            .Pure,
            error_definition,
            .{},
        );
    }

    pub fn functionFromTypeName(
        self: *TypeProvider,
        type_name: *const AST.Node,
    ) ProviderError!*const Types.Type {
        if (type_name.nodeKind() != .function_type_name)
            return error.InvalidFunctionType;
        const value = type_name.payload.function_type_name;
        const kind: Types.FunctionKind = switch (value.effectiveVisibility()) {
            .Internal => .Internal,
            .External => .External,
            else => return error.InvalidFunctionType,
        };
        if (value.state_mutability == .Payable and kind != .External)
            return error.InvalidFunctionType;
        var parameters = try self.parameterTypesAndNamesAlloc(value.parameter_types);
        defer parameters.deinit(self.backing_allocator);
        var returns = try self.parameterTypesAndNamesAlloc(value.return_types);
        defer returns.deinit(self.backing_allocator);
        const parameter_names = try self.backing_allocator.alloc(
            []const u8,
            parameters.types.len,
        );
        defer self.backing_allocator.free(parameter_names);
        @memset(parameter_names, "");
        const return_names = try self.backing_allocator.alloc(
            []const u8,
            returns.types.len,
        );
        defer self.backing_allocator.free(return_names);
        @memset(return_names, "");
        return self.function(
            parameters.types,
            returns.types,
            parameter_names,
            return_names,
            kind,
            value.state_mutability,
            null,
            .{},
        );
    }

    const ParameterTypesAndNames = struct {
        types: []*const Types.Type,
        names: [][]const u8,

        fn deinit(self: *ParameterTypesAndNames, backing_allocator: std.mem.Allocator) void {
            backing_allocator.free(self.types);
            backing_allocator.free(self.names);
            self.* = undefined;
        }
    };

    fn parameterTypesAndNamesAlloc(
        self: *TypeProvider,
        maybe_list: ?*const AST.Node,
    ) ProviderError!ParameterTypesAndNames {
        const parameters = if (maybe_list) |list| blk: {
            if (list.nodeKind() != .parameter_list) return error.InvalidFunctionType;
            break :blk list.payload.parameter_list.parameters;
        } else @as(AST.NodeList, &.{});
        const types = try self.backing_allocator.alloc(*const Types.Type, parameters.len);
        errdefer self.backing_allocator.free(types);
        const names = try self.backing_allocator.alloc([]const u8, parameters.len);
        errdefer self.backing_allocator.free(names);
        for (parameters, 0..) |parameter, index| {
            types[index] = try annotatedVariableType(parameter);
            names[index] = parameter.payload.variable_declaration.declaration.name;
        }
        return .{ .types = types, .names = names };
    }

    pub fn functionFromTypeNames(
        self: *TypeProvider,
        parameter_names_as_types: []const []const u8,
        return_names_as_types: []const []const u8,
        kind: Types.FunctionKind,
        state_mutability: Types.StateMutability,
        options: Types.FunctionOptions,
    ) ProviderError!*const Types.Type {
        if (options.gas_set or options.value_set or options.salt_set or
            options.has_bound_first_argument) return error.InvalidFunctionType;
        const parameters = try self.allocator().alloc(*const Types.Type, parameter_names_as_types.len);
        for (parameter_names_as_types, 0..) |name, index|
            parameters[index] = try self.fromElementaryTypeName(name);
        const returns = try self.allocator().alloc(*const Types.Type, return_names_as_types.len);
        for (return_names_as_types, 0..) |name, index|
            returns[index] = try self.fromElementaryTypeName(name);
        const parameter_names = try self.emptyNames(parameter_names_as_types.len);
        const return_names = try self.emptyNames(return_names_as_types.len);
        return self.function(
            parameters,
            returns,
            parameter_names,
            return_names,
            kind,
            state_mutability,
            null,
            options,
        );
    }

    fn copyNames(
        self: *TypeProvider,
        names: []const []const u8,
    ) std.mem.Allocator.Error![]const []const u8 {
        const owned = try self.allocator().alloc([]const u8, names.len);
        for (names, 0..) |name, index| owned[index] = try self.allocator().dupe(u8, name);
        return owned;
    }

    fn emptyNames(
        self: *TypeProvider,
        count: usize,
    ) std.mem.Allocator.Error![]const []const u8 {
        const names = try self.allocator().alloc([]const u8, count);
        @memset(names, "");
        return names;
    }

    pub fn withBoundFirstArgument(
        self: *TypeProvider,
        function_type: *const Types.Type,
    ) ProviderError!*const Types.Type {
        const value = function_type.asFunction() orelse return error.InvalidFunctionType;
        if (value.parameter_types.len == 0 or
            value.options.has_bound_first_argument or
            value.options.gas_set or
            value.options.value_set or
            value.options.salt_set)
            return error.InvalidFunctionType;
        var options = value.options;
        options.has_bound_first_argument = true;
        return self.function(
            value.parameter_types,
            value.return_parameter_types,
            value.parameter_names,
            value.return_parameter_names,
            value.kind,
            value.state_mutability,
            value.declaration,
            options,
        );
    }

    pub fn copyAndSetCallOptions(
        self: *TypeProvider,
        function_type: *const Types.Type,
        set_gas: bool,
        set_value: bool,
        set_salt: bool,
    ) ProviderError!*const Types.Type {
        const value = function_type.asFunction() orelse return error.InvalidFunctionType;
        if (value.kind == .Declaration) return error.InvalidFunctionType;
        var options = value.options;
        options.gas_set = options.gas_set or set_gas;
        options.value_set = options.value_set or set_value;
        options.salt_set = options.salt_set or set_salt;
        return self.function(
            value.parameter_types,
            value.return_parameter_types,
            value.parameter_names,
            value.return_parameter_names,
            value.kind,
            value.state_mutability,
            value.declaration,
            options,
        );
    }

    pub fn stringLiteral(
        self: *TypeProvider,
        value: []const u8,
    ) ProviderError!*const Types.Type {
        if (self.string_literals.get(value)) |existing| return existing;
        const owned_value = try self.allocator().dupe(u8, value);
        const result = try self.createType(.{ .StringLiteral = .{ .value = owned_value } });
        try self.string_literals.put(owned_value, result);
        return result;
    }

    pub fn rationalInteger(
        self: *TypeProvider,
        digits: []const u8,
        compatible_bytes_type: ?*const Types.Type,
    ) ProviderError!*const Types.Type {
        const clean = try removeUnderscoresAlloc(self.backing_allocator, digits);
        defer self.backing_allocator.free(clean);
        const owner = try self.allocator().create(RationalOwner);
        owner.* = .{
            .numerator = try Types.BigInt.parse(self.backing_allocator, clean, 0),
            .denominator = Types.BigInt.initUnsigned(1),
        };
        errdefer owner.deinit();
        try self.rational_owners.append(self.backing_allocator, owner);
        return self.createType(.{ .RationalNumber = .{
            .numerator = &owner.numerator,
            .denominator = &owner.denominator,
            .compatible_bytes_type = compatible_bytes_type,
        } });
    }

    /// Interns a normalized arbitrary-precision rational result. The provider
    /// owns independent arbitrary-precision values so callers can tear down their temporaries
    /// immediately after this function returns.
    pub fn rationalNumber(
        self: *TypeProvider,
        numerator: *const Types.BigInt,
        denominator: *const Types.BigInt,
        compatible_bytes_type: ?*const Types.Type,
    ) ProviderError!*const Types.Type {
        if (denominator.isZero()) return error.InvalidInteger;
        var normalized_numerator = numerator.clone();
        errdefer normalized_numerator.deinit();
        var normalized_denominator = denominator.clone();
        errdefer normalized_denominator.deinit();
        if (normalized_denominator.isNegative()) {
            var positive_denominator = normalized_denominator.negate();
            var negated_numerator = normalized_numerator.negate();
            normalized_denominator.deinit();
            normalized_numerator.deinit();
            normalized_denominator = positive_denominator.take();
            normalized_numerator = negated_numerator.take();
        }
        var divisor = Types.BigInt.gcd(
            &normalized_numerator,
            &normalized_denominator,
        );
        defer divisor.deinit();
        if (divisor.compareUnsigned(1) != .eq) {
            var reduced_numerator = Types.BigInt.quotient( // zlinter-disable-current-line no_swallow_error - GCD is nonzero for the normalized rational
                &normalized_numerator,
                &divisor,
            ) catch unreachable;
            var reduced_denominator = Types.BigInt.quotient( // zlinter-disable-current-line no_swallow_error - GCD is nonzero for the normalized rational
                &normalized_denominator,
                &divisor,
            ) catch unreachable;
            normalized_numerator.deinit();
            normalized_denominator.deinit();
            normalized_numerator = reduced_numerator.take();
            normalized_denominator = reduced_denominator.take();
        }
        const owner = try self.allocator().create(RationalOwner);
        owner.* = .{
            .numerator = normalized_numerator.take(),
            .denominator = normalized_denominator.take(),
        };
        self.rational_owners.append(self.backing_allocator, owner) catch |err| {
            owner.deinit();
            return err;
        };
        return self.createType(.{ .RationalNumber = .{
            .numerator = &owner.numerator,
            .denominator = &owner.denominator,
            .compatible_bytes_type = compatible_bytes_type,
        } });
    }

    pub fn forLiteral(
        self: *TypeProvider,
        literal: AST.Literal,
    ) ProviderError!?*const Types.Type {
        return switch (literal.token) {
            .TrueLiteral, .FalseLiteral => self.boolean(),
            .StringLiteral, .UnicodeStringLiteral, .HexStringLiteral => try self.stringLiteral(literal.value),
            .Number => self.rationalLiteral(literal),
            else => null,
        };
    }

    fn rationalLiteral(
        self: *TypeProvider,
        literal: AST.Literal,
    ) ProviderError!?*const Types.Type {
        const clean = try removeUnderscoresAlloc(self.backing_allocator, literal.value);
        defer self.backing_allocator.free(clean);
        if (clean.len == 0) return null;

        var compatible: ?*const Types.Type = null;
        var numerator: Types.BigInt = undefined;
        var numerator_initialized = false;
        defer if (numerator_initialized) numerator.deinit();
        var denominator: Types.BigInt = undefined;
        var denominator_initialized = false;
        defer if (denominator_initialized) denominator.deinit();
        if (literal.token == .Number and
            std.mem.startsWith(u8, literal.value, "0x"))
        {
            numerator = Types.BigInt.parse(self.backing_allocator, clean, 0) catch return null;
            numerator_initialized = true;
            denominator = Types.BigInt.initUnsigned(1);
            denominator_initialized = true;
            const digit_count = clean.len - 2;
            if (digit_count % 2 == 0 and digit_count / 2 <= 32 and digit_count != 0)
                compatible = try self.fixedBytes(@intCast(digit_count / 2));
        } else {
            const exponent_index = std.mem.findAny(u8, clean, "eE");
            const mantissa = if (exponent_index) |index| clean[0..index] else clean;
            const point_index = std.mem.findScalar(u8, mantissa, '.');
            const whole = if (point_index) |index| mantissa[0..index] else mantissa;
            const fraction = if (point_index) |index| mantissa[index + 1 ..] else "";
            if (whole.len == 0 or (point_index != null and fraction.len == 0)) return null;
            const digits = try self.backing_allocator.alloc(u8, whole.len + fraction.len);
            defer self.backing_allocator.free(digits);
            @memcpy(digits[0..whole.len], whole);
            @memcpy(digits[whole.len..], fraction);
            numerator = Types.BigInt.parse(
                self.backing_allocator,
                if (digits.len == 0) "0" else digits,
                10,
            ) catch return null;
            numerator_initialized = true;
            var ten = Types.BigInt.initUnsigned(10);
            defer ten.deinit();
            denominator = ten.pow(@intCast(fraction.len));
            denominator_initialized = true;
            if (exponent_index) |index| {
                // Upstream accepts zero before attempting to parse the exponent,
                // so even a decimal exponent outside every machine integer range
                // still denotes the exact value zero.
                if (!numerator.isZero()) {
                    const exponent = std.fmt.parseInt(
                        i32,
                        clean[index + 1 ..],
                        10,
                    ) catch return null;
                    const exponent_abs: u32 = if (exponent < 0)
                        @intCast(-@as(i64, exponent))
                    else
                        @intCast(exponent);
                    if (exponent < 0) {
                        if (!(Numeric.fitsPrecisionBaseX( // zlinter-disable-current-line no_swallow_error - bounded exponent and normalized value satisfy the helper preconditions
                            &denominator,
                            3.3219280948873624,
                            exponent_abs,
                        ) catch unreachable)) return null;
                        var scale = ten.pow(exponent_abs);
                        defer scale.deinit();
                        var scaled = Types.BigInt.mul(&denominator, &scale);
                        denominator.deinit();
                        denominator = scaled.take();
                    } else if (exponent > 0) {
                        if (!(Numeric.fitsPrecisionBaseX( // zlinter-disable-current-line no_swallow_error - bounded exponent and normalized value satisfy the helper preconditions
                            &numerator,
                            3.3219280948873624,
                            exponent_abs,
                        ) catch unreachable)) return null;
                        var scale = ten.pow(exponent_abs);
                        defer scale.deinit();
                        var scaled = Types.BigInt.mul(&numerator, &scale);
                        numerator.deinit();
                        numerator = scaled.take();
                    }
                }
            }
        }
        const denomination: u64 = switch (literal.sub_denomination) {
            .None, .Wei, .Second => 1,
            .Gwei => 1_000_000_000,
            .Ether => 1_000_000_000_000_000_000,
            .Minute => 60,
            .Hour => 3_600,
            .Day => 86_400,
            .Week => 604_800,
            .Year => 31_536_000,
        };
        if (denomination != 1) {
            var multiplier = Types.BigInt.initUnsigned(denomination);
            defer multiplier.deinit();
            var scaled = Types.BigInt.mul(&numerator, &multiplier);
            numerator.deinit();
            numerator = scaled.take();
            compatible = null;
        }
        return try self.rationalNumber(&numerator, &denominator, compatible);
    }

    pub fn contract(
        self: *TypeProvider,
        declaration: *const AST.Node,
        is_super: bool,
    ) ProviderError!*const Types.Type {
        if (declaration.nodeKind() != .contract_definition) return error.InvalidElementaryType;
        return self.createType(.{ .Contract = .{
            .declaration = declaration,
            .is_super = is_super,
        } });
    }

    pub fn structType(
        self: *TypeProvider,
        declaration: *const AST.Node,
        location: Types.DataLocation,
    ) ProviderError!*const Types.Type {
        if (declaration.nodeKind() != .struct_definition) return error.InvalidElementaryType;
        if (location == .Transient) return error.UnsupportedTransientReference;
        return self.createType(.{ .Struct = .{
            .reference = .{ .location = location },
            .declaration = declaration,
        } });
    }

    pub fn enumType(
        self: *TypeProvider,
        declaration: *const AST.Node,
    ) ProviderError!*const Types.Type {
        if (declaration.nodeKind() != .enum_definition) return error.InvalidElementaryType;
        return self.createType(.{ .Enum = .{ .declaration = declaration } });
    }

    pub fn userDefinedValueType(
        self: *TypeProvider,
        declaration: *const AST.Node,
        underlying_type: ?*const Types.Type,
    ) ProviderError!*const Types.Type {
        if (declaration.nodeKind() != .user_defined_value_type_definition)
            return error.InvalidElementaryType;
        const entry = try self.user_defined_value_types.getOrPut(declaration);
        if (!entry.found_existing) entry.value_ptr.* = .{};
        if (underlying_type) |underlying| {
            if (entry.value_ptr.underlying_type) |known| {
                if (known != underlying and !elementaryTypesEqual(known, underlying))
                    return error.InvalidElementaryType;
            } else {
                entry.value_ptr.underlying_type = underlying;
                for (entry.value_ptr.instances.items) |instance|
                    instance.payload.UserDefinedValueType.underlying_type = underlying;
            }
        }

        // Upstream creates a fresh UserDefinedValueType for every provider
        // request. Its TupleType equality compares component pointers, making
        // this identity observable in conditional tuple conversions.
        const created = @constCast(try self.createType(.{ .UserDefinedValueType = .{
            .declaration = declaration,
            .underlying_type = entry.value_ptr.underlying_type,
        } }));
        try entry.value_ptr.instances.append(self.backing_allocator, created);
        return created;
    }

    pub fn module(
        self: *TypeProvider,
        source_unit: *const AST.Node,
    ) ProviderError!*const Types.Type {
        if (source_unit.nodeKind() != .source_unit) return error.InvalidElementaryType;
        return self.createType(.{ .Module = .{ .source_unit = source_unit } });
    }

    pub fn typeType(
        self: *TypeProvider,
        actual_type: *const Types.Type,
    ) ProviderError!*const Types.Type {
        return self.createType(.{ .TypeType = .{ .actual_type = actual_type } });
    }

    pub fn modifier(
        self: *TypeProvider,
        parameter_types: []const *const Types.Type,
    ) ProviderError!*const Types.Type {
        const owned = try self.allocator().dupe(*const Types.Type, parameter_types);
        return self.createType(.{ .Modifier = .{ .parameter_types = owned } });
    }

    pub fn magic(
        self: *const TypeProvider,
        kind: Types.MagicKind,
    ) ProviderError!*const Types.Type {
        if (kind == .MetaType) return error.InvalidMetaType;
        return self.magic_types[@as(usize, @intCast(@intFromEnum(kind)))];
    }

    pub fn meta(
        self: *TypeProvider,
        type_argument: *const Types.Type,
    ) ProviderError!*const Types.Type {
        switch (type_argument.category()) {
            .Contract, .Integer, .Enum => {},
            else => return error.InvalidMetaType,
        }
        return self.createType(.{ .Magic = .{
            .kind = .MetaType,
            .type_argument = type_argument,
        } });
    }

    pub fn mapping(
        self: *TypeProvider,
        key_type: *const Types.Type,
        key_name: []const u8,
        value_type: *const Types.Type,
        value_name: []const u8,
    ) ProviderError!*const Types.Type {
        return self.createType(.{ .Mapping = .{
            .key_type = key_type,
            .key_name = try self.allocator().dupe(u8, key_name),
            .value_type = value_type,
            .value_name = try self.allocator().dupe(u8, value_name),
        } });
    }

    pub fn fromElementaryTypeToken(
        self: *TypeProvider,
        type_name: TokenModule.ElementaryTypeNameToken,
        state_mutability: ?Types.StateMutability,
    ) ProviderError!*const Types.Type {
        const m: u16 = @intCast(type_name.first_number);
        const n: u8 = @intCast(type_name.second_number);
        return switch (type_name.token_value) {
            .IntM => self.integer(m, .Signed),
            .UIntM => self.integer(m, .Unsigned),
            .Byte => self.byte(),
            .BytesM => self.fixedBytes(@intCast(m)),
            .FixedMxN => self.fixedPoint(m, n, .Signed),
            .UFixedMxN => self.fixedPoint(m, n, .Unsigned),
            .Int => self.int256(),
            .UInt => self.uint256(),
            .Fixed => self.fixedPoint(128, 18, .Signed),
            .UFixed => self.fixedPoint(128, 18, .Unsigned),
            .Address => blk: {
                if (state_mutability) |value| {
                    if (value != .Payable) return error.InvalidStateMutability;
                    break :blk self.payableAddress();
                }
                break :blk self.address();
            },
            .Bool => self.boolean(),
            .Bytes => self.bytesStorage(),
            .String => self.stringStorage(),
            else => error.InvalidElementaryType,
        };
    }

    pub fn fromElementaryTypeName(
        self: *TypeProvider,
        name: []const u8,
    ) ProviderError!*const Types.Type {
        const separator = std.mem.findScalar(u8, name, ' ');
        const base_name = if (separator) |index| name[0..index] else name;
        const suffix = if (separator) |index| name[index + 1 ..] else "";
        if (base_name.len == 0 or (suffix.len != 0 and std.mem.findScalar(u8, suffix, ' ') != null))
            return error.InvalidElementaryType;
        const token = TokenModule.fromIdentifierOrKeyword(base_name);
        if (!TokenModule.isElementaryTypeName(token.token)) return error.InvalidElementaryType;
        const elementary = TokenModule.ElementaryTypeNameToken.init(
            token.token,
            token.first_number,
            token.second_number,
        ) catch return error.InvalidElementaryType;
        var result = try self.fromElementaryTypeToken(elementary, null);
        if (result.asReference() != null) {
            const location: Types.DataLocation = if (suffix.len == 0 or
                std.mem.eql(u8, suffix, "storage"))
                .Storage
            else if (std.mem.eql(u8, suffix, "memory"))
                .Memory
            else if (std.mem.eql(u8, suffix, "calldata"))
                .CallData
            else
                return error.InvalidDataLocation;
            result = try self.withLocation(result, location, true);
        } else if (result.category() == .Address) {
            if (suffix.len == 0) return result;
            if (!std.mem.eql(u8, suffix, "payable")) return error.InvalidStateMutability;
            result = self.payableAddress();
        } else if (suffix.len != 0) {
            return error.InvalidDataLocation;
        }
        return result;
    }
};

fn annotatedVariableType(node: *const AST.Node) ProviderError!*const Types.Type {
    if (node.nodeKind() != .variable_declaration)
        return error.InvalidFunctionType;
    const annotation = ASTAnnotations.annotationConst(node) orelse
        return error.InvalidFunctionType;
    return switch (annotation.*) {
        .variable_declaration => |value| value.type_ref orelse
            error.InvalidFunctionType,
        else => error.InvalidFunctionType,
    };
}

fn elementaryTypesEqual(left: *const Types.Type, right: *const Types.Type) bool {
    if (left.category() != right.category()) return false;
    return switch (left.payload) {
        .Address => |value| value.state_mutability == right.payload.Address.state_mutability,
        .Integer => |value| value.bits == right.payload.Integer.bits and
            value.modifier == right.payload.Integer.modifier,
        .Bool => true,
        .FixedPoint => |value| value.total_bits == right.payload.FixedPoint.total_bits and
            value.fractional_digits == right.payload.FixedPoint.fractional_digits and
            value.modifier == right.payload.FixedPoint.modifier,
        .FixedBytes => |value| value.bytes == right.payload.FixedBytes.bytes,
        else => false,
    };
}

fn removeUnderscoresAlloc(
    allocator: std.mem.Allocator,
    value: []const u8,
) std.mem.Allocator.Error![]u8 {
    const output = try allocator.alloc(u8, value.len);
    var length: usize = 0;
    for (value) |byte| {
        if (byte == '_') continue;
        output[length] = byte;
        length += 1;
    }
    return allocator.realloc(output, length);
}

test "provider canonical basics, parsing, and stable moved arena" {
    var provider = try TypeProvider.init(std.testing.allocator);

    try std.testing.expect(provider.boolean() == provider.boolean());
    try std.testing.expect((try provider.uint(256)) == provider.uint256());
    try std.testing.expect((try provider.fixedBytes(32)) ==
        (try provider.fromElementaryTypeName("bytes32")));
    try std.testing.expect(provider.payableAddress() ==
        (try provider.fromElementaryTypeName("address payable")));
    try std.testing.expect(provider.bytesMemory() ==
        (try provider.fromElementaryTypeName("bytes memory")));

    const pointer_before_move = provider.uint256();
    var moved = provider;
    provider = undefined;
    defer moved.deinit();
    try std.testing.expect(pointer_before_move == moved.uint256());
    try std.testing.expectEqual(@as(u16, 256), pointer_before_move.asInteger().?.bits);
}

test "provider owns composite slices and tears down native literal values" {
    var provider = try TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    const uint_type = provider.uint256();
    const function_type = try provider.function(
        &.{uint_type},
        &.{provider.boolean()},
        &.{"amount"},
        &.{"ok"},
        .Internal,
        .Pure,
        null,
        .{},
    );
    try std.testing.expectEqual(@as(usize, 1), function_type.asFunction().?.parameter_types.len);
    try std.testing.expectEqualStrings("amount", function_type.asFunction().?.parameter_names[0]);

    const literal = try provider.rationalInteger("12_345", null);
    try std.testing.expectEqual(
        std.math.Order.eq,
        literal.payload.RationalNumber.numerator.compareUnsigned(12_345),
    );
}

test "provider preserves fresh upstream UDVT identities and backfills underlying types" {
    var provider = try TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    var tree = try AST.Tree.init(std.testing.allocator, "", "Types.sol");
    defer tree.deinit();

    const underlying_name = try tree.createNode(.{}, .{ .elementary_type_name = .{
        .type_name = try TokenModule.ElementaryTypeNameToken.init(.Address, 0, 0),
    } });
    const definition = try tree.createNode(.{}, .{ .user_defined_value_type_definition = .{
        .declaration = .{ .name = "Currency" },
        .underlying_type = underlying_name,
    } });

    const before_resolution = try provider.userDefinedValueType(definition, null);
    const resolved = try provider.userDefinedValueType(definition, provider.address());
    const repeated = try provider.userDefinedValueType(definition, null);
    try std.testing.expect(before_resolution != resolved);
    try std.testing.expect(resolved != repeated);
    try std.testing.expect(before_resolution.payload.UserDefinedValueType.underlying_type ==
        provider.address());
    try std.testing.expect(resolved.payload.UserDefinedValueType.underlying_type ==
        provider.address());
    try std.testing.expect(repeated.payload.UserDefinedValueType.underlying_type ==
        provider.address());

    const first_tuple = try provider.tupleOfTypes(&.{ before_resolution, resolved });
    const second_tuple = try provider.tupleOfTypes(&.{ resolved, repeated });
    try std.testing.expect(first_tuple.payload.Tuple.components[0] !=
        second_tuple.payload.Tuple.components[0]);
}

test "provider normalizes decimal, exponent, and denomination literals" {
    var provider = try TypeProvider.init(std.testing.allocator);
    defer provider.deinit();
    const decimal = (try provider.forLiteral(.{
        .token = .Number,
        .value = "2.5e2",
    })).?;
    try std.testing.expectEqual(
        std.math.Order.eq,
        decimal.payload.RationalNumber.numerator.compareUnsigned(250),
    );
    try std.testing.expectEqual(
        std.math.Order.eq,
        decimal.payload.RationalNumber.denominator.compareUnsigned(1),
    );

    const ether = (try provider.forLiteral(.{
        .token = .Number,
        .value = "1.5",
        .sub_denomination = .Ether,
    })).?;
    var expected = try Types.BigInt.parse(
        std.testing.allocator,
        "1500000000000000000",
        10,
    );
    defer expected.deinit();
    try std.testing.expectEqual(
        std.math.Order.eq,
        ether.payload.RationalNumber.numerator.compare(&expected),
    );
    try std.testing.expectEqual(
        std.math.Order.eq,
        ether.payload.RationalNumber.denominator.compareUnsigned(1),
    );
}

test "rational literal precision matches the 4096-bit upstream boundary" {
    var provider = try TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const zero = (try provider.forLiteral(.{
        .token = .Number,
        .value = "0E999999999999999999999999999999999999999",
    })).?;
    try std.testing.expect(zero.payload.RationalNumber.numerator.isZero());
    try std.testing.expectEqual(
        std.math.Order.eq,
        zero.payload.RationalNumber.denominator.compareUnsigned(1),
    );

    try std.testing.expect((try provider.forLiteral(.{
        .token = .Number,
        .value = "1e1233",
    })) != null);
    try std.testing.expect((try provider.forLiteral(.{
        .token = .Number,
        .value = "1e1234",
    })) == null);
    try std.testing.expect((try provider.forLiteral(.{
        .token = .Number,
        .value = "1e-1233",
    })) != null);
    try std.testing.expect((try provider.forLiteral(.{
        .token = .Number,
        .value = "1e-1234",
    })) == null);
}

test "provider derives every declaration-backed function type as one family" {
    var tree = try AST.Tree.init(std.testing.allocator, "", "Types.sol");
    defer tree.deinit();
    var provider = try TypeProvider.init(std.testing.allocator);
    defer provider.deinit();

    const parameter = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "amount" },
    } });
    (try ASTAnnotations.ensure(&tree, parameter)).variable_declaration.type_ref =
        provider.uint256();
    const result = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "ok" },
    } });
    (try ASTAnnotations.ensure(&tree, result)).variable_declaration.type_ref =
        provider.boolean();
    const parameters = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{parameter}),
    } });
    const returns = try tree.createNode(.{}, .{ .parameter_list = .{
        .parameters = try tree.ownSlice(*AST.Node, &.{result}),
    } });

    const definition = try tree.createNode(.{}, .{ .function_definition = .{
        .callable = .{
            .declaration = .{ .name = "pay" },
            .parameters = parameters,
            .return_parameters = returns,
        },
        .state_mutability = .Payable,
    } });
    const internal = (try provider.functionFromDefinition(
        definition,
        .Internal,
    )).asFunction().?;
    try std.testing.expectEqual(Types.FunctionKind.Internal, internal.kind);
    try std.testing.expectEqual(Types.StateMutability.NonPayable, internal.state_mutability);
    try std.testing.expect(internal.declaration == definition);
    try std.testing.expectEqualStrings("amount", internal.parameter_names[0]);
    try std.testing.expectEqualStrings("ok", internal.return_parameter_names[0]);

    const event = try tree.createNode(.{}, .{ .event_definition = .{
        .callable = .{
            .declaration = .{ .name = "Paid" },
            .parameters = parameters,
        },
    } });
    const event_type = (try provider.functionFromEvent(event)).asFunction().?;
    try std.testing.expectEqual(Types.FunctionKind.Event, event_type.kind);
    try std.testing.expectEqual(@as(usize, 0), event_type.return_parameter_types.len);
    try std.testing.expect(event_type.declaration == event);

    const error_definition = try tree.createNode(.{}, .{ .error_definition = .{
        .callable = .{
            .declaration = .{ .name = "BadAmount" },
            .parameters = parameters,
        },
    } });
    const error_type = (try provider.functionFromError(error_definition)).asFunction().?;
    try std.testing.expectEqual(Types.FunctionKind.Error, error_type.kind);
    try std.testing.expectEqual(Types.StateMutability.Pure, error_type.state_mutability);
    try std.testing.expectEqual(@as(usize, 1), error_type.return_parameter_types.len);
    try std.testing.expect(error_type.return_parameter_types[0] ==
        (try provider.magic(.Error)));

    const function_type_name = try tree.createNode(.{}, .{ .function_type_name = .{
        .parameter_types = parameters,
        .return_types = returns,
        .visibility = .External,
        .state_mutability = .Payable,
    } });
    const named_type = (try provider.functionFromTypeName(function_type_name)).asFunction().?;
    try std.testing.expectEqual(Types.FunctionKind.External, named_type.kind);
    try std.testing.expectEqual(Types.StateMutability.Payable, named_type.state_mutability);
    try std.testing.expect(named_type.declaration == null);
    try std.testing.expectEqualStrings("", named_type.parameter_names[0]);
    try std.testing.expectEqualStrings("", named_type.return_parameter_names[0]);

    const scalar_member = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "plain" },
    } });
    (try ASTAnnotations.ensure(&tree, scalar_member)).variable_declaration.type_ref =
        provider.uint256();
    const array_member = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "items" },
    } });
    (try ASTAnnotations.ensure(&tree, array_member)).variable_declaration.type_ref =
        try provider.array(.Storage, provider.uint256());
    const bytes_member = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "payload" },
    } });
    (try ASTAnnotations.ensure(&tree, bytes_member)).variable_declaration.type_ref =
        provider.bytesStorage();
    const mapping_member = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "lookup" },
    } });
    (try ASTAnnotations.ensure(&tree, mapping_member)).variable_declaration.type_ref =
        try provider.mapping(provider.uint256(), "", provider.uint256(), "");
    const structure = try tree.createNode(.{}, .{ .struct_definition = .{
        .declaration = .{ .name = "Record" },
        .members = try tree.ownSlice(*AST.Node, &.{
            scalar_member,
            array_member,
            bytes_member,
            mapping_member,
        }),
    } });
    const records = try provider.array(
        .Storage,
        try provider.structType(structure, .Storage),
    );
    const getter_storage_type = try provider.mapping(
        provider.uint256(),
        "owner",
        records,
        "records",
    );
    const state_variable = try tree.createNode(.{}, .{ .variable_declaration = .{
        .declaration = .{ .name = "records", .visibility = .Public },
    } });
    (try ASTAnnotations.ensure(&tree, state_variable)).variable_declaration.type_ref =
        getter_storage_type;

    const getter = (try provider.functionFromVariable(state_variable)).asFunction().?;
    try std.testing.expectEqual(Types.FunctionKind.External, getter.kind);
    try std.testing.expectEqual(Types.StateMutability.View, getter.state_mutability);
    try std.testing.expectEqual(@as(usize, 2), getter.parameter_types.len);
    try std.testing.expectEqualStrings("owner", getter.parameter_names[0]);
    try std.testing.expectEqualStrings("", getter.parameter_names[1]);
    try std.testing.expectEqual(@as(usize, 2), getter.return_parameter_types.len);
    try std.testing.expectEqualStrings("plain", getter.return_parameter_names[0]);
    try std.testing.expectEqualStrings("payload", getter.return_parameter_names[1]);
    try std.testing.expectEqual(
        Types.DataLocation.Memory,
        getter.return_parameter_types[1].asReference().?.location,
    );
}

fn exerciseProviderInitialization(allocator: std.mem.Allocator) !void {
    var provider = try TypeProvider.init(allocator);
    defer provider.deinit();
    try std.testing.expect(provider.bool_type.payload == .Bool);
    try std.testing.expectEqual(@as(u16, 256), provider.integer_types[0][31].asInteger().?.bits);
}

test "provider initialization has one cleanup owner at every allocation failure" {
    try exerciseProviderInitialization(std.testing.allocator);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, exerciseProviderInitialization, .{});
}
