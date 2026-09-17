// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Storage and transient-storage layout generation translated from
//! `StorageLayout.cpp`.

const std = @import("std");
const AST = @import("../ast/ast.zig");
const ASTImplementation = @import("../ast/ast.zig");
const Types = @import("../ast/types.zig");
const TypeBehavior = @import("../ast/types.zig");
const TypeProviderModule = @import("../ast/type_provider.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const JSON = @import("../../libsolutil/json.zig");

const Json = JSON.Json;

pub const StorageLayoutError = ASTImplementation.AstError || error{InvalidAst};

pub const StorageLayout = struct {
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    contract: ?*const AST.Node = null,
    types: Json = .{ .object = .empty },

    pub fn init(
        allocator: std.mem.Allocator,
        type_provider: *TypeProviderModule.TypeProvider,
        compatibility_ids: CompatibilityIdResolver,
    ) StorageLayout {
        return .{
            .allocator = allocator,
            .type_provider = type_provider,
            .compatibility_ids = compatibility_ids,
        };
    }

    /// Generates the exact Standard JSON layout for ordinary or transient
    /// storage. All returned strings and containers are owned by `allocator`.
    pub fn generate(
        self: *StorageLayout,
        contract: *const AST.Node,
        location: Types.DataLocation,
    ) StorageLayoutError!Json {
        if (self.contract != null or contract.nodeKind() != .contract_definition)
            return error.InvalidAst;
        if (location != .Storage and location != .Transient)
            return error.InvalidAst;
        self.contract = contract;
        self.types = .{ .object = .empty };

        const contract_type = try self.type_provider.contract(contract, false);
        const variables = try TypeBehavior.linearizedStateVariablesAlloc(
            self.allocator,
            contract_type.payload.Contract,
            location,
        );
        defer self.allocator.free(variables);

        var storage = std.json.Array.init(self.allocator); // zlinter-disable-current-line require_errdefer_dealloc - JSON graph uses caller-owned arena lifetime and transfers into the result
        for (variables) |entry|
            try storage.append(try self.generateVariable(
                entry.declaration,
                entry.slot,
                entry.byte_offset,
            ));

        var layout: Json = .{ .object = .empty };
        try layout.object.put(self.allocator, "storage", .{ .array = storage });
        try layout.object.put(self.allocator, "types", self.types);
        return layout;
    }

    fn generateVariable(
        self: *StorageLayout,
        variable: *const AST.Node,
        slot: u256,
        offset: u8,
    ) StorageLayoutError!Json {
        if (variable.nodeKind() != .variable_declaration) return error.InvalidAst;
        const contract = self.contract orelse return error.InvalidAst;
        const variable_type = try TypeBehavior.variableDeclarationType(variable);
        const type_key = try self.typeKeyName(variable_type);

        var entry: Json = .{ .object = .empty };
        try entry.object.put(
            self.allocator,
            "astId",
            .{ .integer = self.compatibility_ids.id(variable) orelse return error.InvalidAst },
        );
        try entry.object.put(
            self.allocator,
            "contract",
            .{ .string = try ASTImplementation.fullyQualifiedContractNameAlloc(
                self.allocator,
                contract,
            ) },
        );
        try entry.object.put(
            self.allocator,
            "label",
            .{ .string = variable.payload.variable_declaration.declaration.name },
        );
        try entry.object.put(self.allocator, "offset", .{ .integer = offset });
        try entry.object.put(
            self.allocator,
            "slot",
            .{ .string = try decimalAlloc(self.allocator, slot) },
        );
        try entry.object.put(self.allocator, "type", .{ .string = type_key });

        try self.generateType(variable_type);
        return entry;
    }

    fn generateType(
        self: *StorageLayout,
        type_ref: *const Types.Type,
    ) StorageLayoutError!void {
        const key = try self.typeKeyName(type_ref);
        if (self.types.object.get(key) != null) return;

        // Register before descending so recursive structs through mappings or
        // dynamic arrays terminate. Reacquiring/replacing the map entry after
        // recursion avoids retaining a pointer across hash-map growth.
        try self.types.object.put(self.allocator, key, .{ .object = .empty });

        const byte_count = std.math.mul(
            u256,
            @as(u256, try TypeBehavior.storageBytes(type_ref)),
            try TypeBehavior.storageSize(type_ref),
        ) catch return error.Overflow;
        var info: Json = .{ .object = .empty };

        switch (type_ref.payload) {
            .Struct => |structure| {
                const offsets = try TypeBehavior.structStorageOffsetsAlloc(
                    self.allocator,
                    structure,
                );
                defer self.allocator.free(offsets.offsets);
                if (structure.declaration.nodeKind() != .struct_definition or
                    offsets.offsets.len !=
                        structure.declaration.payload.struct_definition.members.len)
                    return error.InvalidAst;
                var members = std.json.Array.init(self.allocator);
                for (
                    structure.declaration.payload.struct_definition.members,
                    offsets.offsets,
                ) |member, maybe_offset| {
                    const offset = maybe_offset orelse return error.InvalidAst;
                    try members.append(try self.generateVariable(
                        member,
                        offset.slot,
                        offset.byte_offset,
                    ));
                }
                try putString(self.allocator, &info, "encoding", "inplace");
                try info.object.put(self.allocator, "members", .{ .array = members });
            },
            .Mapping => |mapping| {
                const key_type = try self.typeKeyName(mapping.key_type);
                const value_type = try self.typeKeyName(mapping.value_type);
                try self.generateType(mapping.key_type);
                try self.generateType(mapping.value_type);
                try putString(self.allocator, &info, "encoding", "mapping");
                try putString(self.allocator, &info, "key", key_type);
                try putString(self.allocator, &info, "value", value_type);
            },
            .Array => |array| {
                if (array.isByteArrayOrString()) {
                    try putString(self.allocator, &info, "encoding", "bytes");
                } else {
                    const base = try self.typeKeyName(array.base_type);
                    try self.generateType(array.base_type);
                    try putString(self.allocator, &info, "base", base);
                    try putString(
                        self.allocator,
                        &info,
                        "encoding",
                        if (array.isDynamicallySized()) "dynamic_array" else "inplace",
                    );
                }
            },
            else => {
                if (!TypeBehavior.isValueType(type_ref)) return error.InvalidAst;
                try putString(self.allocator, &info, "encoding", "inplace");
            },
        }

        try putString(
            self.allocator,
            &info,
            "label",
            try TypeBehavior.toStringAlloc(self.allocator, type_ref, true),
        );
        try putString(
            self.allocator,
            &info,
            "numberOfBytes",
            try decimalAlloc(self.allocator, byte_count),
        );
        try self.types.object.put(self.allocator, key, info);
    }

    fn typeKeyName(
        self: *StorageLayout,
        type_ref: *const Types.Type,
    ) StorageLayoutError![]u8 {
        const normalized = if (type_ref.asReference()) |reference|
            try self.type_provider.withLocationIfReference(
                reference.location,
                type_ref,
                false,
            )
        else
            type_ref;
        return TypeBehavior.compatibilityRichIdentifierAlloc(
            self.allocator,
            self.compatibility_ids,
            normalized,
        );
    }
};

pub fn generate(
    allocator: std.mem.Allocator,
    type_provider: *TypeProviderModule.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const AST.Node,
    location: Types.DataLocation,
) StorageLayoutError!Json {
    var generator = StorageLayout.init(allocator, type_provider, compatibility_ids);
    return generator.generate(contract, location);
}

fn decimalAlloc(
    allocator: std.mem.Allocator,
    value: anytype,
) std.mem.Allocator.Error![]u8 {
    return std.fmt.allocPrint(allocator, "{d}", .{value});
}

fn putString(
    allocator: std.mem.Allocator,
    object: *Json,
    key: []const u8,
    value: []const u8,
) std.mem.Allocator.Error!void {
    try object.object.put(allocator, key, .{ .string = value });
}
