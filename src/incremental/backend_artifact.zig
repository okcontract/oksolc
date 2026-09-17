// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Versioned, checksummed backend-artifact serialization.
//!
//! The wire format contains explicit fixed-width fields, never native Zig
//! layouts, pointers, arenas, or hash-table iteration order. Assembly trees
//! use the compiler's portable legacy-assembly JSON representation; linker
//! objects and source mappings use a compact binary encoding.

const std = @import("std");
const AssemblyModule = @import("../libevmasm/assembly.zig");
const Assembly = AssemblyModule.Assembly;
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const JSON = @import("../libsolutil/json.zig");
const Keccak = @import("../libsolutil/keccak256.zig");
const LinkerObjectModule = @import("../libevmasm/linker_object.zig");
const LinkerObject = LinkerObjectModule.LinkerObject;
const ObjectModule = @import("../libyul/object.zig");
const YulStackModule = @import("../libyul/yul_stack.zig");

const blueprint_magic = "OKBLUE\x00";
const creation_magic = "OKCREA\x00";
const deployed_magic = "OKDEPL\x00";
const linker_magic = "OKLINK\x00";
const metadata_magic = "OKMETA\x00";
const schema_version: u32 = 1;
const checksum_size = Keccak.H256.size;
const no_deployed_index = std.math.maxInt(u32);

pub const DecodeError = std.mem.Allocator.Error || error{
    Corrupt,
    IncompatibleSchema,
};

/// Deterministically records metadata by object-tree position. The payload is
/// both the metadata artifact and the input to its phase key.
pub fn encodeMetadataAlloc(
    allocator: std.mem.Allocator,
    object: *const ObjectModule.Object,
) ![]u8 {
    var encoder = Encoder.init(allocator);
    errdefer encoder.deinit();
    try encoder.writeBytes(metadata_magic);
    try encoder.writeInt(u32, schema_version);
    try encodeMetadataObject(&encoder, object);
    return encoder.finish();
}

/// Removes only `.metadata` auxiliary bytes from a lowered assembly tree.
/// Object children are matched by their deterministic source order.
pub fn stripMetadata(
    object: *const ObjectModule.Object,
    assembly: *Assembly,
) !void {
    var expected_offset: usize = 0;
    var object_index: usize = 0;
    for (object.sub_objects.items) |*node| switch (node.*) {
        .data => |*data| {
            if (!std.mem.eql(u8, data.name, ObjectModule.Object.metadataName())) continue;
            if (data.data.len > assembly.auxiliary_data.items.len -| expected_offset)
                return error.MetadataAssemblyMismatch;
            if (!std.mem.eql(
                u8,
                data.data,
                assembly.auxiliary_data.items[expected_offset..][0..data.data.len],
            )) return error.MetadataAssemblyMismatch;
            expected_offset += data.data.len;
        },
        .object => |child| {
            if (object_index >= assembly.subs.items.len)
                return error.MetadataAssemblyMismatch;
            try stripMetadata(child, assembly.subs.items[object_index]);
            object_index += 1;
        },
    };
    if (object_index != assembly.subs.items.len or
        expected_offset != assembly.auxiliary_data.items.len)
        return error.MetadataAssemblyMismatch;
    assembly.auxiliary_data.clearRetainingCapacity();
}

/// Applies the current request's metadata to a decoded metadata-free tree.
pub fn applyMetadata(
    object: *const ObjectModule.Object,
    assembly: *Assembly,
) !void {
    if (assembly.auxiliary_data.items.len != 0)
        return error.MetadataAssemblyMismatch;
    var object_index: usize = 0;
    for (object.sub_objects.items) |*node| switch (node.*) {
        .data => |*data| {
            if (std.mem.eql(u8, data.name, ObjectModule.Object.metadataName()))
                try assembly.auxiliary_data.appendSlice(assembly.allocator, data.data);
        },
        .object => |child| {
            if (object_index >= assembly.subs.items.len)
                return error.MetadataAssemblyMismatch;
            try applyMetadata(child, assembly.subs.items[object_index]);
            object_index += 1;
        },
    };
    if (object_index != assembly.subs.items.len)
        return error.MetadataAssemblyMismatch;
}

pub fn encodeBlueprintAlloc(
    allocator: std.mem.Allocator,
    pair: *const YulStackModule.AssemblyPair,
    source_indices: []const AssemblyModule.SourceIndex,
    evm_version: EVMVersion,
) ![]u8 {
    const root = pair.creation.get() orelse return error.MissingAssembly;
    const assembly_json = try assemblyJsonAlloc(allocator, root, source_indices);
    defer allocator.free(assembly_json);

    var encoder = Encoder.init(allocator);
    errdefer encoder.deinit();
    try encoder.writeBytes(blueprint_magic);
    try encoder.writeInt(u32, schema_version);
    try encoder.writeByte(@intCast(@intFromEnum(evm_version.version)));
    try encoder.writeInt(u32, try deployedIndexWire(pair));
    try encoder.writeSlice(assembly_json);
    try encodePortableAssemblyState(&encoder, root);
    return encoder.finish();
}

pub fn decodeBlueprintAlloc(
    allocator: std.mem.Allocator,
    encoded: []const u8,
    evm_version: EVMVersion,
) DecodeError!YulStackModule.AssemblyPair {
    var cursor = try verifiedCursor(encoded, blueprint_magic);
    try expectVersion(&cursor, evm_version);
    const deployed_index = try decodeDeployedIndex(try cursor.readInt(u32));
    const assembly_json = try cursor.readSlice();
    var result = try assemblyPairFromJsonAlloc(
        allocator,
        assembly_json,
        evm_version,
        deployed_index,
    );
    errdefer result.deinit();
    try decodePortableAssemblyState(
        allocator,
        &cursor,
        result.creation.get() orelse return error.Corrupt,
    );
    if (cursor.remaining() != 0) return error.Corrupt;
    return result;
}

pub fn encodeCreationAlloc(
    allocator: std.mem.Allocator,
    pair: *const YulStackModule.MachineAssemblyPair,
    source_indices: []const AssemblyModule.SourceIndex,
    evm_version: EVMVersion,
) ![]u8 {
    const root = pair.creation.assembly() orelse return error.MissingAssembly;
    const assembly_json = try assemblyJsonAlloc(allocator, root, source_indices);
    defer allocator.free(assembly_json);

    const deployed_index = try deployedIndexFromMachinePair(pair);

    var encoder = Encoder.init(allocator);
    errdefer encoder.deinit();
    try encoder.writeBytes(creation_magic);
    try encoder.writeInt(u32, schema_version);
    try encoder.writeByte(@intCast(@intFromEnum(evm_version.version)));
    try encoder.writeInt(u32, deployed_index);
    try encoder.writeSlice(assembly_json);
    try encodePortableAssemblyState(&encoder, root);
    try encodeMachineObject(&encoder, &pair.creation);
    return encoder.finish();
}

pub fn creationHasDeployed(
    encoded: []const u8,
    evm_version: EVMVersion,
) DecodeError!bool {
    var cursor = try verifiedCursor(encoded, creation_magic);
    try expectVersion(&cursor, evm_version);
    return (try decodeDeployedIndex(try cursor.readInt(u32))) != null;
}

pub fn encodeDeployedAlloc(
    allocator: std.mem.Allocator,
    object: *const YulStackModule.MachineAssemblyObject,
    evm_version: EVMVersion,
) ![]u8 {
    var encoder = Encoder.init(allocator);
    errdefer encoder.deinit();
    try encoder.writeBytes(deployed_magic);
    try encoder.writeInt(u32, schema_version);
    try encoder.writeByte(@intCast(@intFromEnum(evm_version.version)));
    try encodeMachineObject(&encoder, object);
    return encoder.finish();
}

pub fn decodeMachinePairAlloc(
    allocator: std.mem.Allocator,
    creation_encoded: []const u8,
    deployed_encoded: ?[]const u8,
    evm_version: EVMVersion,
) DecodeError!YulStackModule.MachineAssemblyPair {
    var creation_cursor = try verifiedCursor(creation_encoded, creation_magic);
    try expectVersion(&creation_cursor, evm_version);
    const deployed_index = try decodeDeployedIndex(try creation_cursor.readInt(u32));
    const assembly_json = try creation_cursor.readSlice();
    var assemblies = try assemblyPairFromJsonAlloc(
        allocator,
        assembly_json,
        evm_version,
        deployed_index,
    );
    defer assemblies.deinit();
    try decodePortableAssemblyState(
        allocator,
        &creation_cursor,
        assemblies.creation.get() orelse return error.Corrupt,
    );

    var result: YulStackModule.MachineAssemblyPair = .{};
    errdefer result.deinit();
    result.creation = try decodeMachineObject(allocator, &creation_cursor);
    if (creation_cursor.remaining() != 0) return error.Corrupt;
    result.creation.assembly_reference = assemblies.creation.take();

    if (deployed_index != null) {
        const payload = deployed_encoded orelse return error.Corrupt;
        var deployed_cursor = try verifiedCursor(payload, deployed_magic);
        try expectVersion(&deployed_cursor, evm_version);
        result.deployed = try decodeMachineObject(allocator, &deployed_cursor);
        if (deployed_cursor.remaining() != 0) return error.Corrupt;
        result.deployed.assembly_reference = assemblies.deployed.take();
    } else if (deployed_encoded != null) return error.Corrupt;
    return result;
}

pub fn encodeLinkerObjectAlloc(
    allocator: std.mem.Allocator,
    object: *const LinkerObject,
) ![]u8 {
    var encoder = Encoder.init(allocator);
    errdefer encoder.deinit();
    try encoder.writeBytes(linker_magic);
    try encoder.writeInt(u32, schema_version);
    try encodeLinkerObject(&encoder, object);
    return encoder.finish();
}

pub fn decodeLinkerObjectAlloc(
    allocator: std.mem.Allocator,
    encoded: []const u8,
) DecodeError!LinkerObject {
    var cursor = try verifiedCursor(encoded, linker_magic);
    var result = try decodeLinkerObject(allocator, &cursor);
    errdefer result.deinit(allocator);
    if (cursor.remaining() != 0) return error.Corrupt;
    return result;
}

fn encodeMetadataObject(encoder: *Encoder, object: *const ObjectModule.Object) !void {
    try encoder.writeString(object.name);
    var metadata_count: usize = 0;
    var object_count: usize = 0;
    for (object.sub_objects.items) |node| switch (node) {
        .data => |data| if (std.mem.eql(u8, data.name, ObjectModule.Object.metadataName())) {
            metadata_count += 1;
        },
        .object => object_count += 1,
    };
    try encoder.writeCount(metadata_count);
    for (object.sub_objects.items) |node| switch (node) {
        .data => |data| if (std.mem.eql(u8, data.name, ObjectModule.Object.metadataName()))
            try encoder.writeSlice(data.data),
        .object => {},
    };
    try encoder.writeCount(object_count);
    for (object.sub_objects.items) |node| switch (node) {
        .object => |child| try encodeMetadataObject(encoder, child),
        .data => {},
    };
}

fn encodePortableAssemblyState(encoder: *Encoder, assembly: *const Assembly) !void {
    try encoder.writeString(assembly.name());
    try encoder.writeByte(@intFromBool(assembly.isCreation()));
    try encoder.writeByte(@intFromBool(assembly.isInvalid()));
    try encoder.writeInt(u32, assembly.usedTagCount());
    try encoder.writeCount(assembly.subPathCount());
    for (0..assembly.subPathCount()) |index| {
        const sub_path = assembly.subPathAt(index);
        try encoder.writeInt(u64, sub_path.id.toInt());
        try encoder.writeCount(sub_path.path.len);
        for (sub_path.path) |component|
            try encoder.writeInt(u64, component.toInt());
    }
    var verbatim_count: usize = 0;
    for (assembly.itemsConst()) |item|
        if (item.item_type == .VerbatimBytecode) {
            verbatim_count += 1;
        };
    try encoder.writeCount(verbatim_count);
    for (assembly.itemsConst(), 0..) |item, index| {
        if (item.item_type != .VerbatimBytecode) continue;
        try encoder.writeUsize(index);
        try encoder.writeUsize(item.arguments());
        try encoder.writeUsize(item.returnValues());
    }
    var pushed_value_count: usize = 0;
    var immutable_occurrence_count: usize = 0;
    for (assembly.itemsConst()) |item| {
        if (item.pushedValue() != null) pushed_value_count += 1;
        if (item.immutableOccurrences() != null) immutable_occurrence_count += 1;
    }
    try encoder.writeCount(pushed_value_count);
    for (assembly.itemsConst(), 0..) |item, index| {
        const pushed_value = item.pushedValue() orelse continue;
        try encoder.writeUsize(index);
        try encoder.writeInt(u256, pushed_value.*);
    }
    try encoder.writeCount(immutable_occurrence_count);
    for (assembly.itemsConst(), 0..) |item, index| {
        const occurrences = item.immutableOccurrences() orelse continue;
        try encoder.writeUsize(index);
        try encoder.writeUsize(occurrences);
    }
    try encoder.writeCount(assembly.namedTagCount());
    for (0..assembly.namedTagCount()) |index| {
        const tag = assembly.namedTagAt(index);
        try encoder.writeString(tag.name);
        try encoder.writeUsize(tag.id);
        try encoder.writeOptionalUsize(tag.source_id);
        try encoder.writeUsize(tag.params);
        try encoder.writeUsize(tag.returns);
    }
    try encoder.writeCount(assembly.subs.items.len);
    for (assembly.subs.items) |sub_assembly|
        try encodePortableAssemblyState(encoder, sub_assembly);
}

fn decodePortableAssemblyState(
    allocator: std.mem.Allocator,
    cursor: *Cursor,
    assembly: *Assembly,
) DecodeError!void {
    const name = try cursor.readString();
    if (try cursor.readFlag() != assembly.isCreation()) return error.Corrupt;
    const invalid = try cursor.readFlag();
    assembly.setName(name) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
    };
    if (invalid) assembly.markAsInvalid();

    assembly.restoreUsedTagCount(try cursor.readInt(u32)) catch
        return error.Corrupt;
    assembly.clearSubPaths();
    const sub_path_count = try cursor.readCount();
    if (sub_path_count > cursor.remaining()) return error.Corrupt;
    for (0..sub_path_count) |_| {
        const id = AssemblyModule.SubAssemblyID.init(try cursor.readInt(u64));
        const component_count = try cursor.readCount();
        if (component_count > cursor.remaining() / @sizeOf(u64)) return error.Corrupt;
        const path = try allocator.alloc(
            AssemblyModule.SubAssemblyID,
            component_count,
        );
        defer allocator.free(path);
        for (path) |*component|
            component.* = AssemblyModule.SubAssemblyID.init(try cursor.readInt(u64));
        assembly.restoreSubPath(id, path) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.Corrupt,
        };
    }

    const verbatim_count = try cursor.readCount();
    var expected_verbatim_count: usize = 0;
    for (assembly.itemsConst()) |item|
        if (item.item_type == .VerbatimBytecode) {
            expected_verbatim_count += 1;
        };
    if (verbatim_count != expected_verbatim_count) return error.Corrupt;
    var previous_verbatim_index: ?usize = null;
    for (0..verbatim_count) |_| {
        const item_index = try cursor.readUsize();
        if (item_index >= assembly.itemsConst().len or
            (previous_verbatim_index != null and previous_verbatim_index.? >= item_index))
            return error.Corrupt;
        previous_verbatim_index = item_index;
        assembly.items().items[item_index].restoreVerbatimArity(
            try cursor.readUsize(),
            try cursor.readUsize(),
        ) catch return error.Corrupt;
    }

    const pushed_value_count = try cursor.readCount();
    if (pushed_value_count > assembly.itemsConst().len) return error.Corrupt;
    var previous_pushed_value_index: ?usize = null;
    for (0..pushed_value_count) |_| {
        const item_index = try cursor.readUsize();
        if (item_index >= assembly.itemsConst().len or
            (previous_pushed_value_index != null and
                previous_pushed_value_index.? >= item_index) or
            assembly.itemsConst()[item_index].item_type != .PushSubSize)
            return error.Corrupt;
        previous_pushed_value_index = item_index;
        assembly.items().items[item_index].setPushedValue(try cursor.readInt(u256));
    }

    const immutable_occurrence_count = try cursor.readCount();
    if (immutable_occurrence_count > assembly.itemsConst().len) return error.Corrupt;
    var previous_immutable_index: ?usize = null;
    for (0..immutable_occurrence_count) |_| {
        const item_index = try cursor.readUsize();
        if (item_index >= assembly.itemsConst().len or
            (previous_immutable_index != null and previous_immutable_index.? >= item_index) or
            assembly.itemsConst()[item_index].item_type != .AssignImmutable)
            return error.Corrupt;
        previous_immutable_index = item_index;
        assembly.items().items[item_index].setImmutableOccurrences(
            try cursor.readUsize(),
        );
    }

    const named_tag_count = try cursor.readCount();
    if (named_tag_count > cursor.remaining()) return error.Corrupt;
    for (0..named_tag_count) |_| {
        assembly.restoreNamedTag(.{
            .name = try cursor.readString(),
            .id = try cursor.readUsize(),
            .source_id = try cursor.readOptionalUsize(),
            .params = try cursor.readUsize(),
            .returns = try cursor.readUsize(),
        }) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return error.Corrupt,
        };
    }

    const sub_count = try cursor.readCount();
    if (sub_count != assembly.subs.items.len) return error.Corrupt;
    for (assembly.subs.items) |sub_assembly|
        try decodePortableAssemblyState(allocator, cursor, sub_assembly);
}

fn encodeMachineObject(
    encoder: *Encoder,
    object: *const YulStackModule.MachineAssemblyObject,
) !void {
    if (object.bytecode) |*bytecode| {
        try encoder.writeByte(1);
        try encodeLinkerObject(encoder, bytecode);
    } else try encoder.writeByte(0);
    if (object.source_mappings) |source_mappings| {
        try encoder.writeByte(1);
        try encoder.writeSlice(source_mappings);
    } else try encoder.writeByte(0);
}

fn decodeMachineObject(
    allocator: std.mem.Allocator,
    cursor: *Cursor,
) DecodeError!YulStackModule.MachineAssemblyObject {
    var result: YulStackModule.MachineAssemblyObject = .{ .allocator = allocator };
    errdefer result.deinit();
    result.bytecode = switch (try cursor.readFlag()) {
        false => null,
        true => try decodeLinkerObject(allocator, cursor),
    };
    result.source_mappings = switch (try cursor.readFlag()) {
        false => null,
        true => try allocator.dupe(u8, try cursor.readSlice()),
    };
    return result;
}

fn encodeLinkerObject(encoder: *Encoder, object: *const LinkerObject) !void {
    try encoder.writeSlice(object.bytecode.items);

    try encoder.writeCount(object.link_references.items.len);
    for (object.link_references.items) |reference| {
        try encoder.writeUsize(reference.offset);
        try encoder.writeString(reference.library_name);
    }

    try encoder.writeCount(object.immutable_references.items.len);
    for (object.immutable_references.items) |reference| {
        try encoder.writeInt(u256, reference.hash);
        try encoder.writeString(reference.references.identifier);
        try encoder.writeCount(reference.references.offsets.items.len);
        for (reference.references.offsets.items) |offset|
            try encoder.writeUsize(offset);
    }

    try encoder.writeUsize(object.code_section_location.start);
    try encoder.writeUsize(object.code_section_location.end);
    try encoder.writeCount(object.code_section_location.instruction_locations.items.len);
    for (object.code_section_location.instruction_locations.items) |location| {
        try encoder.writeUsize(location.start);
        try encoder.writeUsize(location.end);
        try encoder.writeUsize(location.assembly_item_index);
    }

    try encoder.writeCount(object.function_debug_data.items.len);
    for (object.function_debug_data.items) |entry| {
        try encoder.writeString(entry.name);
        try encoder.writeOptionalUsize(entry.data.bytecode_offset);
        try encoder.writeOptionalUsize(entry.data.instruction_index);
        try encoder.writeOptionalUsize(entry.data.source_id);
        try encoder.writeUsize(entry.data.params);
        try encoder.writeUsize(entry.data.returns);
    }
}

fn decodeLinkerObject(
    allocator: std.mem.Allocator,
    cursor: *Cursor,
) DecodeError!LinkerObject {
    var result: LinkerObject = .{};
    errdefer result.deinit(allocator);
    try result.bytecode.appendSlice(allocator, try cursor.readSlice());

    const link_count = try cursor.readCount();
    if (link_count > cursor.remaining()) return error.Corrupt;
    try result.link_references.ensureTotalCapacity(allocator, link_count);
    for (0..link_count) |_| {
        const offset = try cursor.readUsize();
        const name = try cursor.readOwnedString(allocator);
        errdefer allocator.free(name);
        if (result.link_references.items.len != 0 and
            result.link_references.items[result.link_references.items.len - 1].offset >= offset)
            return error.Corrupt;
        if (offset > result.bytecode.items.len or result.bytecode.items.len - offset < 20)
            return error.Corrupt;
        result.link_references.appendAssumeCapacity(.{
            .offset = offset,
            .library_name = name,
        });
    }

    const immutable_count = try cursor.readCount();
    if (immutable_count > cursor.remaining()) return error.Corrupt;
    try result.immutable_references.ensureTotalCapacity(allocator, immutable_count);
    for (0..immutable_count) |_| {
        const hash = try cursor.readInt(u256);
        const identifier = try cursor.readOwnedString(allocator);
        var references: LinkerObjectModule.ImmutableRefs = .{ .identifier = identifier };
        errdefer references.deinit(allocator);
        const offset_count = try cursor.readCount();
        if (offset_count > cursor.remaining()) return error.Corrupt;
        try references.offsets.ensureTotalCapacity(allocator, offset_count);
        for (0..offset_count) |_| {
            const offset = try cursor.readUsize();
            if (offset > result.bytecode.items.len or result.bytecode.items.len - offset < 32)
                return error.Corrupt;
            references.offsets.appendAssumeCapacity(offset);
        }
        if (result.immutable_references.items.len != 0 and
            result.immutable_references.items[result.immutable_references.items.len - 1].hash >= hash)
            return error.Corrupt;
        result.immutable_references.appendAssumeCapacity(.{
            .hash = hash,
            .references = references,
        });
    }

    result.code_section_location.start = try cursor.readUsize();
    result.code_section_location.end = try cursor.readUsize();
    if (result.code_section_location.start > result.code_section_location.end or
        result.code_section_location.end > result.bytecode.items.len)
        return error.Corrupt;
    const location_count = try cursor.readCount();
    if (location_count > cursor.remaining()) return error.Corrupt;
    try result.code_section_location.instruction_locations.ensureTotalCapacity(
        allocator,
        location_count,
    );
    for (0..location_count) |_| {
        const location: LinkerObjectModule.InstructionLocation = .{
            .start = try cursor.readUsize(),
            .end = try cursor.readUsize(),
            .assembly_item_index = try cursor.readUsize(),
        };
        if (location.start > location.end or location.end > result.bytecode.items.len)
            return error.Corrupt;
        result.code_section_location.instruction_locations.appendAssumeCapacity(location);
    }

    const function_count = try cursor.readCount();
    if (function_count > cursor.remaining()) return error.Corrupt;
    try result.function_debug_data.ensureTotalCapacity(allocator, function_count);
    for (0..function_count) |_| {
        const name = try cursor.readOwnedString(allocator);
        errdefer allocator.free(name);
        if (result.function_debug_data.items.len != 0 and
            std.mem.order(
                u8,
                result.function_debug_data.items[result.function_debug_data.items.len - 1].name,
                name,
            ) != .lt) return error.Corrupt;
        result.function_debug_data.appendAssumeCapacity(.{
            .name = name,
            .data = .{
                .bytecode_offset = try cursor.readOptionalUsize(),
                .instruction_index = try cursor.readOptionalUsize(),
                .source_id = try cursor.readOptionalUsize(),
                .params = try cursor.readUsize(),
                .returns = try cursor.readUsize(),
            },
        });
    }
    return result;
}

fn assemblyJsonAlloc(
    allocator: std.mem.Allocator,
    assembly: *const Assembly,
    source_indices: []const AssemblyModule.SourceIndex,
) ![]u8 {
    var json = try assembly.assemblyJSONAlloc(allocator, source_indices, true);
    defer json.deinit();
    return JSON.jsonCompactPrintAlloc(allocator, &json.value);
}

fn assemblyPairFromJsonAlloc(
    allocator: std.mem.Allocator,
    assembly_json: []const u8,
    evm_version: EVMVersion,
    deployed_index: ?usize,
) DecodeError!YulStackModule.AssemblyPair {
    var parsed = try JSON.jsonParseStrict(allocator, assembly_json);
    defer parsed.deinit();
    const root_json = switch (parsed) {
        .document => |*document| document.rootConst(),
        .failure => return error.Corrupt,
    };
    const root = Assembly.fromJSONForVersion(
        allocator,
        root_json,
        evm_version,
    ) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return error.Corrupt,
    };
    errdefer root.destroy();
    return YulStackModule.AssemblyPair.initOwnedRoot(
        allocator,
        root,
        deployed_index,
    ) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return error.Corrupt,
    };
}

fn deployedIndexWire(pair: *const YulStackModule.AssemblyPair) !u32 {
    const deployed_index = try pair.deployedIndex() orelse return no_deployed_index;
    return std.math.cast(u32, deployed_index) orelse error.ArtifactTooLarge;
}

fn deployedIndexFromMachinePair(
    pair: *const YulStackModule.MachineAssemblyPair,
) !u32 {
    const root = pair.creation.assembly() orelse return error.MissingAssembly;
    const deployed = pair.deployed.assembly() orelse return no_deployed_index;
    for (root.subs.items, 0..) |candidate, index|
        if (candidate == deployed)
            return std.math.cast(u32, index) orelse error.ArtifactTooLarge;
    return error.DeployObjectNotFound;
}

fn decodeDeployedIndex(value: u32) DecodeError!?usize {
    if (value == no_deployed_index) return null;
    return std.math.cast(usize, value) orelse error.Corrupt;
}

fn expectVersion(cursor: *Cursor, expected: EVMVersion) DecodeError!void {
    const encoded = try cursor.readByte();
    if (encoded != @as(u8, @intCast(@intFromEnum(expected.version))))
        return error.Corrupt;
}

fn verifiedCursor(encoded: []const u8, expected_magic: []const u8) DecodeError!Cursor {
    const minimum_size = expected_magic.len + @sizeOf(u32) + checksum_size;
    if (encoded.len < minimum_size) return error.Corrupt;
    const checksum_offset = encoded.len - checksum_size;
    const actual = Keccak.keccak256(encoded[0..checksum_offset]);
    if (!std.mem.eql(u8, actual.bytes(), encoded[checksum_offset..]))
        return error.Corrupt;
    var cursor: Cursor = .{ .bytes = encoded[0..checksum_offset] };
    if (!std.mem.eql(u8, try cursor.readBytes(expected_magic.len), expected_magic))
        return error.Corrupt;
    if (try cursor.readInt(u32) != schema_version)
        return error.IncompatibleSchema;
    return cursor;
}

const Encoder = struct {
    allocator: std.mem.Allocator,
    bytes: std.ArrayList(u8) = .empty,

    fn init(allocator: std.mem.Allocator) Encoder {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *Encoder) void {
        self.bytes.deinit(self.allocator);
        self.* = undefined;
    }

    fn writeByte(self: *Encoder, value: u8) !void {
        try self.bytes.append(self.allocator, value);
    }

    fn writeBytes(self: *Encoder, value: []const u8) !void {
        try self.bytes.appendSlice(self.allocator, value);
    }

    fn writeInt(self: *Encoder, comptime T: type, value: T) !void {
        var encoded: [@sizeOf(T)]u8 = undefined;
        std.mem.writeInt(T, &encoded, value, .big);
        try self.writeBytes(&encoded);
    }

    fn writeCount(self: *Encoder, value: usize) !void {
        try self.writeInt(u32, std.math.cast(u32, value) orelse return error.ArtifactTooLarge);
    }

    fn writeUsize(self: *Encoder, value: usize) !void {
        try self.writeInt(u64, @intCast(value));
    }

    fn writeSlice(self: *Encoder, value: []const u8) !void {
        try self.writeInt(u64, @intCast(value.len));
        try self.writeBytes(value);
    }

    fn writeString(self: *Encoder, value: []const u8) !void {
        if (!std.unicode.utf8ValidateSlice(value)) return error.InvalidUtf8;
        try self.writeCount(value.len);
        try self.writeBytes(value);
    }

    fn writeOptionalUsize(self: *Encoder, value: ?usize) !void {
        if (value) |present| {
            try self.writeByte(1);
            try self.writeUsize(present);
        } else try self.writeByte(0);
    }

    fn finish(self: *Encoder) ![]u8 {
        const checksum = Keccak.keccak256(self.bytes.items);
        try self.writeBytes(checksum.bytes());
        const result = try self.bytes.toOwnedSlice(self.allocator);
        self.* = undefined;
        return result;
    }
};

const Cursor = struct {
    bytes: []const u8,
    offset: usize = 0,

    fn remaining(self: Cursor) usize {
        return self.bytes.len - self.offset;
    }

    fn readByte(self: *Cursor) DecodeError!u8 {
        if (self.offset == self.bytes.len) return error.Corrupt;
        defer self.offset += 1;
        return self.bytes[self.offset];
    }

    fn readFlag(self: *Cursor) DecodeError!bool {
        return switch (try self.readByte()) {
            0 => false,
            1 => true,
            else => error.Corrupt,
        };
    }

    fn readBytes(self: *Cursor, count: usize) DecodeError![]const u8 {
        if (count > self.remaining()) return error.Corrupt;
        defer self.offset += count;
        return self.bytes[self.offset..][0..count];
    }

    fn readArray(self: *Cursor, comptime count: usize) DecodeError![count]u8 {
        var result: [count]u8 = undefined;
        @memcpy(&result, try self.readBytes(count));
        return result;
    }

    fn readInt(self: *Cursor, comptime T: type) DecodeError!T {
        return std.mem.readInt(T, &(try self.readArray(@sizeOf(T))), .big);
    }

    fn readCount(self: *Cursor) DecodeError!usize {
        return std.math.cast(usize, try self.readInt(u32)) orelse error.Corrupt;
    }

    fn readUsize(self: *Cursor) DecodeError!usize {
        return std.math.cast(usize, try self.readInt(u64)) orelse error.Corrupt;
    }

    fn readSlice(self: *Cursor) DecodeError![]const u8 {
        const length = try self.readUsize();
        return self.readBytes(length);
    }

    fn readOwnedString(
        self: *Cursor,
        allocator: std.mem.Allocator,
    ) DecodeError![]u8 {
        return allocator.dupe(u8, try self.readString());
    }

    fn readString(self: *Cursor) DecodeError![]const u8 {
        const value = try self.readBytes(try self.readCount());
        if (!std.unicode.utf8ValidateSlice(value)) return error.Corrupt;
        return value;
    }

    fn readOptionalUsize(self: *Cursor) DecodeError!?usize {
        return if (try self.readFlag()) try self.readUsize() else null;
    }
};

test "backend artifact codecs round-trip metadata, assemblies, and linker state" {
    const Diagnostics = @import("../liblangutil/diagnostics.zig");
    const EVMDialect = @import("../libyul/backends/evm/evm_dialect.zig");
    const ObjectParser = @import("../libyul/object_parser.zig").ObjectParser;

    const allocator = std.testing.allocator;
    const evm_version = EVMVersion.init(.Cancun);
    var dialect = try EVMDialect.EVMDialect.init(allocator, evm_version, true);
    defer dialect.deinit();
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const object = (try ObjectParser.parseSource(
        allocator,
        "object \"A\" { code { stop() } object \"A_deployed\" { code { mstore(0, 1) return(0, 32) } object \"Nested\" { code { stop() } } object \"NestedTwo\" { code { stop() } } data \".metadata\" hex\"aabb\" } }",
        "A.yul",
        &reporter,
        dialect.dialect(),
    )).?;
    defer object.destroy();

    const metadata = try encodeMetadataAlloc(allocator, object);
    defer allocator.free(metadata);
    try std.testing.expect(metadata.len > metadata_magic.len + checksum_size);

    const assembly = try Assembly.create(allocator, evm_version, true, "A");
    var assembly_owned = true;
    defer if (assembly_owned) assembly.destroy();
    const deployed = try Assembly.create(allocator, evm_version, false, "A_deployed");
    var deployed_owned = true;
    defer if (deployed_owned) deployed.destroy();
    const function_tag = try deployed.namedTag("f()", 1, 1, 7);
    _ = try deployed.append(function_tag);
    try deployed.appendVerbatim(&.{0xaa}, 1, 2);
    _ = try deployed.newTag();
    const used_tag_count = deployed.usedTagCount();
    try deployed.appendToAuxiliaryData(&.{ 0xaa, 0xbb });
    const nested = try Assembly.create(allocator, evm_version, false, "Nested");
    var nested_owned = true;
    defer if (nested_owned) nested.destroy();
    try deployed.subs.append(allocator, nested);
    nested_owned = false;
    const nested_two = try Assembly.create(allocator, evm_version, false, "NestedTwo");
    var nested_two_owned = true;
    defer if (nested_two_owned) nested_two.destroy();
    try deployed.subs.append(allocator, nested_two);
    nested_two_owned = false;
    try assembly.subs.append(allocator, deployed);
    deployed_owned = false;
    const second_nested_path = [_]AssemblyModule.SubAssemblyID{
        .init(0),
        .init(1),
    };
    const second_nested_path_id = try assembly.encodeSubPath(&second_nested_path);
    const nested_path = [_]AssemblyModule.SubAssemblyID{
        .init(0),
        .init(0),
    };
    const nested_path_id = try assembly.encodeSubPath(&nested_path);
    _ = try assembly.append(assembly.newPushSubSize(second_nested_path_id));
    _ = try assembly.append(assembly.newPushSubSize(nested_path_id));
    _ = try assembly.append(try function_tag.toSubAssemblyTag(.init(0)));
    var pair = YulStackModule.AssemblyPair.initOwnedRoot(
        allocator,
        assembly,
        0,
    ) catch |err| {
        return err;
    };
    assembly_owned = false;
    defer pair.deinit();
    try stripMetadata(object, pair.creation.get().?);
    const blueprint = try encodeBlueprintAlloc(
        allocator,
        &pair,
        &.{.{ .source_name = "A.yul", .index = 0 }},
        evm_version,
    );
    defer allocator.free(blueprint);
    var decoded = try decodeBlueprintAlloc(allocator, blueprint, evm_version);
    defer decoded.deinit();
    const decoded_creation = decoded.creation.get().?;
    try applyMetadata(object, decoded_creation);
    try std.testing.expectEqualStrings("A", decoded_creation.name());
    const decoded_deployed = decoded.deployed.get().?;
    try std.testing.expectEqualStrings("A_deployed", decoded_deployed.name());
    try std.testing.expectEqual(used_tag_count, decoded_deployed.usedTagCount());
    const decoded_path = try decoded_creation.decodeSubPathAlloc(
        allocator,
        nested_path_id,
    );
    defer allocator.free(decoded_path);
    try std.testing.expectEqualSlices(
        AssemblyModule.SubAssemblyID,
        &nested_path,
        decoded_path,
    );
    const decoded_second_path = try decoded_creation.decodeSubPathAlloc(
        allocator,
        second_nested_path_id,
    );
    defer allocator.free(decoded_second_path);
    try std.testing.expectEqualSlices(
        AssemblyModule.SubAssemblyID,
        &second_nested_path,
        decoded_second_path,
    );
    try std.testing.expectEqualSlices(
        u8,
        &.{ 0xaa, 0xbb },
        decoded_deployed.auxiliary_data.items,
    );
    try std.testing.expectEqual(@as(usize, 1), decoded_deployed.namedTagCount());
    var found_verbatim = false;
    for (decoded_deployed.itemsConst()) |item| {
        if (item.item_type != .VerbatimBytecode) continue;
        found_verbatim = true;
        try std.testing.expectEqual(@as(usize, 1), item.arguments());
        try std.testing.expectEqual(@as(usize, 2), item.returnValues());
    }
    try std.testing.expect(found_verbatim);
    const decoded_bytecode = try decoded_deployed.assemble();
    try std.testing.expectEqual(@as(usize, 1), decoded_bytecode.function_debug_data.items.len);
    try std.testing.expectEqualStrings("f()", decoded_bytecode.function_debug_data.items[0].name);
    try applyMetadata(object, pair.creation.get().?);
    const expected_creation = try pair.creation.get().?.assemble();
    const actual_creation = try decoded_creation.assemble();
    try std.testing.expect(!expected_creation.lessThan(actual_creation));
    try std.testing.expect(!actual_creation.lessThan(expected_creation));

    var linker: LinkerObject = .{};
    defer linker.deinit(allocator);
    try linker.bytecode.appendNTimes(allocator, 0, 64);
    try linker.putLinkReference(allocator, 1, "A.yul:L");
    try linker.putImmutableReference(allocator, 9, "immutable", &.{24});
    linker.code_section_location = .{ .start = 0, .end = 64 };
    try linker.code_section_location.instruction_locations.append(allocator, .{
        .start = 0,
        .end = 1,
        .assembly_item_index = 2,
    });
    try linker.putFunctionDebugData(allocator, "f()", .{
        .bytecode_offset = 3,
        .instruction_index = 2,
        .source_id = 7,
        .params = 1,
        .returns = 1,
    });
    const encoded_linker = try encodeLinkerObjectAlloc(allocator, &linker);
    defer allocator.free(encoded_linker);
    var round_tripped = try decodeLinkerObjectAlloc(allocator, encoded_linker);
    defer round_tripped.deinit(allocator);
    try std.testing.expect(!linker.lessThan(&round_tripped));
    try std.testing.expect(!round_tripped.lessThan(&linker));
    try std.testing.expectEqual(@as(usize, 1), round_tripped.function_debug_data.items.len);

    const corrupted = try allocator.dupe(u8, encoded_linker);
    defer allocator.free(corrupted);
    corrupted[linker_magic.len + @sizeOf(u32)] ^= 1;
    try std.testing.expectError(
        error.Corrupt,
        decodeLinkerObjectAlloc(allocator, corrupted),
    );
}
