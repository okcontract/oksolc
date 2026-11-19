// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Expression = evm.expression_classes.Expression;
const Owner = evm.expression_classes.ExpressionClasses;
const Header = @FieldType(Owner, "representatives");
const Cache = @FieldType(Owner, "expressions");
const MetadataPointer = @typeInfo(@FieldType(Cache, "metadata")).optional.child;
const Metadata = @typeInfo(MetadataPointer).pointer.child;
const Lock = @FieldType(Cache, "pointer_stability");
comptime {
    std.debug.assert(@FieldType(Header, "pointer_stability") == Lock);
}
const LockState = @FieldType(Lock, "state");
const Field = struct { name: []const u8, type: []const u8, offset: usize, bytes: usize, alignment: usize };
const EnumEntry = struct { name: []const u8, value: usize };

fn enumEntries(comptime T: type) [@typeInfo(T).@"enum".field_names.len]EnumEntry {
    var entries: [@typeInfo(T).@"enum".field_names.len]EnumEntry = undefined;
    inline for (comptime @typeInfo(T).@"enum".field_names, 0..) |name, index| {
        entries[index] = .{ .name = name, .value = @backingInt(@field(T, name)) };
    }
    return entries;
}

pub fn fieldsOf(comptime T: type) [@typeInfo(T).@"struct".field_names.len]Field {
    const native_fields = comptime @typeInfo(T).@"struct".field_names;
    var fields: [native_fields.len]Field = undefined;
    inline for (native_fields, 0..) |name, index| {
        fields[index] = .{ .name = name, .type = @typeName(@FieldType(T, name)), .offset = @offsetOf(T, name), .bytes = @sizeOf(@FieldType(T, name)), .alignment = @alignOf(@FieldType(T, name)) };
    }
    return fields;
}

const Target = struct {
    schema: []const u8,
    zigVersion: []const u8 = builtin.zig_version_string,
    arch: []const u8 = @tagName(builtin.target.cpu.arch),
    os: []const u8 = @tagName(builtin.target.os.tag),
    osVersionRange: @TypeOf(builtin.target.os.versionRange()) = builtin.target.os.versionRange(),
    abi: []const u8 = @tagName(builtin.target.abi),
    cpu: []const u8 = builtin.target.cpu.model.name,
    cpuFeatures: @TypeOf(builtin.target.cpu.features.ints) = builtin.target.cpu.features.ints,
    endianness: []const u8 = @tagName(builtin.target.cpu.arch.endian()),
    mode: []const u8 = switch (builtin.mode) {
        .debug => "Debug",
        .safe => "ReleaseSafe",
        .fast => "ReleaseFast",
        .small => "ReleaseSmall",
    },
    backend: []const u8 = @tagName(builtin.zig_backend),
    pointerBits: usize = @bitSizeOf(usize),
    name: []const u8,
    bytes: usize,
    alignment: usize,
};

pub fn target(comptime T: type, schema: []const u8) Target {
    return .{
        .schema = schema,
        .name = @typeName(T),
        .bytes = @sizeOf(T),
        .alignment = @alignOf(T),
    };
}

pub fn main(init: std.process.Init) !void {
    const profile = .{
        .schema = "oksolc.representative-array-layout.v5",
        .target = target(Header, "oksolc.representative-header-layout.v1"),
        .fields = fieldsOf(Header),
        .element = .{ .name = @typeName(Expression), .bytes = @sizeOf(Expression), .alignment = @alignOf(Expression) },
        .owner = .{ .target = target(Owner, "oksolc.expression-owner-layout.v1"), .fields = fieldsOf(Owner) },
        .cache = .{
            .target = target(Cache, "oksolc.expression-map-layout.v1"),
            .fields = fieldsOf(Cache),
            .metadata = .{
                .pointer = .{ .name = @typeName(MetadataPointer), .bytes = @sizeOf(MetadataPointer), .alignment = @alignOf(MetadataPointer), .is_const = @typeInfo(MetadataPointer).pointer.attrs.@"const", .is_allowzero = @typeInfo(MetadataPointer).pointer.attrs.@"allowzero", .size = @tagName(@typeInfo(MetadataPointer).pointer.size) },
                .child = .{ .name = @typeName(Metadata), .bytes = @sizeOf(Metadata), .alignment = @alignOf(Metadata) },
            },
            .lock = .{ .fields = fieldsOf(Lock), .state_bits = @bitSizeOf(LockState), .exhaustive = @typeInfo(LockState).@"enum".mode == .exhaustive, .states = enumEntries(LockState), .initial = @backingInt((Lock{}).state) },
        },
    };
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(profile, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
