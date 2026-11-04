// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Expression = evm.expression_classes.Expression;
const Item = evm.assembly_item.AssemblyItem;

const Field = struct { name: []const u8, type: []const u8, offset: usize, bytes: usize, alignment: usize };

pub fn main(init: std.process.Init) !void {
    const native_fields = comptime @typeInfo(Expression).@"struct".field_names;
    var fields: [native_fields.len]Field = undefined;
    inline for (native_fields, 0..) |name, index| {
        fields[index] = .{ .name = name, .type = @typeName(@FieldType(Expression, name)), .offset = @offsetOf(Expression, name), .bytes = @sizeOf(@FieldType(Expression, name)), .alignment = @alignOf(@FieldType(Expression, name)) };
    }
    const profile = .{
        .schema = "oksolc.expression-field-layout.v1",
        .target = .{
            .schema = "oksolc.expression-layout.v1",
            .zigVersion = builtin.zig_version_string,
            .arch = @tagName(builtin.target.cpu.arch),
            .os = @tagName(builtin.target.os.tag),
            .osVersionRange = builtin.target.os.versionRange(),
            .abi = @tagName(builtin.target.abi),
            .cpu = builtin.target.cpu.model.name,
            .cpuFeatures = builtin.target.cpu.features.ints,
            .endianness = @tagName(builtin.target.cpu.arch.endian()),
            .mode = switch (builtin.mode) {
                .debug => "Debug",
                .safe => "ReleaseSafe",
                .fast => "ReleaseFast",
                .small => "ReleaseSmall",
            },
            .backend = @tagName(builtin.zig_backend),
            .pointerBits = @bitSizeOf(usize),
            .name = @typeName(Expression),
            .bytes = @sizeOf(Expression),
            .alignment = @alignOf(Expression),
        },
        .fields = fields,
        .item = .{ .name = @typeName(Item), .bytes = @sizeOf(Item), .alignment = @alignOf(Item) },
    };
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(profile, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
