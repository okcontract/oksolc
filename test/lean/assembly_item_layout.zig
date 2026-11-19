// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const AssemblyItem = @import("compiler").libevmasm.assembly_item.AssemblyItem;

pub const profile = .{
    .schema = "oksolc.assembly-item-layout.v1",
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
    .name = @typeName(AssemblyItem),
    .bytes = @sizeOf(AssemblyItem),
    .alignment = @alignOf(AssemblyItem),
};

/// Capture the nominal allocation extent without inventing a field layout.
pub fn main(init: std.process.Init) !void {
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(profile, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
