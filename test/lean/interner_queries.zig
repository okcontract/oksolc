// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Item = evm.assembly_item.AssemblyItem;
const Kind = evm.assembly_item.AssemblyItemType;
const Instruction = evm.instruction.Instruction;

const Result = enum { deterministic, nondeterministic, assemblyException };
const Observation = struct { kind: i32, instruction: ?u8, result: Result };

fn observe(kind: Kind, opcode: ?u8) Observation {
    const item: Item = .{ .item_type = kind, .instruction_value = if (opcode) |op| @as(Instruction, @fromBackingInt(@intCast(op))) else null };
    const classified = evm.semantic_information.isDeterministic(&item);
    const result: Result = if (classified) |yes|
        if (yes) .deterministic else .nondeterministic
    else |err| switch (err) {
        error.AssemblyException => .assemblyException,
    };
    return .{ .kind = @backingInt(kind), .instruction = opcode, .result = result };
}

/// Exhaust every opcode, all native item tags and the early error's optional
/// shapes. Do not execute assertion-violating items: Lean checks their rejection.
pub fn main(init: std.process.Init) !void {
    var cases: [525]Observation = undefined;
    var count: usize = 0;
    inline for (comptime @typeInfo(Kind).@"enum".field_names) |name| {
        const kind: Kind = @field(Kind, name);
        if (kind == .Operation or kind == .VerbatimBytecode) {
            for (0..256) |op| {
                cases[count] = observe(kind, @intCast(op));
                count += 1;
            }
        }
        if (kind != .Operation) {
            cases[count] = observe(kind, null);
            count += 1;
        }
    }
    std.debug.assert(count == cases.len);
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(.{
        .schema = "oksolc.interner-query-observations.v1",
        .zigVersion = builtin.zig_version_string,
        .mode = switch (builtin.mode) {
            .debug => "Debug",
            .safe => "ReleaseSafe",
            .fast => "ReleaseFast",
            .small => "ReleaseSmall",
        },
        .backend = @tagName(builtin.zig_backend),
        .cases = cases[0..count],
    }, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
