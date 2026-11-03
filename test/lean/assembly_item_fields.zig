// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const nominal = @import("assembly_item_layout.zig");
const evm = @import("compiler").libevmasm;
const item = evm.assembly_item;
const Item = item.AssemblyItem;
const DebugData = @FieldType(Item, "debug_data");
const SourceLocation = @FieldType(DebugData, "native_location");

const Field = struct { name: []const u8, type: []const u8, offset: usize, bytes: usize, alignment: usize };
const EnumEntry = struct { name: []const u8, value: i32 };

const IntegerChild = struct { type: []const u8, bits: u16, signed: bool };

fn recordLayout(comptime T: type) struct { type: []const u8, bytes: usize, alignment: usize, fields: [@typeInfo(T).@"struct".field_names.len]Field } {
    var fields: [@typeInfo(T).@"struct".field_names.len]Field = undefined;
    inline for (comptime @typeInfo(T).@"struct".field_names, 0..) |name, index| {
        fields[index] = .{ .name = name, .type = @typeName(@FieldType(T, name)), .offset = @offsetOf(T, name), .bytes = @sizeOf(@FieldType(T, name)), .alignment = @alignOf(@FieldType(T, name)) };
    }
    return .{ .type = @typeName(T), .bytes = @sizeOf(T), .alignment = @alignOf(T), .fields = fields };
}

fn integerChild(comptime Optional: type) IntegerChild {
    const Child = @typeInfo(Optional).optional.child;
    const info = @typeInfo(Child).int;
    return .{ .type = @typeName(Child), .bits = info.bits, .signed = info.signedness == .signed };
}

const IntegerObservation = struct { pushed_value: ?u256, immutable_occurrences: ?usize };

fn integerObservations() [8]IntegerObservation {
    var value = Item.initPush(17, .{});
    var observations: [8]IntegerObservation = undefined;
    observations[0] = .{ .pushed_value = value.pushed_value, .immutable_occurrences = value.immutable_occurrences };
    const words = [_]?u256{ 0, 1, @as(u256, 1) << 255, (@as(u256, 1) << 255) + 17, std.math.maxInt(u256), null, 0 };
    const sizes = [_]?usize{ 0, 1, @as(usize, 1) << 63, (@as(usize, 1) << 63) + 17, std.math.maxInt(usize), null, 0 };
    for (words, sizes, 1..) |word, size, index| {
        value.pushed_value = word;
        value.immutable_occurrences = size;
        observations[index] = .{ .pushed_value = value.pushed_value, .immutable_occurrences = value.immutable_occurrences };
    }
    return observations;
}

const SliceObservation = struct { offset: usize, length: usize };
const VerbatimObservation = struct { arguments: usize, returns: usize, data: SliceObservation };
const LocationObservation = struct { start: i32, end: i32, source: ?SliceObservation };
const DebugObservation = struct { native: LocationObservation, origin: LocationObservation, ast_id: ?i64 };

fn locationObservation(location: SourceLocation, backing: []const u8) LocationObservation {
    return .{ .start = location.start, .end = location.end, .source = if (location.source_name) |name|
        .{ .offset = @intFromPtr(name.ptr) - @intFromPtr(backing.ptr), .length = name.len }
    else
        null };
}

fn verbatimObservation(payload: ?item.VerbatimBytecode, backing: []const u8) ?VerbatimObservation {
    return if (payload) |present| .{
        .arguments = present.arguments,
        .returns = present.return_variables,
        .data = .{ .offset = @intFromPtr(present.data.ptr) - @intFromPtr(backing.ptr), .length = present.data.len },
    } else null;
}

fn debugObservation(debug: DebugData, backing: []const u8) DebugObservation {
    return .{
        .native = locationObservation(debug.native_location, backing),
        .origin = locationObservation(debug.origin_location, backing),
        .ast_id = debug.ast_id,
    };
}

fn debugInput(index: usize, identity: ?i64, backing: []const u8) DebugData {
    return if (index == 0) .{} else .{
        .native_location = .{ .start = -1, .end = 17, .source_name = if (index == 6) null else backing[2..5] },
        .origin_location = .{ .start = std.math.minInt(i32), .end = std.math.maxInt(i32), .source_name = backing[7..7] },
        .ast_id = identity,
    };
}

// These stack-backed descriptors test field storage/copy only, not payload ownership.
fn verbatimObservations() [6]?VerbatimObservation {
    var backing = [_]u8{ 11, 22, 33, 44, 55, 66 };
    var value = Item.initPush(17, .{});
    const payloads = [_]?item.VerbatimBytecode{
        null,
        .{ .arguments = 0, .return_variables = 0, .data = backing[2..2] },
        .{ .arguments = 3, .return_variables = 2, .data = backing[1..4] },
        .{ .arguments = std.math.maxInt(usize), .return_variables = std.math.maxInt(usize), .data = backing[0..6] },
        null,
        .{ .arguments = 1, .return_variables = 0, .data = backing[5..5] },
    };
    var observations: [payloads.len]?VerbatimObservation = undefined;
    for (payloads, 0..) |payload, index| {
        if (index != 0) value.verbatim = payload;
        const copied = value;
        observations[index] = verbatimObservation(copied.verbatim, &backing);
    }
    return observations;
}

fn debugObservations() [8]DebugObservation {
    const backing = "native-origin";
    const identities = [_]?i64{ null, 0, -1, std.math.minInt(i64), std.math.maxInt(i64), 17, null, 0 };
    var observations: [identities.len]DebugObservation = undefined;
    for (identities, 0..) |identity, index| {
        const debug = debugInput(index, identity, backing);
        const value = Item.initInstruction(.ADD, debug);
        const copied = value;
        observations[index] = debugObservation(copied.debug_data, backing);
    }
    return observations;
}

const ItemObservation = struct {
    kind: i32,
    instruction: ?u8,
    data: u256,
    verbatim: ?VerbatimObservation,
    debug: DebugObservation,
    jump: i32,
    pushed: ?u256,
    immutable: ?usize,
    modifier: usize,
};

// Observe complete constructors after pointer assignment overwrites a populated
// destination. All backing remains alive; this does not transfer payload ownership.
fn initializerObservations() [6]ItemObservation {
    const names = "native-origin";
    var bytes = [_]u8{ 11, 22, 33, 44, 55, 66 };
    const sources = [_]Item{
        Item.initPush(0, .{}),
        Item.initPush(std.math.maxInt(u256), debugInput(1, std.math.maxInt(i64), names)),
        Item.initPush((@as(u256, 1) << 255) + 17, debugInput(1, -1, names)),
        Item.initInstruction(@fromBackingInt(@intCast(0)), .{}),
        Item.initInstruction(.ADD, debugInput(1, 0, names)),
        Item.initInstruction(@fromBackingInt(@intCast(255)), debugInput(1, std.math.minInt(i64), names)),
    };
    var observations: [sources.len]ItemObservation = undefined;
    for (sources, 0..) |source, index| {
        var target: Item = .{
            .item_type = .VerbatimBytecode,
            .instruction_value = .ADD,
            .data_value = 123,
            .verbatim = .{ .arguments = 3, .return_variables = 2, .data = &bytes },
            .debug_data = debugInput(6, 17, names),
            .jump_type = .OutOfFunction,
            .pushed_value = 99,
            .immutable_occurrences = 27,
            .modifier_depth = 19,
        };
        const destination = &target;
        destination.* = source;
        observations[index] = .{
            .kind = @backingInt(target.item_type),
            .instruction = if (target.instruction_value) |opcode| @backingInt(opcode) else null,
            .data = target.data_value,
            .verbatim = verbatimObservation(target.verbatim, &bytes),
            .debug = debugObservation(target.debug_data, names),
            .jump = @backingInt(target.jump_type),
            .pushed = target.pushed_value,
            .immutable = target.immutable_occurrences,
            .modifier = target.modifier_depth,
        };
    }
    return observations;
}

fn enumEntries(comptime T: type) [@typeInfo(T).@"enum".field_names.len]EnumEntry {
    var entries: [@typeInfo(T).@"enum".field_names.len]EnumEntry = undefined;
    inline for (comptime @typeInfo(T).@"enum".field_names, 0..) |name, index| {
        entries[index] = .{ .name = name, .value = @backingInt(@field(T, name)) };
    }
    return entries;
}

pub fn main(init: std.process.Init) !void {
    const operation = Item.initInstruction(.ADD, .{});
    var pushed = Item.initPush((@as(u256, 1) << 255) + 17, .{});
    pushed.jump_type = .OutOfFunction;
    pushed.modifier_depth = 19;
    const Instruction = @typeInfo(@TypeOf(operation.instruction_value)).optional.child;
    var instructions: [257]?u8 = undefined;
    instructions[0] = if (pushed.instruction_value) |opcode| @backingInt(opcode) else null;
    for (0..256) |value| {
        const native = Item.initInstruction(@fromBackingInt(@intCast(value)), .{});
        instructions[value + 1] = if (native.instruction_value) |opcode| @backingInt(opcode) else null;
    }
    const profile = .{
        .schema = "oksolc.assembly-item-fields.v5",
        .target = nominal.profile,
        .fields = recordLayout(Item).fields,
        .nested = .{ .verbatim = recordLayout(item.VerbatimBytecode), .debug_data = recordLayout(DebugData), .source_location = recordLayout(SourceLocation) },
        .itemTag = .{ .type = @typeName(@typeInfo(item.AssemblyItemType).@"enum".tag_type), .values = enumEntries(item.AssemblyItemType) },
        .jumpTag = .{ .type = @typeName(@typeInfo(item.JumpType).@"enum".tag_type), .values = enumEntries(item.JumpType) },
        .instruction = .{ .type = @typeName(Instruction), .tagType = @typeName(@typeInfo(Instruction).@"enum".tag_type), .exhaustive = @typeInfo(Instruction).@"enum".mode == .exhaustive },
        .integerOptionals = .{ .pushed_value = integerChild(@TypeOf(operation.pushed_value)), .immutable_occurrences = integerChild(@TypeOf(operation.immutable_occurrences)), .ast_id = integerChild(@FieldType(DebugData, "ast_id")) },
        .observations = .{
            .optionalInstructions = instructions,
            .optionalIntegers = integerObservations(),
            .verbatim = verbatimObservations(),
            .debug = debugObservations(),
            .initializers = initializerObservations(),
            .operation = .{ .kind = @backingInt(operation.item_type), .opcode = @backingInt(operation.instruction_value.?), .data = operation.data_value, .jump = @backingInt(operation.jump_type), .modifier = operation.modifier_depth },
            .pushed = .{ .kind = @backingInt(pushed.item_type), .opcodeAbsent = pushed.instruction_value == null, .data = pushed.data_value, .jump = @backingInt(pushed.jump_type), .modifier = pushed.modifier_depth },
        },
    };
    var buffer: [8192]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(profile, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
