// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Item = evm.assembly_item.AssemblyItem;
const Classes = evm.expression_classes.ExpressionClasses;
const Observation = struct {
    kind: i32,
    instruction: ?u8,
    id: u32,
    opcode: u8,
    input_pointer: usize,
    input_length: usize,
    output_pointer: ?usize,
    values: ?[]const u32,
};

fn observe(classes: *const Classes, item: *const Item, arguments: []const u32, id: u32, opcode: u8) Observation {
    const result = classes.operationArguments(id, @fromBackingInt(@intCast(opcode)));
    return .{
        .kind = @backingInt(item.item_type),
        .instruction = if (item.instruction_value) |value| @backingInt(value) else null,
        .id = id,
        .opcode = opcode,
        .input_pointer = @intFromPtr(arguments.ptr),
        .input_length = arguments.len,
        .output_pointer = if (result) |slice| @intFromPtr(slice.ptr) else null,
        .values = result,
    };
}

// Live stack fixtures exercise only the actual readonly query. They are not
// interner-owned graph storage and must not be passed to its destructor.
pub fn main(init: std.process.Init) !void {
    var words = [_]u32{ 777, 99, 1, 5 };
    var item = Item.initInstruction(.ADD, .{});
    var descriptors = [_]evm.expression_classes.Expression{.{ .id = 0, .item = &item, .arguments = words[1..3], .sequence_number = 23 }};
    var classes = Classes.init(std.heap.page_allocator);
    classes.representatives = .fromOwnedSlice(&descriptors);
    var cases: [529]Observation = undefined;
    var count: usize = 0;
    for (0..256) |value| {
        const opcode: u8 = @intCast(value);
        item = Item.initInstruction(@fromBackingInt(@intCast(opcode)), .{});
        for ([_]u8{ opcode, opcode +% 1 }) |wanted| {
            cases[count] = observe(&classes, &item, descriptors[0].arguments, 0, wanted);
            count += 1;
        }
    }
    inline for (comptime @typeInfo(evm.assembly_item.AssemblyItemType).@"enum".field_names) |name| {
        const kind: evm.assembly_item.AssemblyItemType = @field(evm.assembly_item.AssemblyItemType, name);
        if (@backingInt(kind) != 1) {
            item = Item.initType(kind, 0, .{});
            cases[count] = observe(&classes, &item, descriptors[0].arguments, 0, 12);
            count += 1;
        }
    }
    for ([_]u32{ 1, 0xFFFFFFFE, 0xFFFFFFFF }) |id| {
        cases[count] = observe(&classes, &item, descriptors[0].arguments, id, 12);
        count += 1;
    }
    item = Item.initInstruction(.ADD, .{});
    descriptors[0].arguments = words[3..3];
    cases[count] = observe(&classes, &item, descriptors[0].arguments, 0, 1);
    count += 1;
    std.debug.assert(count == cases.len);
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(.{ .schema = "oksolc.operation-arguments-observations.v1", .zigVersion = builtin.zig_version_string, .mode = switch (builtin.mode) {
        .debug => "Debug",
        .safe => "ReleaseSafe",
        .fast => "ReleaseFast",
        .small => "ReleaseSmall",
    }, .backend = @tagName(builtin.zig_backend), .cases = cases }, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
