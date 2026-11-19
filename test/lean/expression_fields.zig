// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Expression = evm.expression_classes.Expression;

const Fields = struct { item_pointer: usize, arguments_pointer: usize, arguments_length: usize, id: u32, sequence_number: u32 };

fn read(expression: *const Expression) Fields {
    return .{ .item_pointer = @intFromPtr(expression.item), .arguments_pointer = @intFromPtr(expression.arguments.ptr), .arguments_length = expression.arguments.len, .id = expression.id, .sequence_number = expression.sequence_number };
}

pub fn main(init: std.process.Init) !void {
    var item = evm.assembly_item.AssemblyItem.initInstruction(.SUB, .{});
    var arguments = [_]u32{ 777, 99, 1, 5 };
    const initial: Expression = .{ .item = &item, .arguments = arguments[1..3], .id = 17, .sequence_number = 23 };
    var descriptors = [_]Expression{ initial, initial };
    const before = [_]Fields{ read(&descriptors[0]), read(&descriptors[1]) };
    descriptors[1].id = 19;
    descriptors[1].sequence_number = 29;
    const after = [_]Fields{ read(&descriptors[0]), read(&descriptors[1]) };
    const profile = .{
        .schema = "oksolc.expression-field-observations.v1",
        .zigVersion = builtin.zig_version_string,
        .mode = switch (builtin.mode) {
            .debug => "Debug",
            .safe => "ReleaseSafe",
            .fast => "ReleaseFast",
            .small => "ReleaseSmall",
        },
        .backend = @tagName(builtin.zig_backend),
        .item_pointer = @intFromPtr(&item),
        .argument_allocation_pointer = @intFromPtr(&arguments),
        .argument_allocation_length = arguments.len,
        .descriptor_pointers = [_]usize{ @intFromPtr(&descriptors[0]), @intFromPtr(&descriptors[1]) },
        .descriptor_bytes = @sizeOf(Expression),
        .descriptor_alignment = @alignOf(Expression),
        .before = before,
        .after = after,
        .borrowed_arguments = descriptors[1].arguments,
    };
    var buffer: [4096]u8 = undefined;
    var output = std.Io.File.stdout().writer(init.io, &buffer);
    try std.json.Stringify.value(profile, .{}, &output.interface);
    try output.interface.writeByte('\n');
    try output.interface.flush();
}
