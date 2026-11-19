// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");

const Inner = extern struct { byte: u8, word: u64 };
const Record = extern struct { tiny: u8, big: u64, child: Inner, tail: [3]u8, count: usize };
const Packed = packed struct(u16) { low: u8, high: u8 };
const Tagged = struct { comptime tag: u8 = 7, value: u64 };
const Ordinal = enum(u32) { zero, one };
const Signed = enum(i32) { negative = -7, positive = 11 };
const Open = enum(u16) { one = 1, maximum = 65535, _ };
const EnumRecord = extern struct { marker: u8, tag: Signed };

fn initial(seed: u64) Record {
    var result = Record{ .tiny = undefined, .big = 0, .child = .{ .byte = undefined, .word = 9 }, .tail = undefined, .count = 0 };
    result.big = seed;
    return result;
}

export fn initialize(result: *Record) void {
    result.* = initial(0);
}

// Exercise both the fixed-index and payload-index field-pointer encodings.
export fn touch(result: *Record, value: u64) u64 {
    result.tiny = 1;
    result.big = value;
    result.child.byte = 2;
    result.tail[0] = 3;
    result.count = value;
    return result.count;
}

export fn packed_read(record: *const Packed) u8 {
    return record.low;
}

export fn tagged_read(record: *const Tagged) u64 {
    return record.value;
}

export fn ordinal_bytes(value: *const Ordinal) *align(4) const [4]u8 {
    return std.mem.asBytes(value);
}

export fn open_bytes(value: *const Open) *align(2) const [2]u8 {
    return std.mem.asBytes(value);
}

fn signed_view(value: *const Signed) []const u8 {
    return std.mem.asBytes(value);
}

export fn enum_byte(record: *const EnumRecord, index: usize) u8 {
    return signed_view(&record.tag)[index];
}

test "independent native layout and initialized fields" {
    try std.testing.expectEqual(48, @sizeOf(Record));
    try std.testing.expectEqual(8, @alignOf(Record));
    inline for (.{ "tiny", "big", "child", "tail", "count" }, .{ 0, 8, 16, 32, 40 }) |name, offset| {
        try std.testing.expectEqual(offset, @offsetOf(Record, name));
    }
    try std.testing.expectEqual(16, @sizeOf(Inner));
    try std.testing.expectEqual(8, @offsetOf(Inner, "word"));
    var record: Record = undefined;
    initialize(&record);
    try std.testing.expectEqual(0, record.big);
    try std.testing.expectEqual(9, record.child.word);
    try std.testing.expectEqual(0, record.count);
    try std.testing.expectEqual(123, touch(&record, 123));
    try std.testing.expectEqual(1, record.tiny);
    try std.testing.expectEqual(2, record.child.byte);
    try std.testing.expectEqual(3, record.tail[0]);
    const packed_value: Packed = .{ .low = 5, .high = 6 };
    try std.testing.expectEqual(5, packed_read(&packed_value));
    const tagged: Tagged = .{ .value = 17 };
    try std.testing.expectEqual(17, tagged_read(&tagged));
}

test "enum backing values and byte views retain native representation" {
    try std.testing.expectEqual(8, @sizeOf(EnumRecord));
    try std.testing.expectEqual(4, @alignOf(EnumRecord));
    try std.testing.expectEqual(4, @offsetOf(EnumRecord, "tag"));
    const ordinal: Ordinal = .one;
    try std.testing.expectEqualSlices(u8, &.{ 1, 0, 0, 0 }, ordinal_bytes(&ordinal));
    const open: Open = @fromBackingInt(@as(u16, 65534));
    try std.testing.expectEqualSlices(u8, &.{ 254, 255 }, open_bytes(&open));
    const record: EnumRecord = .{ .marker = 77, .tag = .negative };
    const expected = [_]u8{ 249, 255, 255, 255 };
    for (expected, 0..) |byte, index| try std.testing.expectEqual(byte, enum_byte(&record, index));
    const positive: Signed = .positive;
    try std.testing.expectEqualSlices(u8, &.{ 11, 0, 0, 0 }, signed_view(&positive));
}
