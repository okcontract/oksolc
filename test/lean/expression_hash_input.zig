// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
const std = @import("std");
const builtin = @import("builtin");
const evm = @import("compiler").libevmasm;
const Map = @FieldType(evm.expression_classes.ExpressionClasses, "expressions");
const Key = @FieldType(Map.KV, "key");
const Context = @typeInfo(@TypeOf(Map.getOrPutContext)).@"fn".param_types[3].?;
const lengths = [_]usize{ 0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 31, 32, 33, 65 };
const Case = struct {
    length: usize,
    // u16 keeps JSON's representation numeric rather than treating u8 slices
    // as strings. Every element below is widened from an observed native byte.
    inputs: [5][]const u16,
    native_hash: u64,
    replayed_hash: u64,
};
const Capture = struct {
    schema: []const u8 = "oksolc.expression-hash-input.v1",
    endian: []const u8 = @tagName(builtin.cpu.arch.endian()),
    usize_bytes: usize = @sizeOf(usize),
    scalar_bytes: [4]usize = .{ @sizeOf(@FieldType(Key, "item_type")), @sizeOf(u8), @sizeOf(u256), @sizeOf(u32) },
    cases: [lengths.len]Case,
};

/// The caller owns an arena until serialization finishes. This captures input
/// bytes and a native consistency observation, not a proof of Wyhash execution.
pub fn observe(arena: std.mem.Allocator) !Capture {
    var values: [65]u32 = undefined;
    for (&values, 0..) |*value, i| value.* = @as(u32, @intCast(i)) *% 0x9e3779b9;
    std.mem.doNotOptimizeAway(&values);
    var cases: [lengths.len]Case = undefined;
    for (lengths, &cases) |len, *result| {
        const key: Key = .{
            .item_type = .Push,
            .instruction = 171,
            .data = 11 * (@as(u256, 1) << 192) + 7 * (@as(u256, 1) << 128) + 5 * (@as(u256, 1) << 64) + 3,
            .arguments = values[0..len],
            .sequence_number = 0x12345678,
        };
        const inputs = [5][]const u8{
            std.mem.asBytes(&key.item_type),
            std.mem.asBytes(&key.instruction),
            std.mem.asBytes(&key.data),
            std.mem.sliceAsBytes(key.arguments),
            std.mem.asBytes(&key.sequence_number),
        };
        var observed: [5][]const u16 = undefined;
        var replay = std.hash.Wyhash.init(0);
        for (inputs, &observed) |bytes, *copy| {
            const owned = try arena.alloc(u16, bytes.len);
            for (bytes, owned) |byte, *target| target.* = byte;
            copy.* = owned;
            replay.update(bytes);
        }
        result.* = .{ .length = len, .inputs = observed, .native_hash = (Context{}).hash(key), .replayed_hash = replay.final() };
    }
    return .{ .cases = cases };
}
