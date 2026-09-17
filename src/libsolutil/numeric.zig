// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Numeric compatibility layer for `Numeric.cpp`.
//!
//! Fixed-width EVM arithmetic uses Zig integers. Unbounded values use the
//! ownership-explicit native Zig big-integer implementation.

const std = @import("std");
const BigIntModule = @import("big_int");

pub const BigInt = BigIntModule.BigInt;
pub const bigint = BigInt;
pub const U160 = u160;
pub const U256 = u256;
pub const S256 = i256;
pub const U512 = u512;

pub fn u2s(value: u256) i256 {
    const sign_boundary = @as(u256, 1) << 255;
    if (value < sign_boundary) return @intCast(value);
    return std.math.minInt(i256) + @as(i256, @intCast(value - sign_boundary));
}

pub fn s2u(value: i256) u256 {
    if (value >= 0) return @intCast(value);
    const sign_boundary = @as(u256, 1) << 255;
    return sign_boundary + @as(u256, @intCast(value - std.math.minInt(i256)));
}

pub fn exp256(base_value: u256, exponent_value: u256) u256 {
    var base = base_value;
    var exponent = exponent_value;
    var result: u256 = 1;
    while (exponent != 0) : (exponent >>= 1) {
        if ((exponent & 1) != 0) result *%= base;
        base *%= base;
    }
    return result;
}

pub const PrecisionError = error{NegativeMantissa};

pub fn fitsPrecisionBaseX(
    mantissa: *const BigInt,
    log2_of_base: f64,
    exponent: u32,
) PrecisionError!bool {
    if (mantissa.isZero()) return true;
    if (mantissa.isNegative()) return error.NegativeMantissa;

    const bit_length = mantissa.bitLength();
    const bits_max: usize = 4096;
    const most_significant_bit = bit_length - 1;
    if (most_significant_bit > bits_max) return false;

    const exponent_bits = @floor(@as(f64, @floatFromInt(exponent)) * log2_of_base);
    if (!std.math.isFinite(exponent_bits)) return exponent_bits < 0;
    const bits_needed = @as(f64, @floatFromInt(most_significant_bit)) + exponent_bits + 1;
    return bits_needed <= @as(f64, @floatFromInt(bits_max));
}

fn requireUnsigned(comptime T: type) void {
    const info = @typeInfo(T);
    if (info != .int or info.int.signedness != .unsigned) {
        @compileError("big-endian fixed integer helpers require an unsigned integer type");
    }
}

/// Writes `value` big-endian, truncating high bytes or zero-extending exactly
/// like the templated C++ helper.
pub fn toBigEndian(comptime T: type, value: T, output: []u8) void {
    comptime requireUnsigned(T);
    var remaining = value;
    var index = output.len;
    while (index != 0) {
        index -= 1;
        output[index] = @truncate(remaining);
        remaining >>= 8;
    }
}

/// Reads the low `@bitSizeOf(T)` bits of a big-endian byte stream.
pub fn fromBigEndian(comptime T: type, input: []const u8) T {
    comptime requireUnsigned(T);
    var result: T = 0;
    for (input) |byte| result = (result << 8) | @as(T, byte);
    return result;
}

pub fn numberEncodingSize(comptime T: type, value: T) usize {
    comptime requireUnsigned(T);
    if (value == 0) return 0;
    return (@as(usize, @intCast(std.math.log2_int(T, value))) + 8) / 8;
}

pub fn toCompactBigEndianAlloc(
    comptime T: type,
    allocator: std.mem.Allocator,
    value: T,
    minimum: usize,
) std.mem.Allocator.Error![]u8 {
    const length = @max(minimum, numberEncodingSize(T, value));
    const result = try allocator.alloc(u8, length);
    toBigEndian(T, value, result);
    return result;
}

pub fn toBigEndian256(value: u256) [32]u8 {
    var result: [32]u8 = undefined;
    toBigEndian(u256, value, &result);
    return result;
}

fn hexAlloc(allocator: std.mem.Allocator, bytes: []const u8) std.mem.Allocator.Error![]u8 {
    const result = try allocator.alloc(u8, bytes.len * 2);
    const alphabet = "0123456789abcdef";
    for (bytes, 0..) |byte, index| {
        result[index * 2] = alphabet[byte >> 4];
        result[index * 2 + 1] = alphabet[byte & 0x0f];
    }
    return result;
}

pub fn toHex256Alloc(
    allocator: std.mem.Allocator,
    value: u256,
) std.mem.Allocator.Error![]u8 {
    const bytes = toBigEndian256(value);
    return hexAlloc(allocator, &bytes);
}

pub fn toCompactHexWithPrefixAlloc(
    comptime T: type,
    allocator: std.mem.Allocator,
    value: T,
) std.mem.Allocator.Error![]u8 {
    const bytes = try toCompactBigEndianAlloc(T, allocator, value, 1);
    defer allocator.free(bytes);
    const output = try allocator.alloc(u8, 2 + bytes.len * 2);
    @memcpy(output[0..2], "0x");
    const alphabet = "0123456789abcdef";
    for (bytes, 0..) |byte, index| {
        output[2 + index * 2] = alphabet[byte >> 4];
        output[3 + index * 2] = alphabet[byte & 0x0f];
    }
    return output;
}

pub fn formatNumberU256Alloc(
    allocator: std.mem.Allocator,
    value: u256,
) std.mem.Allocator.Error![]u8 {
    if (value > 0x1000000) {
        return toCompactHexWithPrefixAlloc(u256, allocator, value);
    }
    return std.fmt.allocPrint(allocator, "{d}", .{value});
}

pub const FormatBigIntError = std.mem.Allocator.Error || error{
    InvalidBase,
};

pub fn formatNumberBigIntAlloc(
    allocator: std.mem.Allocator,
    value: *const BigInt,
) FormatBigIntError![]u8 {
    var absolute = value.absolute();
    defer absolute.deinit();
    if (absolute.compareUnsigned(0x1000000) != .gt) {
        return value.toStringAlloc(allocator, 10);
    }

    const magnitude = try absolute.toMagnitudeBigEndianAlloc(allocator);
    defer allocator.free(magnitude);
    const prefix: []const u8 = if (value.isNegative()) "-0x" else "0x";
    const output = try allocator.alloc(u8, prefix.len + magnitude.len * 2);
    @memcpy(output[0..prefix.len], prefix);
    const alphabet = "0123456789abcdef";
    for (magnitude, 0..) |byte, index| {
        output[prefix.len + index * 2] = alphabet[byte >> 4];
        output[prefix.len + index * 2 + 1] = alphabet[byte & 0x0f];
    }
    return output;
}

test "signed and unsigned EVM words round-trip without bit casts" {
    const cases = [_]u256{
        0,
        1,
        (@as(u256, 1) << 255) - 1,
        @as(u256, 1) << 255,
        std.math.maxInt(u256),
    };
    for (cases) |value| try std.testing.expectEqual(value, s2u(u2s(value)));
    try std.testing.expectEqual(std.math.minInt(i256), u2s(@as(u256, 1) << 255));
    try std.testing.expectEqual(@as(i256, -1), u2s(std.math.maxInt(u256)));
}

test "exp256 and endian helpers use fixed-width modular behavior" {
    try std.testing.expectEqual(@as(u256, 1), exp256(0, 0));
    try std.testing.expectEqual(@as(u256, 1024), exp256(2, 10));
    try std.testing.expectEqual(@as(u256, 0), exp256(2, 256));

    var short: [2]u8 = undefined;
    toBigEndian(u32, 0x123456, &short);
    try std.testing.expectEqualSlices(u8, &.{ 0x34, 0x56 }, &short);
    try std.testing.expectEqual(@as(u16, 0x3456), fromBigEndian(u16, &.{ 0x12, 0x34, 0x56 }));
}

test "formatting follows the C++ decimal cutoff and even-byte hex" {
    const decimal = try formatNumberU256Alloc(std.testing.allocator, 0x1000000);
    defer std.testing.allocator.free(decimal);
    try std.testing.expectEqualStrings("16777216", decimal);

    const hexadecimal = try formatNumberU256Alloc(std.testing.allocator, 0x7ffffff);
    defer std.testing.allocator.free(hexadecimal);
    try std.testing.expectEqualStrings("0x07ffffff", hexadecimal);

    var negative = try BigInt.parse(std.testing.allocator, "-16777217", 10);
    defer negative.deinit();
    const negative_text = try formatNumberBigIntAlloc(std.testing.allocator, &negative);
    defer std.testing.allocator.free(negative_text);
    try std.testing.expectEqualStrings("-0x01000001", negative_text);
}

test "precision gate uses unbounded native integer bit lengths" {
    var one = BigInt.initUnsigned(1);
    defer one.deinit();
    try std.testing.expect(try fitsPrecisionBaseX(&one, 1.0, 4095));
    try std.testing.expect(!(try fitsPrecisionBaseX(&one, 1.0, 4096)));

    var zero = BigInt.init();
    defer zero.deinit();
    try std.testing.expect(try fitsPrecisionBaseX(&zero, 1000.0, std.math.maxInt(u32)));
}
