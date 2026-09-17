// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural fixed-size hash container from `FixedHash.h`.

const std = @import("std");

pub const ConstructFromStringType = enum {
    from_hex,
    from_binary,
};

pub const ConstructFromHashType = enum {
    align_left,
    align_right,
    fail_if_different,
};

pub const ParseError = error{InvalidHexCharacter};

pub fn FixedHash(comptime N: usize) type {
    if (N == 0) @compileError("FixedHash size must be nonzero");
    return struct {
        const Self = @This();

        pub const size = N;
        pub const Arith = @Int(.unsigned, N * 8);

        storage: [N]u8 = [_]u8{0} ** N,

        pub fn init() Self {
            return .{};
        }

        pub fn fromArray(value: [N]u8) Self {
            return .{ .storage = value };
        }

        pub fn fromBytes(
            input: []const u8,
            mismatch_behavior: ConstructFromHashType,
        ) Self {
            var result = init();
            if (input.len == N) {
                @memcpy(&result.storage, input);
                return result;
            }
            if (mismatch_behavior == .fail_if_different) return result;

            const count = @min(input.len, N);
            if (mismatch_behavior == .align_right) {
                @memcpy(result.storage[N - count ..], input[input.len - count ..]);
            } else {
                @memcpy(result.storage[0..count], input[0..count]);
            }
            return result;
        }

        pub fn fromHash(
            comptime M: usize,
            other: *const FixedHash(M),
            behavior: ConstructFromHashType,
        ) Self {
            var result = init();
            const count = @min(M, N);
            if (behavior == .align_right) {
                @memcpy(result.storage[N - count ..], other.storage[M - count ..]);
            } else {
                // C++ treats FailIfDifferent as left alignment for this
                // constructor, despite the enum name.
                @memcpy(result.storage[0..count], other.storage[0..count]);
            }
            return result;
        }

        pub fn fromInteger(value: Arith) Self {
            var result = init();
            std.mem.writeInt(Arith, &result.storage, value, .big);
            return result;
        }

        pub fn toInteger(self: *const Self) Arith {
            return std.mem.readInt(Arith, &self.storage, .big);
        }

        pub fn fromString(
            input: []const u8,
            input_type: ConstructFromStringType,
            mismatch_behavior: ConstructFromHashType,
        ) ParseError!Self {
            if (input_type == .from_binary) {
                return fromBytes(input, mismatch_behavior);
            }

            const digits = if (std.mem.startsWith(u8, input, "0x")) input[2..] else input;
            var decoded: [(N * 2 + 1) / 2]u8 = undefined;
            const needed = (digits.len + 1) / 2;
            if (needed > decoded.len) return fromBytes(&.{}, mismatch_behavior);
            var digit_index: usize = 0;
            var byte_index: usize = 0;
            if (digits.len % 2 != 0) {
                decoded[0] = try hexValue(digits[0]);
                digit_index = 1;
                byte_index = 1;
            }
            while (digit_index < digits.len) : (digit_index += 2) {
                decoded[byte_index] = (try hexValue(digits[digit_index])) << 4 |
                    try hexValue(digits[digit_index + 1]);
                byte_index += 1;
            }
            return fromBytes(decoded[0..needed], mismatch_behavior);
        }

        pub fn eql(self: *const Self, other: *const Self) bool {
            return std.mem.eql(u8, &self.storage, &other.storage);
        }

        pub fn lessThan(self: *const Self, other: *const Self) bool {
            return std.mem.order(u8, &self.storage, &other.storage) == .lt;
        }

        pub fn at(self: *Self, index: usize) *u8 {
            return &self.storage[index];
        }

        pub fn get(self: *const Self, index: usize) u8 {
            return self.storage[index];
        }

        pub fn bytes(self: *const Self) []const u8 {
            return &self.storage;
        }

        pub fn mutableBytes(self: *Self) []u8 {
            return &self.storage;
        }

        pub fn array(self: *const Self) *const [N]u8 {
            return &self.storage;
        }

        pub fn mutableArray(self: *Self) *[N]u8 {
            return &self.storage;
        }

        pub fn asBytes(self: *const Self) [N]u8 {
            return self.storage;
        }

        pub fn hex(self: *const Self) [N * 2]u8 {
            var output: [N * 2]u8 = undefined;
            const alphabet = "0123456789abcdef";
            for (self.storage, 0..) |byte, index| {
                output[index * 2] = alphabet[byte >> 4];
                output[index * 2 + 1] = alphabet[byte & 0x0f];
            }
            return output;
        }
    };
}

fn hexValue(character: u8) ParseError!u8 {
    return switch (character) {
        '0'...'9' => character - '0',
        'a'...'f' => character - 'a' + 10,
        'A'...'F' => character - 'A' + 10,
        else => error.InvalidHexCharacter,
    };
}

pub const H160 = FixedHash(20);
pub const H256 = FixedHash(32);
pub const h160 = H160;
pub const h256 = H256;

test "fixed hash construction preserves upstream alignment quirks" {
    const H8 = FixedHash(8);
    const H12 = FixedHash(12);
    const source = try H12.fromString("112233445566778899001122", .from_hex, .fail_if_different);
    const left = H8.fromHash(12, &source, .align_left);
    const right = H8.fromHash(12, &source, .align_right);
    const compatibility = H8.fromHash(12, &source, .fail_if_different);
    try std.testing.expectEqualStrings("1122334455667788", &(left.hex()));
    try std.testing.expectEqualStrings("5566778899001122", &(right.hex()));
    try std.testing.expect(left.eql(&compatibility));

    const mismatch = H8.fromBytes(&.{ 1, 2, 3 }, .fail_if_different);
    try std.testing.expectEqual(H8.init(), mismatch);
}

test "fixed hash converts arithmetic and odd hex big-endian" {
    const H32 = FixedHash(32);
    const value = H32.fromInteger(0x12340000);
    try std.testing.expectEqualStrings(
        "0000000000000000000000000000000000000000000000000000000012340000",
        &(value.hex()),
    );
    try std.testing.expectEqual(@as(u256, 0x12340000), value.toInteger());

    const H1 = FixedHash(1);
    const one = try H1.fromString("1", .from_hex, .fail_if_different);
    try std.testing.expectEqualStrings("01", &(one.hex()));
}
