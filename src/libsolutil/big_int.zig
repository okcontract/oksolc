// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Ownership-explicit arbitrary-precision integers backed by Zig's standard
//! library.
//!
//! `BigInt` is an owner value. It must not be copied after initialization;
//! use `clone` for a second owner and `take` to transfer the value. Every live
//! owner must be paired with `deinit`. A moved-from value may only be
//! deinitialized or replaced.
//!
//! Parsed immutable values may use their caller's allocator. Derived values
//! use `std.heap.smp_allocator` so arithmetic remains safe when compiler work
//! is distributed across threads. Allocation failure in an operation that was
//! historically infallible under GMP retains the same process-fatal policy.

const std = @import("std");

const Native = std.math.big.int.Managed;
const NativeConst = std.math.big.int.Const;
const Limb = std.math.big.Limb;
const limb_bits = @bitSizeOf(Limb);
const derived_allocator = std.heap.smp_allocator;

pub const ParseError = std.mem.Allocator.Error || error{
    InvalidBase,
    InvalidInteger,
};

pub const ConversionError = std.mem.Allocator.Error || error{
    NegativeValue,
    ValueTooLarge,
};

fn outOfMemory() noreturn {
    @panic("out of memory during arbitrary-precision arithmetic");
}

fn digitValue(character: u8, base: u8) ?u8 {
    const value: u8 = if (character >= '0' and character <= '9')
        character - '0'
    else if (character >= 'A' and character <= 'Z')
        character - 'A' + 10
    else if (character >= 'a' and character <= 'z')
        if (base <= 36) character - 'a' + 10 else character - 'a' + 36
    else
        return null;
    return if (value < base) value else null;
}

pub const BigInt = struct {
    const Self = @This();
    const BinaryOperation = enum { add, sub, mul, gcd, bit_and, bit_or, bit_xor };

    raw: Native,
    owns_raw: bool = true,

    fn initWithAllocator(allocator: std.mem.Allocator) std.mem.Allocator.Error!Self {
        return .{ .raw = try Native.init(allocator) };
    }

    fn initSet(value: anytype) Self {
        const raw = Native.initSet(derived_allocator, value) catch outOfMemory();
        return .{ .raw = raw };
    }

    pub fn init() Self {
        return initWithAllocator(derived_allocator) catch outOfMemory();
    }

    pub fn initUnsigned(value: u64) Self {
        return initSet(value);
    }

    pub fn initSigned(value: i64) Self {
        return initSet(value);
    }

    pub fn fromBigEndian(bytes: []const u8) Self {
        var result = init();
        var offset: usize = 0;
        while (offset < bytes.len) {
            const chunk_length = @min(@as(usize, 8), bytes.len - offset);
            var chunk: u64 = 0;
            for (bytes[offset .. offset + chunk_length]) |byte| {
                chunk = (chunk << 8) | byte;
            }
            if (offset == 0) {
                result.raw.set(chunk) catch outOfMemory();
            } else {
                result.raw.shiftLeft(&result.raw, chunk_length * 8) catch outOfMemory();
                result.raw.addScalar(&result.raw, chunk) catch outOfMemory();
            }
            offset += chunk_length;
        }
        return result;
    }

    pub fn fromU256(value: u256) Self {
        return initSet(value);
    }

    pub fn parse(
        allocator: std.mem.Allocator,
        digits: []const u8,
        base: u8,
    ) ParseError!Self {
        if (base != 0 and (base < 2 or base > 62)) return error.InvalidBase;

        var contains_whitespace = false;
        for (digits) |character| {
            if (std.ascii.isWhitespace(character)) {
                contains_whitespace = true;
                break;
            }
        }

        var compact_storage: ?[]u8 = null;
        defer if (compact_storage) |storage| allocator.free(storage);
        const text: []const u8 = if (!contains_whitespace)
            digits
        else compact: {
            const storage = try allocator.alloc(u8, digits.len);
            compact_storage = storage;
            var length: usize = 0;
            for (digits) |character| {
                if (std.ascii.isWhitespace(character)) continue;
                storage[length] = character;
                length += 1;
            }
            break :compact storage[0..length];
        };

        if (text.len == 0) return error.InvalidInteger;
        var offset: usize = 0;
        const negative = text[0] == '-';
        if (negative or text[0] == '+') offset = 1;
        if (offset == text.len) return error.InvalidInteger;

        var actual_base = base;
        var magnitude = text[offset..];
        if (actual_base == 0) {
            actual_base = 10;
            if (magnitude.len >= 2 and magnitude[0] == '0') {
                switch (magnitude[1]) {
                    'x', 'X' => {
                        actual_base = 16;
                        magnitude = magnitude[2..];
                    },
                    'b', 'B' => {
                        actual_base = 2;
                        magnitude = magnitude[2..];
                    },
                    else => if (magnitude.len > 1) {
                        actual_base = 8;
                    },
                }
            }
        }
        if (magnitude.len == 0) return error.InvalidInteger;
        for (magnitude) |character| {
            _ = digitValue(character, actual_base) orelse return error.InvalidInteger;
        }

        var result = try initWithAllocator(allocator);
        errdefer result.deinit();
        if (actual_base <= 36) {
            result.raw.setString(actual_base, magnitude) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.InvalidInteger,
            };
        } else {
            var multiplier = try initWithAllocator(allocator);
            defer multiplier.deinit();
            try multiplier.raw.set(actual_base);
            for (magnitude) |character| {
                try result.raw.mul(&result.raw, &multiplier.raw);
                try result.raw.addScalar(&result.raw, digitValue(character, actual_base).?);
            }
        }
        if (negative and !result.isZero()) result.raw.setSign(false);
        return result;
    }

    pub fn deinit(self: *Self) void {
        if (self.owns_raw) self.raw.deinit();
        self.* = undefined;
    }

    pub fn clone(self: *const Self) Self {
        const raw = self.raw.cloneWithDifferentAllocator(derived_allocator) catch outOfMemory();
        return .{ .raw = raw };
    }

    /// Transfers the allocation without allocating a replacement. The
    /// moved-from value remains safe to deinitialize, but must not otherwise
    /// be used until replaced.
    pub fn take(self: *Self) Self {
        std.debug.assert(self.owns_raw);
        const result = self.*;
        self.owns_raw = false;
        return result;
    }

    pub fn sign(self: *const Self) std.math.Order {
        if (self.isZero()) return .eq;
        return if (self.raw.isPositive()) .gt else .lt;
    }

    pub fn isZero(self: *const Self) bool {
        return self.raw.eqlZero();
    }

    pub fn isNegative(self: *const Self) bool {
        return !self.isZero() and !self.raw.isPositive();
    }

    pub fn compare(self: *const Self, other: *const Self) std.math.Order {
        return self.raw.order(other.raw);
    }

    pub fn compareSigned(self: *const Self, other: i64) std.math.Order {
        return self.raw.toConst().orderAgainstScalar(other);
    }

    pub fn compareUnsigned(self: *const Self, other: u64) std.math.Order {
        return self.raw.toConst().orderAgainstScalar(other);
    }

    /// Number of bits in the absolute value; zero has bit length zero.
    pub fn bitLength(self: *const Self) usize {
        return self.raw.bitCountAbs();
    }

    fn magnitudeBit(self: *const Self, bit: usize) bool {
        const limbs = self.raw.toConst().limbs;
        const index = bit / limb_bits;
        if (index >= limbs.len) return false;
        return limbs[index] & (@as(Limb, 1) << @intCast(bit % limb_bits)) != 0;
    }

    fn lowestMagnitudeBit(self: *const Self) usize {
        for (self.raw.toConst().limbs, 0..) |limb, index| {
            if (limb != 0) {
                return index * limb_bits + @as(usize, @intCast(@ctz(limb)));
            }
        }
        unreachable;
    }

    /// Tests the infinite two's-complement representation, including for
    /// negative values.
    pub fn testBit(self: *const Self, bit: usize) bool {
        if (!self.isNegative()) return self.magnitudeBit(bit);
        const lowest = self.lowestMagnitudeBit();
        if (bit < lowest) return false;
        if (bit == lowest) return true;
        return !self.magnitudeBit(bit);
    }

    pub fn toStringAlloc(
        self: *const Self,
        allocator: std.mem.Allocator,
        base: u8,
    ) (std.mem.Allocator.Error || error{InvalidBase})![]u8 {
        if (base < 2 or base > 62) return error.InvalidBase;
        if (base <= 36) {
            return self.raw.toConst().toStringAlloc(allocator, base, .lower);
        }
        if (self.isZero()) return allocator.dupe(u8, "0");

        const alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        var reversed: std.ArrayList(u8) = .empty;
        defer reversed.deinit(allocator);
        var value = self.absolute();
        defer value.deinit();
        var divisor = initUnsigned(base);
        defer divisor.deinit();
        var quotient_value = init();
        defer quotient_value.deinit();
        var remainder_value = init();
        defer remainder_value.deinit();

        while (!value.isZero()) {
            quotient_value.raw.divTrunc(
                &remainder_value.raw,
                &value.raw,
                &divisor.raw,
            ) catch outOfMemory();
            const digit = remainder_value.raw.toInt(u8) catch unreachable; // zlinter-disable-current-line no_swallow_error - remainder is strictly smaller than the validated radix
            try reversed.append(allocator, alphabet[digit]);
            value.raw.swap(&quotient_value.raw);
        }
        if (self.isNegative()) try reversed.append(allocator, '-');
        std.mem.reverse(u8, reversed.items);
        return reversed.toOwnedSlice(allocator);
    }

    /// Returns the unsigned magnitude in compact big-endian form.
    pub fn toMagnitudeBigEndianAlloc(
        self: *const Self,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        const byte_count = (self.bitLength() + 7) / 8;
        const output = try allocator.alloc(u8, byte_count);
        if (byte_count == 0) return output;
        const value = self.raw.toConst();
        const magnitude: NativeConst = .{
            .limbs = value.limbs,
            .positive = true,
        };
        magnitude.writeTwosComplement(output, .big);
        return output;
    }

    pub fn writeBigEndian(self: *const Self, output: []u8) error{
        NegativeValue,
        ValueTooLarge,
    }!void {
        if (self.isNegative()) return error.NegativeValue;
        const byte_count = (self.bitLength() + 7) / 8;
        if (byte_count > output.len) return error.ValueTooLarge;
        @memset(output, 0);
        if (byte_count == 0) return;
        self.raw.toConst().writeTwosComplement(output, .big);
    }

    /// Converts modulo 2^256, matching fixed-width C++ conversion behavior.
    pub fn toU256Wrapping(self: *const Self) u256 {
        const limbs = self.raw.toConst().limbs;
        const count = @min(limbs.len, 256 / limb_bits);
        var result: u256 = 0;
        var index = count;
        while (index != 0) {
            index -= 1;
            result <<= @intCast(limb_bits);
            result |= @as(u256, limbs[index]);
        }
        return if (self.isNegative()) 0 -% result else result;
    }

    fn binary(lhs: *const Self, rhs: *const Self, operation: BinaryOperation) Self {
        var result = init();
        switch (operation) {
            .add => result.raw.add(&lhs.raw, &rhs.raw) catch outOfMemory(),
            .sub => result.raw.sub(&lhs.raw, &rhs.raw) catch outOfMemory(),
            .mul => result.raw.mul(&lhs.raw, &rhs.raw) catch outOfMemory(),
            .gcd => result.raw.gcd(&lhs.raw, &rhs.raw) catch outOfMemory(),
            .bit_and => result.raw.bitAnd(&lhs.raw, &rhs.raw) catch outOfMemory(),
            .bit_or => result.raw.bitOr(&lhs.raw, &rhs.raw) catch outOfMemory(),
            .bit_xor => result.raw.bitXor(&lhs.raw, &rhs.raw) catch outOfMemory(),
        }
        return result;
    }

    pub fn add(lhs: *const Self, rhs: *const Self) Self {
        return binary(lhs, rhs, .add);
    }

    pub fn sub(lhs: *const Self, rhs: *const Self) Self {
        return binary(lhs, rhs, .sub);
    }

    pub fn mul(lhs: *const Self, rhs: *const Self) Self {
        return binary(lhs, rhs, .mul);
    }

    pub fn quotient(lhs: *const Self, rhs: *const Self) error{DivisionByZero}!Self {
        if (rhs.isZero()) return error.DivisionByZero;
        var result = init();
        errdefer result.deinit();
        var discarded_remainder = init();
        defer discarded_remainder.deinit();
        result.raw.divTrunc(
            &discarded_remainder.raw,
            &lhs.raw,
            &rhs.raw,
        ) catch outOfMemory();
        return result;
    }

    pub fn remainder(lhs: *const Self, rhs: *const Self) error{DivisionByZero}!Self {
        if (rhs.isZero()) return error.DivisionByZero;
        var discarded_quotient = init();
        defer discarded_quotient.deinit();
        var result = init();
        errdefer result.deinit();
        discarded_quotient.raw.divTrunc(
            &result.raw,
            &lhs.raw,
            &rhs.raw,
        ) catch outOfMemory();
        return result;
    }

    pub fn gcd(lhs: *const Self, rhs: *const Self) Self {
        return binary(lhs, rhs, .gcd);
    }

    pub fn bitAnd(lhs: *const Self, rhs: *const Self) Self {
        return binary(lhs, rhs, .bit_and);
    }

    pub fn bitOr(lhs: *const Self, rhs: *const Self) Self {
        return binary(lhs, rhs, .bit_or);
    }

    pub fn bitXor(lhs: *const Self, rhs: *const Self) Self {
        return binary(lhs, rhs, .bit_xor);
    }

    pub fn negate(self: *const Self) Self {
        var result = self.clone();
        if (!result.isZero()) result.raw.negate();
        return result;
    }

    pub fn absolute(self: *const Self) Self {
        var result = self.clone();
        result.raw.abs();
        return result;
    }

    pub fn bitNot(self: *const Self) Self {
        var result = self.negate();
        result.raw.addScalar(&result.raw, @as(i8, -1)) catch outOfMemory();
        return result;
    }

    pub fn shiftLeft(self: *const Self, bits: usize) Self {
        var result = init();
        result.raw.shiftLeft(&self.raw, bits) catch outOfMemory();
        return result;
    }

    /// Arithmetic right shift, matching `cpp_int` for negative operands.
    pub fn shiftRight(self: *const Self, bits: usize) Self {
        var result = init();
        result.raw.shiftRight(&self.raw, bits) catch outOfMemory();
        return result;
    }

    pub fn pow(self: *const Self, exponent: u64) Self {
        if (exponent == 0) return initUnsigned(1);
        if (self.isZero()) return init();
        if (self.compareSigned(1) == .eq) return initUnsigned(1);
        if (self.compareSigned(-1) == .eq) {
            return initSigned(if (exponent & 1 == 0) 1 else -1);
        }
        if (exponent <= std.math.maxInt(u32)) {
            var result = init();
            result.raw.pow(&self.raw, @intCast(exponent)) catch outOfMemory();
            return result;
        }

        var result = initUnsigned(1);
        var factor = self.clone();
        defer factor.deinit();
        var remaining = exponent;
        while (remaining != 0) : (remaining >>= 1) {
            if (remaining & 1 != 0) {
                const product = mul(&result, &factor);
                result.deinit();
                result = product;
            }
            if (remaining > 1) {
                const square = mul(&factor, &factor);
                factor.deinit();
                factor = square;
            }
        }
        return result;
    }
};

test "native BigInt owns, clones, transfers, and formats explicitly" {
    var value = try BigInt.parse(
        std.testing.allocator,
        "1234567890123456789012345678901234567890",
        10,
    );
    defer value.deinit();

    var cloned = value.clone();
    defer cloned.deinit();
    try std.testing.expectEqual(std.math.Order.eq, value.compare(&cloned));

    var moved = cloned.take();
    defer moved.deinit();
    try std.testing.expect(!cloned.owns_raw);

    const text = try moved.toStringAlloc(std.testing.allocator, 10);
    defer std.testing.allocator.free(text);
    try std.testing.expectEqualStrings(
        "1234567890123456789012345678901234567890",
        text,
    );
}

test "native BigInt arithmetic and fixed-width reduction preserve signs" {
    var negative = BigInt.initSigned(-3);
    defer negative.deinit();
    var shifted = negative.shiftRight(1);
    defer shifted.deinit();
    try std.testing.expectEqual(std.math.Order.eq, shifted.compareSigned(-2));

    var two = BigInt.initUnsigned(2);
    defer two.deinit();
    var power = two.pow(300);
    defer power.deinit();
    try std.testing.expectEqual(@as(usize, 301), power.bitLength());
    try std.testing.expectEqual(@as(u256, 0), power.toU256Wrapping());

    var minus_one = BigInt.initSigned(-1);
    defer minus_one.deinit();
    try std.testing.expectEqual(std.math.maxInt(u256), minus_one.toU256Wrapping());
}

test "native BigInt handles trivial powers at the u32 exponent boundary" {
    const boundary: u64 = std.math.maxInt(u32);

    var zero = BigInt.initUnsigned(0);
    defer zero.deinit();
    var zero_to_zero = zero.pow(0);
    defer zero_to_zero.deinit();
    try std.testing.expectEqual(std.math.Order.eq, zero_to_zero.compareUnsigned(1));
    var zero_at_boundary = zero.pow(boundary);
    defer zero_at_boundary.deinit();
    try std.testing.expect(zero_at_boundary.isZero());

    var one = BigInt.initUnsigned(1);
    defer one.deinit();
    var one_at_boundary = one.pow(boundary);
    defer one_at_boundary.deinit();
    try std.testing.expectEqual(std.math.Order.eq, one_at_boundary.compareUnsigned(1));
    var one_after_boundary = one.pow(boundary + 1);
    defer one_after_boundary.deinit();
    try std.testing.expectEqual(std.math.Order.eq, one_after_boundary.compareUnsigned(1));

    var minus_one = BigInt.initSigned(-1);
    defer minus_one.deinit();
    var minus_one_at_boundary = minus_one.pow(boundary);
    defer minus_one_at_boundary.deinit();
    try std.testing.expectEqual(std.math.Order.eq, minus_one_at_boundary.compareSigned(-1));
    var minus_one_after_boundary = minus_one.pow(boundary + 1);
    defer minus_one_after_boundary.deinit();
    try std.testing.expectEqual(std.math.Order.eq, minus_one_after_boundary.compareSigned(1));
}

test "native BigInt preserves GMP parsing, division, and bit semantics" {
    var base62 = try BigInt.parse(std.testing.allocator, "Zz", 62);
    defer base62.deinit();
    try std.testing.expectEqual(std.math.Order.eq, base62.compareUnsigned(2231));
    const base62_text = try base62.toStringAlloc(std.testing.allocator, 62);
    defer std.testing.allocator.free(base62_text);
    try std.testing.expectEqualStrings("Zz", base62_text);

    var hexadecimal = try BigInt.parse(std.testing.allocator, "  -0xff  ", 0);
    defer hexadecimal.deinit();
    try std.testing.expectEqual(std.math.Order.eq, hexadecimal.compareSigned(-255));

    var seven = BigInt.initSigned(-7);
    defer seven.deinit();
    var three = BigInt.initUnsigned(3);
    defer three.deinit();
    var quotient_value = try BigInt.quotient(&seven, &three);
    defer quotient_value.deinit();
    var remainder_value = try BigInt.remainder(&seven, &three);
    defer remainder_value.deinit();
    try std.testing.expectEqual(std.math.Order.eq, quotient_value.compareSigned(-2));
    try std.testing.expectEqual(std.math.Order.eq, remainder_value.compareSigned(-1));

    var minus_two = BigInt.initSigned(-2);
    defer minus_two.deinit();
    try std.testing.expect(!minus_two.testBit(0));
    try std.testing.expect(minus_two.testBit(1));
    try std.testing.expect(minus_two.testBit(200));
    var complement = minus_two.bitNot();
    defer complement.deinit();
    try std.testing.expectEqual(std.math.Order.eq, complement.compareSigned(1));
}

test "native BigInt imports and exports unsigned big-endian magnitudes" {
    var value = BigInt.fromBigEndian(&.{ 0x12, 0x34 });
    defer value.deinit();
    var bytes: [4]u8 = undefined;
    try value.writeBigEndian(&bytes);
    try std.testing.expectEqualSlices(u8, &.{ 0, 0, 0x12, 0x34 }, &bytes);

    var negative = BigInt.initSigned(-1);
    defer negative.deinit();
    try std.testing.expectError(error.NegativeValue, negative.writeBigEndian(&bytes));
}
