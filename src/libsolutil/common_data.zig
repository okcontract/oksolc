// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared container and byte/string algorithms from `CommonData.cpp`.

const std = @import("std");
const fixed_hash = @import("fixed_hash.zig");
const keccak = @import("keccak256.zig");

pub const WhenError = enum(c_int) {
    dont_throw = 0,
    throw = 1,
};

pub const HexPrefix = enum(c_int) {
    dont_add = 0,
    add = 1,
};

pub const HexCase = enum(c_int) {
    lower = 0,
    upper = 1,
    mixed = 2,
};

pub const HexError = error{
    BadHexCase,
    BadHexCharacter,
};

const lower_hex = "0123456789abcdef";
const upper_hex = "0123456789ABCDEF";

pub fn toHexByte(value: u8, letter_case: HexCase) HexError![2]u8 {
    if (letter_case == .mixed) return error.BadHexCase;
    const alphabet = if (letter_case == .upper) upper_hex else lower_hex;
    return .{ alphabet[value >> 4], alphabet[value & 0x0f] };
}

pub fn toHexAlloc(
    allocator: std.mem.Allocator,
    data: []const u8,
    prefix: HexPrefix,
    letter_case: HexCase,
) std.mem.Allocator.Error![]u8 {
    const prefix_length: usize = if (prefix == .add) 2 else 0;
    const result = try allocator.alloc(u8, prefix_length + data.len * 2);
    if (prefix == .add) @memcpy(result[0..2], "0x");

    var reverse_index = data.len -% 1;
    for (data, 0..) |byte, index| {
        const alphabet = switch (letter_case) {
            .upper => upper_hex,
            .lower => lower_hex,
            .mixed => if ((reverse_index & 2) == 0) lower_hex else upper_hex,
        };
        reverse_index -%= 1;
        const offset = prefix_length + index * 2;
        result[offset] = alphabet[byte >> 4];
        result[offset + 1] = alphabet[byte & 0x0f];
    }
    return result;
}

pub fn fromHexCharacter(character: u8, behavior: WhenError) HexError!i8 {
    const value: ?u8 = switch (character) {
        '0'...'9' => character - '0',
        'a'...'f' => character - 'a' + 10,
        'A'...'F' => character - 'A' + 10,
        else => null,
    };
    if (value) |decoded| return @intCast(decoded);
    if (behavior == .throw) return error.BadHexCharacter;
    return -1;
}

pub const FromHexError = std.mem.Allocator.Error || HexError;

pub fn fromHexAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
    behavior: WhenError,
) FromHexError![]u8 {
    if (input.len == 0) return allocator.alloc(u8, 0);
    var source_index: usize = if (std.mem.startsWith(u8, input, "0x")) 2 else 0;
    var result: std.ArrayList(u8) = .empty;
    errdefer result.deinit(allocator);
    try result.ensureTotalCapacity(allocator, (input.len - source_index + 1) / 2);

    if (input.len % 2 != 0) {
        const high = try fromHexCharacter(input[source_index], behavior);
        source_index += 1;
        if (high < 0) return invalidHexResult(allocator, &result);
        result.appendAssumeCapacity(@intCast(high));
    }
    while (source_index < input.len) : (source_index += 2) {
        const high = try fromHexCharacter(input[source_index], behavior);
        const low = try fromHexCharacter(input[source_index + 1], behavior);
        if (high < 0 or low < 0) return invalidHexResult(allocator, &result);
        result.appendAssumeCapacity(@as(u8, @intCast(high)) << 4 | @as(u8, @intCast(low)));
    }
    return result.toOwnedSlice(allocator);
}

fn invalidHexResult(
    allocator: std.mem.Allocator,
    result: *std.ArrayList(u8),
) std.mem.Allocator.Error![]u8 {
    result.deinit(allocator);
    result.* = .empty;
    return allocator.alloc(u8, 0);
}

pub fn asString(bytes: []const u8) []const u8 {
    return bytes;
}

pub fn asBytes(string: []const u8) []const u8 {
    return string;
}

pub fn filterAlloc(
    comptime T: type,
    allocator: std.mem.Allocator,
    values: []const T,
    mask: []const bool,
) std.mem.Allocator.Error![]T {
    std.debug.assert(values.len == mask.len);
    var output: std.ArrayList(T) = .empty;
    errdefer output.deinit(allocator);
    for (values, mask) |value, keep| if (keep) try output.append(allocator, value);
    return output.toOwnedSlice(allocator);
}

pub fn applyMapAlloc(
    comptime Input: type,
    comptime Output: type,
    allocator: std.mem.Allocator,
    values: []const Input,
    context: anytype,
    operation: anytype,
) std.mem.Allocator.Error![]Output {
    const output = try allocator.alloc(Output, values.len);
    for (values, output) |value, *mapped| mapped.* = operation(context, value);
    return output;
}

pub fn convertContainerAlloc(
    comptime T: type,
    allocator: std.mem.Allocator,
    values: []const T,
) std.mem.Allocator.Error![]T {
    return allocator.dupe(T, values);
}

pub fn appendAll(
    comptime T: type,
    allocator: std.mem.Allocator,
    destination: *std.ArrayList(T),
    source: []const T,
) std.mem.Allocator.Error!void {
    try destination.appendSlice(allocator, source);
}

pub fn fold(values: anytype, initial: anytype, context: anytype, operation: anytype) @TypeOf(initial) {
    var accumulator = initial;
    for (values) |value| accumulator = operation(context, accumulator, value);
    return accumulator;
}

pub fn mapTuple(callable: anytype, tuple: anytype) @TypeOf(@call(.auto, callable, tuple)) {
    return @call(.auto, callable, tuple);
}

pub fn UniqueVector(comptime T: type) type {
    return struct {
        const Self = @This();

        storage: std.ArrayList(T) = .empty,

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            self.storage.deinit(allocator);
            self.* = undefined;
        }

        pub fn contents(self: *const Self) []const T {
            return self.storage.items;
        }

        pub fn len(self: *const Self) usize {
            return self.storage.items.len;
        }

        pub fn isEmpty(self: *const Self) bool {
            return self.storage.items.len == 0;
        }

        pub fn clearRetainingCapacity(self: *Self) void {
            self.storage.clearRetainingCapacity();
        }

        pub fn contains(self: *const Self, value: T) bool {
            for (self.storage.items) |candidate| if (std.meta.eql(candidate, value)) return true;
            return false;
        }

        pub fn pushBack(
            self: *Self,
            allocator: std.mem.Allocator,
            value: T,
        ) std.mem.Allocator.Error!bool {
            if (self.contains(value)) return false;
            try self.storage.append(allocator, value);
            return true;
        }

        pub fn appendUnique(
            self: *Self,
            allocator: std.mem.Allocator,
            values: []const T,
        ) std.mem.Allocator.Error!void {
            for (values) |value| _ = try self.pushBack(allocator, value);
        }

        pub fn removeAll(self: *Self, values: []const T) void {
            for (values) |value| {
                var found: ?usize = null;
                for (self.storage.items, 0..) |candidate, index| {
                    if (std.meta.eql(candidate, value)) {
                        found = index;
                        break;
                    }
                }
                std.debug.assert(found != null);
                _ = self.storage.orderedRemove(found.?);
            }
        }
    };
}

pub fn findOffset(values: anytype, needle: @TypeOf(values[0])) ?usize {
    for (values, 0..) |value, index| if (std.meta.eql(value, needle)) return index;
    return null;
}

pub fn contains(values: anytype, needle: @TypeOf(values[0])) bool {
    return findOffset(values, needle) != null;
}

pub fn containsIf(values: anytype, context: anytype, predicate: anytype) bool {
    for (values) |value| if (predicate(context, value)) return true;
    return false;
}

/// The replacement slices are borrowed for the duration of the callback.
/// Elements themselves are moved by value; element teardown remains the
/// caller's responsibility, matching the compatibility container policy.
pub fn iterateReplacing(
    comptime T: type,
    allocator: std.mem.Allocator,
    vector: *std.ArrayList(T),
    context: anytype,
    replace: anytype,
) std.mem.Allocator.Error!void {
    var modified: std.ArrayList(T) = .empty;
    errdefer modified.deinit(allocator);
    var use_modified = false;
    for (vector.items, 0..) |*element, index| {
        if (replace(context, element)) |replacement| {
            if (!use_modified) {
                try modified.appendSlice(allocator, vector.items[0..index]);
                use_modified = true;
            }
            try modified.appendSlice(allocator, replacement);
        } else if (use_modified) {
            try modified.append(allocator, element.*);
        }
    }
    if (use_modified) {
        vector.deinit(allocator);
        vector.* = modified;
    } else {
        modified.deinit(allocator);
    }
}

pub fn iterateReplacingWindow(
    comptime T: type,
    comptime window_size: usize,
    allocator: std.mem.Allocator,
    vector: *std.ArrayList(T),
    context: anytype,
    replace: anytype,
) std.mem.Allocator.Error!void {
    if (window_size == 0) @compileError("replacement window must be nonzero");
    var modified: std.ArrayList(T) = .empty;
    errdefer modified.deinit(allocator);
    var use_modified = false;
    var index: usize = 0;
    while (index + window_size <= vector.items.len) : (index += 1) {
        if (replace(context, vector.items[index .. index + window_size])) |replacement| {
            if (!use_modified) {
                try modified.appendSlice(allocator, vector.items[0..index]);
                use_modified = true;
            }
            try modified.appendSlice(allocator, replacement);
            index += window_size - 1;
        } else if (use_modified) {
            try modified.append(allocator, vector.items[index]);
        }
    }
    if (use_modified) {
        try modified.appendSlice(allocator, vector.items[index..]);
        vector.deinit(allocator);
        vector.* = modified;
    } else {
        modified.deinit(allocator);
    }
}

pub fn hasNonemptyIntersectionSorted(lhs: anytype, rhs: anytype) bool {
    var left_index: usize = 0;
    var right_index: usize = 0;
    while (left_index < lhs.len and right_index < rhs.len) {
        if (std.meta.eql(lhs[left_index], rhs[right_index])) return true;
        if (lhs[left_index] < rhs[right_index])
            left_index += 1
        else
            right_index += 1;
    }
    return false;
}

pub fn invertMapInto(
    allocator: std.mem.Allocator,
    original: anytype,
    inverse: anytype,
) !void {
    for (original.items()) |entry| {
        const inserted = try inverse.insert(allocator, entry.value, entry.key);
        std.debug.assert(inserted);
    }
}

pub fn keysAlloc(
    comptime Key: type,
    allocator: std.mem.Allocator,
    map: anytype,
) std.mem.Allocator.Error![]Key {
    const output = try allocator.alloc(Key, map.items().len);
    for (map.items(), output) |entry, *key| key.* = entry.key;
    return output;
}

pub fn valueOrNullptr(map: anytype, key: anytype) @TypeOf(map.getPtr(key)) {
    return map.getPtr(key);
}

pub fn valueOrDefault(map: anytype, key: anytype, default_value: anytype) @TypeOf(default_value) {
    return if (map.get(key)) |value| value.* else default_value;
}

pub fn joinMap(
    allocator: std.mem.Allocator,
    destination: anytype,
    source: anytype,
    context: anytype,
    conflict_solver: anytype,
) !void {
    for (source.items()) |entry| {
        if (destination.getPtr(entry.key)) |existing| {
            conflict_solver(context, existing, entry.value);
        } else {
            const inserted = try destination.insert(allocator, entry.key, entry.value);
            std.debug.assert(inserted);
        }
    }
}

pub const AddressError = std.mem.Allocator.Error || error{InvalidAddress};

pub fn getChecksummedAddressAlloc(
    allocator: std.mem.Allocator,
    address: []const u8,
) AddressError![]u8 {
    return allocator.dupe(u8, &try checksummedAddress(address));
}

fn checksummedAddress(address: []const u8) error{InvalidAddress}![42]u8 {
    const source = if (std.mem.startsWith(u8, address, "0x")) address[2..] else address;
    if (source.len != 40) return error.InvalidAddress;
    for (source) |character| if (!std.ascii.isHex(character)) return error.InvalidAddress;

    var lowercase: [40]u8 = undefined;
    for (source, &lowercase) |character, *output| output.* = std.ascii.toLower(character);
    const hash = keccak.keccak256(&lowercase);
    var result: [42]u8 = undefined;
    @memcpy(result[0..2], "0x");
    for (source, 0..) |character, index| {
        const nibble = (hash.get(index / 2) >> @intCast(4 * (1 - index % 2))) & 0x0f;
        result[index + 2] = if (nibble >= 8)
            std.ascii.toUpper(character)
        else
            std.ascii.toLower(character);
    }
    return result;
}

pub fn passesAddressChecksum(address: []const u8, strict: bool) bool {
    var prefixed_storage: [42]u8 = undefined;
    const prefixed: []const u8 = if (std.mem.startsWith(u8, address, "0x")) address else blk: {
        if (address.len != 40) return false;
        @memcpy(prefixed_storage[0..2], "0x");
        @memcpy(prefixed_storage[2..], address);
        break :blk &prefixed_storage;
    };
    if (prefixed.len != 42) return false;
    if (!strict) {
        const body = prefixed[2..];
        var has_lower = false;
        var has_upper = false;
        for (body) |character| {
            has_lower = has_lower or (character >= 'a' and character <= 'f');
            has_upper = has_upper or (character >= 'A' and character <= 'F');
        }
        if (!has_lower or !has_upper) return true;
    }

    const expected = checksummedAddress(prefixed) catch return false;
    return std.mem.eql(u8, prefixed, &expected);
}

pub fn isValidHex(input: []const u8) bool {
    if (!std.mem.startsWith(u8, input, "0x")) return false;
    for (input[2..]) |character| if (!std.ascii.isHex(character)) return false;
    return true;
}

pub fn isValidDecimal(input: []const u8) bool {
    if (input.len == 0) return false;
    if (std.mem.eql(u8, input, "0")) return true;
    if (input[0] == '0') return false;
    for (input) |character| if (!std.ascii.isDigit(character)) return false;
    return true;
}

pub const FormatStringError = std.mem.Allocator.Error || error{StringTooLong};

pub fn formatAsStringOrNumberAlloc(
    allocator: std.mem.Allocator,
    value: []const u8,
) FormatStringError![]u8 {
    if (value.len > 32) return error.StringTooLong;
    if (!preferStringLiteral(value)) {
        const hash = fixed_hash.H256.fromBytes(value, .align_left);
        const hex = hash.hex();
        return std.fmt.allocPrint(allocator, "0x{s}", .{hex});
    }
    return escapeAndQuoteStringAlloc(allocator, value);
}

/// The shared spelling rule for a word represented as a string or number.
/// Length validation belongs to the word constructor.
pub fn preferStringLiteral(value: []const u8) bool {
    for (value) |character| {
        if (character <= 0x1f or character >= 0x7f or character == '"') return false;
    }
    return true;
}

pub fn escapeAndQuoteStringAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output = std.Io.Writer.Allocating.init(allocator);
    defer output.deinit();
    writeEscapedQuoted(&output.writer, input) catch return error.OutOfMemory;
    return output.toOwnedSlice();
}

/// Shared quoting for caller-owned writers, including a counting projection.
pub fn writeEscapedQuoted(writer: anytype, input: []const u8) !void {
    try writer.writeByte('"');
    try writeEscapedStringContent(writer, input);
    try writer.writeByte('"');
}

/// Stream one string segment with the same byte escaping as writeEscapedQuoted.
/// The caller owns the quotes, allowing borrowed segments to share one string.
/// Input stays alive and unchanged until return; writers consume slices synchronously.
pub fn writeEscapedStringContent(writer: anytype, input: []const u8) !void {
    // Bound lookahead when a layout probe or failing writer stops early.
    // Each plain run borrows the input; only four-byte escapes use stack storage.
    var remaining = input;
    while (remaining.len != 0) {
        const chunk = remaining[0..@min(remaining.len, 64)];
        var start: usize = 0;
        for (chunk, 0..) |character, index| {
            var encoded: [4]u8 = undefined;
            const escaped: []const u8 = switch (character) {
                '\\' => "\\\\",
                '"' => "\\\"",
                '\n' => "\\n",
                '\r' => "\\r",
                '\t' => "\\t",
                else => blk: {
                    if (std.ascii.isPrint(character)) continue;
                    const hex = std.fmt.bytesToHex([_]u8{character}, .lower);
                    encoded = .{ '\\', 'x', hex[0], hex[1] };
                    break :blk &encoded;
                },
            };
            if (start != index) try writer.writeAll(chunk[start..index]);
            try writer.writeAll(escaped);
            start = index + 1;
        }
        if (start != chunk.len) try writer.writeAll(chunk[start..]);
        remaining = remaining[chunk.len..];
    }
}

test "escaped string content preserves all bytes across segments and writer limits" {
    var input: [256]u8 = undefined;
    for (&input, 0..) |*byte, index| byte.* = @intCast(index);
    const expected = "\"" ++
        "\\x00\\x01\\x02\\x03\\x04\\x05\\x06\\x07\\x08\\t\\n\\x0b\\x0c\\r\\x0e\\x0f\\x10\\x11\\x12\\x13\\x14\\x15\\x16\\x17\\x18\\x19\\x1a\\x1b\\x1c\\x1d\\x1e\\x1f" ++
        " !\\\"#$%&'()*+,-./0123456789:;<=>?" ++
        "@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\\\]^_" ++
        "`abcdefghijklmnopqrstuvwxyz{|}~\\x7f" ++
        "\\x80\\x81\\x82\\x83\\x84\\x85\\x86\\x87\\x88\\x89\\x8a\\x8b\\x8c\\x8d\\x8e\\x8f\\x90\\x91\\x92\\x93\\x94\\x95\\x96\\x97\\x98\\x99\\x9a\\x9b\\x9c\\x9d\\x9e\\x9f" ++
        "\\xa0\\xa1\\xa2\\xa3\\xa4\\xa5\\xa6\\xa7\\xa8\\xa9\\xaa\\xab\\xac\\xad\\xae\\xaf\\xb0\\xb1\\xb2\\xb3\\xb4\\xb5\\xb6\\xb7\\xb8\\xb9\\xba\\xbb\\xbc\\xbd\\xbe\\xbf" ++
        "\\xc0\\xc1\\xc2\\xc3\\xc4\\xc5\\xc6\\xc7\\xc8\\xc9\\xca\\xcb\\xcc\\xcd\\xce\\xcf\\xd0\\xd1\\xd2\\xd3\\xd4\\xd5\\xd6\\xd7\\xd8\\xd9\\xda\\xdb\\xdc\\xdd\\xde\\xdf" ++
        "\\xe0\\xe1\\xe2\\xe3\\xe4\\xe5\\xe6\\xe7\\xe8\\xe9\\xea\\xeb\\xec\\xed\\xee\\xef\\xf0\\xf1\\xf2\\xf3\\xf4\\xf5\\xf6\\xf7\\xf8\\xf9\\xfa\\xfb\\xfc\\xfd\\xfe\\xff" ++
        "\"";
    var buffer: [1024]u8 = undefined;
    for (0..input.len + 1) |split| {
        var writer = std.Io.Writer.fixed(&buffer);
        try writer.writeByte('"');
        try writeEscapedStringContent(&writer, input[0..split]);
        try writeEscapedStringContent(&writer, input[split..]);
        try writer.writeByte('"');
        try std.testing.expectEqualStrings(expected, writer.buffered());
    }
    for (0..expected.len + 1) |capacity| {
        var writer = std.Io.Writer.fixed(buffer[0..capacity]);
        if (capacity < expected.len) {
            try std.testing.expectError(error.WriteFailed, writeEscapedQuoted(&writer, &input));
            try std.testing.expect(std.mem.startsWith(u8, expected, writer.buffered()));
        } else {
            try writeEscapedQuoted(&writer, &input);
            try std.testing.expectEqualStrings(expected, writer.buffered());
        }
    }
}

test "escaped string content joins borrowed segments with shared quoting" {
    const first = "\x00\x1f !\"";
    const second = "\t\n\r\\\x7f\xff";
    const expected = "\"\\x00\\x1f !\\\"\\t\\n\\r\\\\\\x7f\\xff\"";
    var buffer: [128]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buffer);
    try writer.writeByte('"');
    try writeEscapedStringContent(&writer, first);
    try writeEscapedStringContent(&writer, second);
    try writer.writeByte('"');
    try std.testing.expectEqualStrings(expected, writer.buffered());
    writer.end = 0;
    try writeEscapedQuoted(&writer, first ++ second);
    try std.testing.expectEqualStrings(expected, writer.buffered());
    var short = std.Io.Writer.fixed(buffer[0..3]);
    try std.testing.expectError(error.WriteFailed, writeEscapedStringContent(&short, first));
}

pub fn containerEqual(lhs: anytype, rhs: anytype, context: anytype, compare: anytype) bool {
    if (lhs.len != rhs.len) return false;
    for (lhs, rhs) |left, right| if (!compare(context, left, right)) return false;
    return true;
}

pub fn findAnyOf(haystack: []const u8, needles: []const []const u8) []const u8 {
    for (needles) |needle| if (std.mem.find(u8, haystack, needle) != null) return needle;
    return "";
}

pub fn makeVectorAlloc(
    comptime T: type,
    allocator: std.mem.Allocator,
    values: anytype,
) std.mem.Allocator.Error![]T {
    const fields = std.meta.fields(@TypeOf(values));
    const output = try allocator.alloc(T, fields.len);
    inline for (fields, 0..) |field, index| output[index] = @field(values, field.name);
    return output;
}

pub fn stringOrDefault(value: []const u8, default_value: []const u8) []const u8 {
    return if (value.len != 0) value else default_value;
}

test "hex conversion preserves odd nibbles, mixed case, and validation" {
    const decoded = try fromHexAlloc(std.testing.allocator, "0x001122aAbBcCdDeEfF0", .throw);
    defer std.testing.allocator.free(decoded);
    const encoded = try toHexAlloc(std.testing.allocator, decoded, .add, .mixed);
    defer std.testing.allocator.free(encoded);
    try std.testing.expectEqualStrings("0x0001122AabbcCDDEeff0", encoded);
    try std.testing.expect(isValidHex("0x"));
    try std.testing.expect(isValidDecimal("123"));
    try std.testing.expect(!isValidDecimal("01"));
}

test "EIP-55 checksums and escaped strings match upstream behavior" {
    const address = try getChecksummedAddressAlloc(
        std.testing.allocator,
        "52908400098527886e0f7030069857d2e4169ee7",
    );
    defer std.testing.allocator.free(address);
    try std.testing.expectEqualStrings("0x52908400098527886E0F7030069857D2E4169EE7", address);
    try std.testing.expect(passesAddressChecksum(address, true));
    try std.testing.expect(passesAddressChecksum(address[2..], true));
    try std.testing.expect(!passesAddressChecksum("52908400098527886e0F7030069857D2E4169EE7", true));
    try std.testing.expect(!passesAddressChecksum("52908400098527886E0F7030069857D2E4169EEG", true));
    try std.testing.expect(!passesAddressChecksum("0x123", true));
    try std.testing.expect(passesAddressChecksum("52908400098527886e0f7030069857d2e4169ee7", false));

    const escaped = try escapeAndQuoteStringAlloc(std.testing.allocator, "a\n\t\\\"\x01");
    defer std.testing.allocator.free(escaped);
    try std.testing.expectEqualStrings("\"a\\n\\t\\\\\\\"\\x01\"", escaped);
}

test "unique vector and sorted intersection preserve deterministic order" {
    var values: UniqueVector(u32) = .{};
    defer values.deinit(std.testing.allocator);
    try std.testing.expect(try values.pushBack(std.testing.allocator, 2));
    try std.testing.expect(!(try values.pushBack(std.testing.allocator, 2)));
    try values.appendUnique(std.testing.allocator, &.{ 1, 3, 1 });
    try std.testing.expectEqualSlices(u32, &.{ 2, 1, 3 }, values.contents());
    try std.testing.expect(hasNonemptyIntersectionSorted(
        &[_]u32{ 1, 3, 5 },
        &[_]u32{ 2, 3, 4 },
    ));
}
