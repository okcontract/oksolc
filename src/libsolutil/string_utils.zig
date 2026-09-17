// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! String algorithms and diagnostic formatting from `StringUtils.cpp`.

const std = @import("std");
const common_data = @import("common_data.zig");
const numeric = @import("numeric.zig");

pub const BigInt = numeric.BigInt;

pub fn stringDistance(
    allocator: std.mem.Allocator,
    first: []const u8,
    second: []const u8,
) std.mem.Allocator.Error!usize {
    const row_length = second.len + 1;
    const dp = try allocator.alloc(usize, 3 * row_length);
    defer allocator.free(dp);

    for (0..first.len + 1) |first_index| {
        for (0..second.len + 1) |second_index| {
            var distance: usize = 0;
            if (@min(first_index, second_index) == 0) {
                distance = @max(first_index, second_index);
            } else {
                const left = dp[(first_index - 1) % 3 + second_index * 3];
                const up = dp[first_index % 3 + (second_index - 1) * 3];
                const upper_left = dp[(first_index - 1) % 3 + (second_index - 1) * 3];
                distance = @min(left + 1, up + 1);
                distance = @min(
                    distance,
                    upper_left + @intFromBool(first[first_index - 1] != second[second_index - 1]),
                );
                if (first_index > 1 and second_index > 1 and
                    first[first_index - 1] == second[second_index - 2] and
                    first[first_index - 2] == second[second_index - 1])
                {
                    distance = @min(
                        distance,
                        dp[(first_index - 2) % 3 + (second_index - 2) * 3] + 1,
                    );
                }
            }
            dp[first_index % 3 + second_index * 3] = distance;
        }
    }
    return dp[first.len % 3 + second.len * 3];
}

pub fn stringWithinDistance(
    allocator: std.mem.Allocator,
    first: []const u8,
    second: []const u8,
    maximum_distance: usize,
    length_threshold: usize,
) std.mem.Allocator.Error!bool {
    if (std.mem.eql(u8, first, second)) return true;
    if (length_threshold > 0) {
        const product = std.math.mul(usize, first.len, second.len) catch std.math.maxInt(usize);
        if (product > length_threshold) return false;
    }
    const distance = try stringDistance(allocator, first, second);
    return distance <= maximum_distance and distance < first.len and distance < second.len;
}

pub fn joinHumanReadableAlloc(
    allocator: std.mem.Allocator,
    list: []const []const u8,
    separator: []const u8,
    last_separator: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (list, 0..) |element, index| {
        if (index != 0) {
            const selected = if (index + 1 == list.len and last_separator.len != 0)
                last_separator
            else
                separator;
            try output.appendSlice(allocator, selected);
        }
        try output.appendSlice(allocator, element);
    }
    return output.toOwnedSlice(allocator);
}

pub fn joinHumanReadablePrefixedAlloc(
    allocator: std.mem.Allocator,
    list: []const []const u8,
    separator: []const u8,
    last_separator: []const u8,
) std.mem.Allocator.Error![]u8 {
    if (list.len == 0) return allocator.alloc(u8, 0);
    const joined = try joinHumanReadableAlloc(allocator, list, separator, last_separator);
    defer allocator.free(joined);
    return std.fmt.allocPrint(allocator, "{s}{s}", .{ separator, joined });
}

pub fn quotedAlternativesListAlloc(
    allocator: std.mem.Allocator,
    suggestions: []const []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (suggestions, 0..) |suggestion, index| {
        if (index != 0) try output.appendSlice(
            allocator,
            if (index + 1 == suggestions.len) " or " else ", ",
        );
        try output.append(allocator, '"');
        try output.appendSlice(allocator, suggestion);
        try output.append(allocator, '"');
    }
    return output.toOwnedSlice(allocator);
}

pub fn suffixedVariableNameListAlloc(
    allocator: std.mem.Allocator,
    base_name: []const u8,
    start_suffix: usize,
    end_suffix: usize,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    if (start_suffix < end_suffix) {
        for (start_suffix..end_suffix) |suffix| {
            if (suffix != start_suffix) try output.appendSlice(allocator, ", ");
            try output.writer(allocator).print("{s}{d}", .{ base_name, suffix });
        }
    } else if (end_suffix < start_suffix) {
        var suffix = start_suffix;
        while (suffix > end_suffix) {
            suffix -= 1;
            if (suffix + 1 != start_suffix) try output.appendSlice(allocator, ", ");
            try output.writer(allocator).print("{s}{d}", .{ base_name, suffix });
        }
    }
    return output.toOwnedSlice(allocator);
}

fn lowByteIsZero(value: *const BigInt) bool {
    for (0..8) |bit| if (value.testBit(bit)) return false;
    return true;
}

fn isPowerOfTwo(value: *const BigInt) bool {
    if (value.isZero() or value.isNegative()) return false;
    const high_bit = value.bitLength() - 1;
    for (0..high_bit) |bit| if (value.testBit(bit)) return false;
    return value.testBit(high_bit);
}

fn tryFormatPowerOfTwo(
    allocator: std.mem.Allocator,
    value: *const BigInt,
) (std.mem.Allocator.Error!?[]u8) {
    var prefix = value.clone();
    defer prefix.deinit();
    var zero_bytes: usize = 0;
    while (!prefix.isZero() and lowByteIsZero(&prefix)) {
        var shifted = prefix.shiftRight(8);
        prefix.deinit();
        prefix = shifted.take();
        shifted.deinit();
        zero_bytes += 1;
    }
    if (zero_bytes <= 2) return null;

    if (prefix.compareUnsigned(1) == .eq) {
        const formatted = try std.fmt.allocPrint(allocator, "2**{d}", .{zero_bytes * 8});
        return formatted;
    }
    if (isPowerOfTwo(&prefix)) {
        const formatted = try std.fmt.allocPrint(
            allocator,
            "2**{d}",
            .{zero_bytes * 8 + prefix.bitLength() - 1},
        );
        return formatted;
    }

    const bytes = try prefix.toMagnitudeBigEndianAlloc(allocator);
    defer allocator.free(bytes);
    const encoded = try common_data.toHexAlloc(allocator, bytes, .add, .mixed);
    defer allocator.free(encoded);
    const formatted = try std.fmt.allocPrint(allocator, "{s} * 2**{d}", .{ encoded, zero_bytes * 8 });
    return formatted;
}

fn trimTrailingSpaces(value: []const u8) []const u8 {
    var end = value.len;
    while (end != 0 and value[end - 1] == ' ') end -= 1;
    return value[0..end];
}

pub const FormatNumberError = std.mem.Allocator.Error || error{InvalidBase};

pub fn formatNumberReadableAlloc(
    allocator: std.mem.Allocator,
    value: *const BigInt,
    use_truncation: bool,
) FormatNumberError![]u8 {
    const negative = value.isNegative();
    var absolute = value.absolute();
    defer absolute.deinit();
    if (absolute.compareUnsigned(0x1000000) != .gt) {
        return value.toStringAlloc(allocator, 10);
    }

    if (try tryFormatPowerOfTwo(allocator, &absolute)) |formatted| {
        defer allocator.free(formatted);
        return std.fmt.allocPrint(allocator, "{s}{s}", .{ if (negative) "-" else "", formatted });
    }

    var one = BigInt.initUnsigned(1);
    defer one.deinit();
    var next = BigInt.add(&absolute, &one);
    defer next.deinit();
    if (try tryFormatPowerOfTwo(allocator, &next)) |formatted| {
        defer allocator.free(formatted);
        return std.fmt.allocPrint(
            allocator,
            "{s}{s}{s}",
            .{ if (negative) "-" else "", formatted, if (negative) " + 1" else " - 1" },
        );
    }

    const magnitude = try absolute.toMagnitudeBigEndianAlloc(allocator);
    defer allocator.free(magnitude);
    const encoded = try common_data.toHexAlloc(allocator, magnitude, .add, .mixed);
    defer allocator.free(encoded);
    const sign: []const u8 = if (negative) "-" else "";
    if (!use_truncation or encoded.len < 24) {
        return std.fmt.allocPrint(allocator, "{s}{s}", .{ sign, encoded });
    }

    const initial_characters: usize = 6;
    const final_characters: usize = 4;
    const skipped = encoded.len - initial_characters - final_characters;
    return std.fmt.allocPrint(
        allocator,
        "{s}{s}...{{+{d} more}}...{s}",
        .{
            sign,
            encoded[0..initial_characters],
            skipped,
            encoded[encoded.len - final_characters ..],
        },
    );
}

pub fn formatNumberReadableU256Alloc(
    allocator: std.mem.Allocator,
    value: u256,
    use_truncation: bool,
) FormatNumberError![]u8 {
    var unbounded = BigInt.fromU256(value);
    defer unbounded.deinit();
    return formatNumberReadableAlloc(allocator, &unbounded, use_truncation);
}

pub fn toUnsignedInt(value: []const u8) ?u32 {
    var index: usize = 0;
    while (index < value.len and std.ascii.isWhitespace(value[index])) index += 1;
    if (index < value.len and value[index] == '+') index += 1;
    const begin = index;
    while (index < value.len and std.ascii.isDigit(value[index])) index += 1;
    if (index == begin) return null;
    return std.fmt.parseInt(u32, value[begin..index], 10) catch null;
}

pub fn toLower(character: u8) u8 {
    return std.ascii.toLower(character);
}

pub fn toUpper(character: u8) u8 {
    return std.ascii.toUpper(character);
}

pub fn toLowerAlloc(
    allocator: std.mem.Allocator,
    value: []const u8,
) std.mem.Allocator.Error![]u8 {
    const result = try allocator.dupe(u8, value);
    for (result) |*character| character.* = toLower(character.*);
    return result;
}

pub fn isDigit(character: u8) bool {
    return std.ascii.isDigit(character);
}

pub fn isPrint(character: u8) bool {
    return std.ascii.isPrint(character);
}

pub fn prefixLinesAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
    prefix: []const u8,
    trim_prefix: bool,
    ensure_final_newline: bool,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var position: usize = 0;
    while (position < input.len) {
        const relative_newline = std.mem.findScalar(u8, input[position..], '\n');
        const line_end = if (relative_newline) |offset| position + offset else input.len;
        const line = input[position..line_end];
        if (line.len == 0 and trim_prefix) {
            try output.appendSlice(allocator, trimTrailingSpaces(prefix));
        } else {
            try output.appendSlice(allocator, prefix);
            try output.appendSlice(allocator, line);
        }
        const had_newline = line_end < input.len;
        if (had_newline or ensure_final_newline) try output.append(allocator, '\n');
        position = if (had_newline) line_end + 1 else input.len;
    }
    return output.toOwnedSlice(allocator);
}

pub fn printPrefixed(
    writer: anytype,
    input: []const u8,
    prefix: []const u8,
    trim_prefix: bool,
    ensure_final_newline: bool,
) anyerror!void {
    var position: usize = 0;
    while (position < input.len) {
        const relative_newline = std.mem.findScalar(u8, input[position..], '\n');
        const line_end = if (relative_newline) |offset| position + offset else input.len;
        const line = input[position..line_end];
        if (line.len == 0 and trim_prefix) {
            try writer.writeAll(trimTrailingSpaces(prefix));
        } else {
            try writer.writeAll(prefix);
            try writer.writeAll(line);
        }
        const had_newline = line_end < input.len;
        if (had_newline or ensure_final_newline) try writer.writeByte('\n');
        position = if (had_newline) line_end + 1 else input.len;
    }
}

pub fn indentAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
    indent_empty_lines: bool,
) std.mem.Allocator.Error![]u8 {
    return prefixLinesAlloc(allocator, input, "    ", !indent_empty_lines, false);
}

pub fn parseArithmetic(comptime T: type, input: []const u8) ?T {
    if (@typeInfo(T) != .int and @typeInfo(T) != .float) {
        @compileError("parseArithmetic requires an integer or float type");
    }
    if (input.len == 0 or std.ascii.isWhitespace(input[0]) or input[0] == '+') return null;
    if (@typeInfo(T) == .float) return std.fmt.parseFloat(T, input) catch null;

    var end: usize = @intFromBool(input[0] == '-');
    const begin = end;
    while (end < input.len and std.ascii.isDigit(input[end])) end += 1;
    if (end == begin) return null;
    return std.fmt.parseInt(T, input[0..end], 10) catch null;
}

test "Damerau-Levenshtein and suggestion filtering match upstream" {
    try std.testing.expectEqual(@as(usize, 1), try stringDistance(std.testing.allocator, "hello", "helol"));
    try std.testing.expect(try stringWithinDistance(std.testing.allocator, "hello", "helol", 1, 0));
    try std.testing.expect(!(try stringWithinDistance(std.testing.allocator, "abc", "ba", 2, 0)));
}

test "human-readable numbers preserve power and truncation forms" {
    const power = try formatNumberReadableU256Alloc(std.testing.allocator, 0x7ffffff, false);
    defer std.testing.allocator.free(power);
    try std.testing.expectEqualStrings("2**27 - 1", power);

    const mixed = try formatNumberReadableU256Alloc(std.testing.allocator, 0x8888888888000000, false);
    defer std.testing.allocator.free(mixed);
    try std.testing.expectEqualStrings("0x8888888888 * 2**24", mixed);

    var large = try BigInt.parse(
        std.testing.allocator,
        "0xabcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789",
        0,
    );
    defer large.deinit();
    const truncated = try formatNumberReadableAlloc(std.testing.allocator, &large, true);
    defer std.testing.allocator.free(truncated);
    try std.testing.expectEqualStrings("0xABCD...{+56 more}...6789", truncated);
}

test "prefixing and list formatting preserve empty-line behavior" {
    const prefixed = try prefixLinesAlloc(std.testing.allocator, "a\n\nb", "  > ", true, false);
    defer std.testing.allocator.free(prefixed);
    try std.testing.expectEqualStrings("  > a\n  >\n  > b", prefixed);

    const alternatives = try quotedAlternativesListAlloc(std.testing.allocator, &.{ "a", "b", "c" });
    defer std.testing.allocator.free(alternatives);
    try std.testing.expectEqualStrings("\"a\", \"b\" or \"c\"", alternatives);
}
