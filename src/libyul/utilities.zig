// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Literal, ordering, name-resolution, and text helpers translated from
//! `libyul/Utilities.cpp`.

const std = @import("std");
const common_data = @import("../libsolutil/common_data.zig");
const AST = @import("ast.zig");

pub const LiteralError = std.mem.Allocator.Error || error{
    InvalidNumberLiteral,
    UnexpectedBoolLiteral,
    InvalidLiteral,
};

pub fn reindent(
    allocator: std.mem.Allocator,
    code: []const u8,
) std.mem.Allocator.Error![]u8 {
    const indentation_width = 4;
    const whitespace = " \t\r\n\x0b\x0c";

    var lines: std.ArrayList([]const u8) = .empty;
    defer lines.deinit(allocator);
    var iterator = std.mem.splitScalar(u8, code, '\n');
    while (iterator.next()) |raw_line| {
        const line = std.mem.trim(u8, raw_line, whitespace);
        if (!(line.len == 0 and lines.items.len != 0 and lines.items[lines.items.len - 1].len == 0))
            try lines.append(allocator, line);
    }

    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var depth: i32 = 0;
    for (lines.items) |line| {
        const diff = braceDifference(line);
        if (diff < 0) depth += diff;
        if (line.len != 0) {
            const indentation: usize = if (depth <= 0)
                0
            else
                @as(usize, @intCast(depth)) * indentation_width;
            try output.appendNTimes(allocator, ' ', indentation);
            try output.appendSlice(allocator, line);
        }
        try output.append(allocator, '\n');
        if (diff > 0) depth += diff;
    }
    return output.toOwnedSlice(allocator);
}

fn braceDifference(line: []const u8) i32 {
    const code = line[0 .. std.mem.find(u8, line, "//") orelse line.len];
    var opening: i32 = 0;
    var closing: i32 = 0;
    for (code) |character| switch (character) {
        '{', '(' => opening += 1,
        '}', ')' => closing += 1,
        else => {},
    };
    return opening - closing;
}

pub fn valueOfNumberLiteral(
    allocator: std.mem.Allocator,
    literal: []const u8,
) LiteralError!AST.LiteralValue {
    const value = parseNumberLiteral(literal) orelse return error.InvalidNumberLiteral;
    return AST.LiteralValue.initNumeric(allocator, value, literal);
}

pub fn valueOfStringLiteral(
    allocator: std.mem.Allocator,
    literal: []const u8,
) std.mem.Allocator.Error!AST.LiteralValue {
    var bytes: [32]u8 = @splat(0);
    const copied = @min(bytes.len, literal.len);
    @memcpy(bytes[0..copied], literal[0..copied]);
    return AST.LiteralValue.initNumeric(
        allocator,
        std.mem.readInt(u256, &bytes, .big),
        literal,
    );
}

pub fn valueOfBuiltinStringLiteralArgument(
    allocator: std.mem.Allocator,
    literal: []const u8,
) std.mem.Allocator.Error!AST.LiteralValue {
    return AST.LiteralValue.initBuiltinString(allocator, literal);
}

pub fn valueOfBoolLiteral(
    allocator: std.mem.Allocator,
    literal: []const u8,
) LiteralError!AST.LiteralValue {
    if (std.mem.eql(u8, literal, "true"))
        return AST.LiteralValue.initNumeric(allocator, 1, null);
    if (std.mem.eql(u8, literal, "false"))
        return AST.LiteralValue.initNumeric(allocator, 0, null);
    return error.UnexpectedBoolLiteral;
}

pub fn valueOfLiteral(
    allocator: std.mem.Allocator,
    literal: []const u8,
    kind: AST.LiteralKind,
    unlimited_literal_argument: bool,
) LiteralError!AST.LiteralValue {
    return switch (kind) {
        .Number => valueOfNumberLiteral(allocator, literal),
        .Boolean => valueOfBoolLiteral(allocator, literal),
        .String => if (unlimited_literal_argument)
            valueOfBuiltinStringLiteralArgument(allocator, literal)
        else
            valueOfStringLiteral(allocator, literal),
    };
}

pub fn validLiteral(literal: *const AST.Literal) bool {
    return switch (literal.kind) {
        .Number => validNumberLiteral(literal),
        .Boolean => validBoolLiteral(literal),
        .String => validStringLiteral(literal),
    };
}

pub fn validStringLiteral(literal: *const AST.Literal) bool {
    if (literal.kind != .String) return false;
    if (literal.value.unlimited()) return true;
    const hint = literal.value.hint() catch return false;
    if (hint) |representation| {
        if (representation.len > 32) return false;
        var bytes: [32]u8 = @splat(0);
        @memcpy(bytes[0..representation.len], representation);
        return literal.value.numeric_value.? == std.mem.readInt(u256, &bytes, .big);
    }
    return true;
}

pub fn validNumberLiteral(literal: *const AST.Literal) bool {
    if (literal.kind != .Number or literal.value.unlimited()) return false;
    const hint = literal.value.hint() catch return false;
    const representation = hint orelse return true;
    if (!common_data.isValidDecimal(representation) and !common_data.isValidHex(representation))
        return false;
    const parsed = parseNumberLiteral(representation) orelse return false;
    return literal.value.numeric_value.? == parsed;
}

pub fn validBoolLiteral(literal: *const AST.Literal) bool {
    if (literal.kind != .Boolean or literal.value.unlimited()) return false;
    const value = literal.value.numeric_value.?;
    const hint = literal.value.hint() catch return false;
    if (hint) |representation| {
        if (std.mem.eql(u8, representation, "false")) return value == 0;
        if (std.mem.eql(u8, representation, "true")) return value == 1;
        return false;
    }
    return value == 0 or value == 1;
}

pub fn formatLiteralAlloc(
    allocator: std.mem.Allocator,
    literal: *const AST.Literal,
    validated: bool,
) LiteralError![]u8 {
    if (validated and !validLiteral(literal)) return error.InvalidLiteral;
    if (literal.value.unlimited())
        return allocator.dupe(u8, literal.value.builtinStringLiteralValue() catch return error.InvalidLiteral);
    if (literal.value.hint() catch return error.InvalidLiteral) |representation|
        return allocator.dupe(u8, representation);
    if (literal.kind == .Boolean)
        return allocator.dupe(u8, if (literal.value.numeric_value.? == 0) "false" else "true");
    return std.fmt.allocPrint(allocator, "{d}", .{literal.value.numeric_value.?});
}

pub fn literalLessThan(left: *const AST.Literal, right: *const AST.Literal) bool {
    if (left.kind != right.kind) return @intFromEnum(left.kind) < @intFromEnum(right.kind);
    return left.value.lessThan(&right.value);
}

pub fn switchCaseLessThan(left: *const AST.Case, right: *const AST.Case) bool {
    if (left.value == null or right.value == null) return left.value == null and right.value != null;
    return literalLessThan(left.value.?, right.value.?);
}

pub fn resolveFunctionName(
    function_name: *const AST.FunctionName,
    dialect: AST.Dialect,
) error{ InvalidYulStringHandle, UnknownBuiltin }![]const u8 {
    return switch (function_name.*) {
        .identifier => |identifier| identifier.name.str(),
        .builtin => |builtin_name| (try dialect.builtin(builtin_name.handle)).name,
    };
}

pub fn resolveFunctionHandle(
    function_handle: *const AST.FunctionHandle,
    dialect: AST.Dialect,
) error{ InvalidYulStringHandle, UnknownBuiltin }![]const u8 {
    return switch (function_handle.*) {
        .user => |name| name.str(),
        .builtin => |handle| (try dialect.builtin(handle)).name,
    };
}

pub fn resolveBuiltinFunction(
    function_name: *const AST.FunctionName,
    dialect: AST.Dialect,
) error{UnknownBuiltin}!?*const AST.BuiltinFunction {
    return switch (function_name.*) {
        .identifier => null,
        .builtin => |builtin_name| try dialect.builtin(builtin_name.handle),
    };
}

/// EVM-specialized counterpart without importing the concrete dialect. Keeping
/// this generic avoids the upstream Object -> Parser -> Utilities dependency
/// cycle while preserving the concrete pointer type at each call site.
pub fn resolveBuiltinFunctionForEVM(
    function_name: *const AST.FunctionName,
    dialect: anytype,
) error{UnknownBuiltin}!@TypeOf(dialect.builtin(.{ .id = 0 })) {
    return switch (function_name.*) {
        .identifier => null,
        .builtin => |builtin_name| dialect.builtin(builtin_name.handle) orelse error.UnknownBuiltin,
    };
}

pub fn functionNameToHandle(function_name: *const AST.FunctionName) AST.FunctionHandle {
    return switch (function_name.*) {
        .identifier => |identifier| .{ .user = identifier.name },
        .builtin => |builtin_name| .{ .builtin = builtin_name.handle },
    };
}

fn parseNumberLiteral(literal: []const u8) ?u256 {
    if (std.mem.startsWith(u8, literal, "0x")) {
        if (literal.len == 2) return null;
        return std.fmt.parseUnsigned(u256, literal[2..], 16) catch null;
    }
    return std.fmt.parseUnsigned(u256, literal, 10) catch null;
}

test "literal parsing, validation, formatting, and ordering preserve Yul semantics" {
    const allocator = std.testing.allocator;
    var number: AST.Literal = .{
        .kind = .Number,
        .value = try valueOfNumberLiteral(allocator, "0x2a"),
    };
    defer number.deinit(allocator);
    try std.testing.expect(validLiteral(&number));
    const formatted_number = try formatLiteralAlloc(allocator, &number, true);
    defer allocator.free(formatted_number);
    try std.testing.expectEqualStrings("0x2a", formatted_number);

    var string: AST.Literal = .{
        .kind = .String,
        .value = try valueOfStringLiteral(allocator, "abc"),
    };
    defer string.deinit(allocator);
    try std.testing.expect(validLiteral(&string));
    try std.testing.expect(literalLessThan(&number, &string));

    var invalid_long: AST.Literal = .{
        .kind = .String,
        .value = try valueOfStringLiteral(allocator, "123456789012345678901234567890123"),
    };
    defer invalid_long.deinit(allocator);
    try std.testing.expect(!validLiteral(&invalid_long));
}

test "reindent follows braces and collapses repeated empty lines" {
    const formatted = try reindent(std.testing.allocator, " {\n let x := f(\n1\n )\n\n\n } // }\n");
    defer std.testing.allocator.free(formatted);
    try std.testing.expectEqualStrings(
        "{\n    let x := f(\n        1\n    )\n\n} // }\n\n",
        formatted,
    );
}
