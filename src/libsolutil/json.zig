// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned JSON helpers translated from `JSON.cpp` and `JSON.h`.
//!
//! Parsing uses `std.json.Value` behind an explicit document owner. Printing
//! sorts object keys to preserve nlohmann's default `std::map` ordering and
//! always escapes non-ASCII code points.

const std = @import("std");

pub const Json = std.json.Value;

pub const JsonFormat = struct {
    pub const Format = enum {
        compact,
        pretty,
    };

    pub const default_indent: u32 = 2;

    format: Format = .compact,
    indent: u32 = default_indent,
};

pub const JsonDocument = struct {
    const Self = @This();

    parsed: std.json.Parsed(Json),

    pub fn root(self: *Self) *Json {
        return &self.parsed.value;
    }

    pub fn rootConst(self: *const Self) *const Json {
        return &self.parsed.value;
    }

    pub fn deinit(self: *Self) void {
        self.parsed.deinit();
        self.* = undefined;
    }
};

pub const ParseFailure = struct {
    allocator: std.mem.Allocator,
    message: []u8,

    pub fn deinit(self: *@This()) void {
        self.allocator.free(self.message);
        self.* = undefined;
    }
};

/// The C++ API reports syntax failures through its boolean return and `_errs`
/// output. This union makes both outcomes explicit while reserving the error
/// return for allocation failure.
pub const StrictParseResult = union(enum) {
    document: JsonDocument,
    failure: ParseFailure,

    pub fn deinit(self: *@This()) void {
        switch (self.*) {
            .document => |*document| document.deinit(),
            .failure => |*failure| failure.deinit(),
        }
        self.* = undefined;
    }
};

const PreprocessError = std.mem.Allocator.Error || error{UnterminatedComment};

/// Parses one complete JSON value, accepts C/C++ comments, applies the
/// upstream compatibility escape for raw newlines/tabs inside strings, and
/// lets the last duplicate object member win.
pub fn jsonParseStrict(
    allocator: std.mem.Allocator,
    input: []const u8,
) std.mem.Allocator.Error!StrictParseResult {
    const fixed = preprocessInput(allocator, input) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.UnterminatedComment => return parseFailure(allocator, "unterminated JSON comment"),
    };
    defer allocator.free(fixed);

    const parsed = std.json.parseFromSlice(Json, allocator, fixed, .{
        .duplicate_field_behavior = .use_last,
        .allocate = .alloc_always,
        .max_value_len = fixed.len,
    }) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return parseFailureName(allocator, err),
    };
    return .{ .document = .{ .parsed = parsed } };
}

fn parseFailure(
    allocator: std.mem.Allocator,
    message: []const u8,
) std.mem.Allocator.Error!StrictParseResult {
    return .{ .failure = .{
        .allocator = allocator,
        .message = try allocator.dupe(u8, message),
    } };
}

fn parseFailureName(
    allocator: std.mem.Allocator,
    err: anyerror,
) std.mem.Allocator.Error!StrictParseResult {
    const message = try std.fmt.allocPrint(allocator, "JSON parse error: {s}", .{@errorName(err)});
    return .{ .failure = .{ .allocator = allocator, .message = message } };
}

fn preprocessInput(
    allocator: std.mem.Allocator,
    input: []const u8,
) PreprocessError![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.ensureTotalCapacity(allocator, input.len);

    var index: usize = 0;
    var in_string = false;
    var escaped = false;
    while (index < input.len) {
        const byte = input[index];
        if (in_string) {
            switch (byte) {
                '\n' => {
                    try output.appendSlice(allocator, "\\n");
                    escaped = false;
                },
                '\t' => {
                    try output.appendSlice(allocator, "\\t");
                    escaped = false;
                },
                '\\' => {
                    try output.append(allocator, byte);
                    escaped = !escaped;
                },
                '"' => {
                    try output.append(allocator, byte);
                    if (!escaped) in_string = false;
                    escaped = false;
                },
                else => {
                    try output.append(allocator, byte);
                    escaped = false;
                },
            }
            index += 1;
            continue;
        }

        if (byte == '"') {
            in_string = true;
            escaped = false;
            try output.append(allocator, byte);
            index += 1;
            continue;
        }

        if (byte == '/' and index + 1 < input.len and input[index + 1] == '/') {
            try output.appendSlice(allocator, "  ");
            index += 2;
            while (index < input.len and input[index] != '\n') : (index += 1)
                try output.append(allocator, ' ');
            continue;
        }

        if (byte == '/' and index + 1 < input.len and input[index + 1] == '*') {
            try output.appendSlice(allocator, "  ");
            index += 2;
            var terminated = false;
            while (index < input.len) {
                if (input[index] == '*' and index + 1 < input.len and input[index + 1] == '/') {
                    try output.appendSlice(allocator, "  ");
                    index += 2;
                    terminated = true;
                    break;
                }
                try output.append(allocator, if (input[index] == '\n') '\n' else ' ');
                index += 1;
            }
            if (!terminated) return error.UnterminatedComment;
            continue;
        }

        // nlohmann accepts a UTF-8 BOM at the beginning of a document.
        if (index == 0 and input.len >= 3 and std.mem.eql(u8, input[0..3], "\xef\xbb\xbf")) {
            try output.appendSlice(allocator, "   ");
            index = 3;
            continue;
        }

        try output.append(allocator, byte);
        index += 1;
    }
    return output.toOwnedSlice(allocator);
}

pub const JsonPrintError = std.mem.Allocator.Error || error{IndentationTooLarge};

pub fn jsonPrettyPrintAlloc(
    allocator: std.mem.Allocator,
    input: *const Json,
) JsonPrintError![]u8 {
    return jsonPrintAlloc(allocator, input, .{ .format = .pretty });
}

pub fn jsonCompactPrintAlloc(
    allocator: std.mem.Allocator,
    input: *const Json,
) JsonPrintError![]u8 {
    return jsonPrintAlloc(allocator, input, .{});
}

pub fn jsonPrintAlloc(
    allocator: std.mem.Allocator,
    input: *const Json,
    format: JsonFormat,
) JsonPrintError![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendValue(allocator, &output, input, format, 0);
    return output.toOwnedSlice(allocator);
}

fn appendValue(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    value: *const Json,
    format: JsonFormat,
    depth: usize,
) JsonPrintError!void {
    switch (value.*) {
        .null => try output.appendSlice(allocator, "null"),
        .bool => |boolean| try output.appendSlice(allocator, if (boolean) "true" else "false"),
        .integer => |integer| try appendFormatted(allocator, output, "{d}", .{integer}),
        .float => |number| try appendFloat(allocator, output, number),
        .number_string => |number| try output.appendSlice(allocator, number),
        .string => |string| try appendString(allocator, output, string),
        .array => |array| {
            try output.append(allocator, '[');
            if (array.items.len != 0) {
                for (array.items, 0..) |*element, index| {
                    if (index != 0) try output.append(allocator, ',');
                    if (format.format == .pretty) {
                        try output.append(allocator, '\n');
                        try appendIndent(allocator, output, format.indent, depth + 1);
                    }
                    try appendValue(allocator, output, element, format, depth + 1);
                }
                if (format.format == .pretty) {
                    try output.append(allocator, '\n');
                    try appendIndent(allocator, output, format.indent, depth);
                }
            }
            try output.append(allocator, ']');
        },
        .object => |object| {
            try output.append(allocator, '{');
            if (object.count() != 0) {
                const indices = try allocator.alloc(usize, object.count());
                defer allocator.free(indices);
                for (indices, 0..) |*slot, index| slot.* = index;
                const keys = object.keys();
                for (1..indices.len) |index| {
                    const selected = indices[index];
                    var position = index;
                    while (position != 0 and std.mem.order(
                        u8,
                        keys[selected],
                        keys[indices[position - 1]],
                    ) == .lt) {
                        indices[position] = indices[position - 1];
                        position -= 1;
                    }
                    indices[position] = selected;
                }

                for (indices, 0..) |object_index, output_index| {
                    if (output_index != 0) try output.append(allocator, ',');
                    if (format.format == .pretty) {
                        try output.append(allocator, '\n');
                        try appendIndent(allocator, output, format.indent, depth + 1);
                    }
                    try appendString(allocator, output, keys[object_index]);
                    try output.appendSlice(
                        allocator,
                        if (format.format == .pretty) ": " else ":",
                    );
                    try appendValue(
                        allocator,
                        output,
                        &object.values()[object_index],
                        format,
                        depth + 1,
                    );
                }
                if (format.format == .pretty) {
                    try output.append(allocator, '\n');
                    try appendIndent(allocator, output, format.indent, depth);
                }
            }
            try output.append(allocator, '}');
        },
    }
}

fn appendFormatted(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    comptime format: []const u8,
    args: anytype,
) std.mem.Allocator.Error!void {
    const formatted = try std.fmt.allocPrint(allocator, format, args);
    defer allocator.free(formatted);
    try output.appendSlice(allocator, formatted);
}

fn appendFloat(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    value: f64,
) std.mem.Allocator.Error!void {
    const encoded = try std.json.Stringify.valueAlloc(allocator, value, .{});
    defer allocator.free(encoded);
    try output.appendSlice(allocator, encoded);
}

fn appendString(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    value: []const u8,
) std.mem.Allocator.Error!void {
    const encoded = try std.json.Stringify.valueAlloc(allocator, value, .{
        .escape_unicode = true,
    });
    defer allocator.free(encoded);
    try output.appendSlice(allocator, encoded);
}

fn appendIndent(
    allocator: std.mem.Allocator,
    output: *std.ArrayList(u8),
    indent: u32,
    depth: usize,
) JsonPrintError!void {
    const count = std.math.mul(usize, depth, indent) catch
        return error.IndentationTooLarge;
    try output.appendNTimes(allocator, ' ', count);
}

/// Removes null-valued object members recursively. Null array elements remain,
/// exactly as in the C++ helper.
pub fn removeNullMembers(value: *Json) void {
    switch (value.*) {
        .array => |*array| for (array.items) |*element| removeNullMembers(element),
        .object => |*object| {
            var index: usize = 0;
            while (index < object.count()) {
                if (object.values()[index] == .null) {
                    object.orderedRemoveAt(index);
                } else {
                    removeNullMembers(&object.values()[index]);
                    index += 1;
                }
            }
        },
        else => {},
    }
}

/// Returns a borrowed value at a dot-separated object path.
pub fn jsonValueByPath(node: *const Json, json_path: []const u8) ?*const Json {
    if (json_path.len == 0) return null;
    const object = switch (node.*) {
        .object => |*object| object,
        else => return null,
    };
    const separator = std.mem.findScalar(u8, json_path, '.');
    const member_name = json_path[0 .. separator orelse json_path.len];
    const member = object.getPtr(member_name) orelse return null;
    if (separator == null) return member;
    return jsonValueByPath(member, json_path[separator.? + 1 ..]);
}

pub fn removeNlohmannInternalErrorIdentifierAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
) std.mem.Allocator.Error![]u8 {
    const start = std.mem.findScalar(u8, input, '[');
    var raw: []u8 = undefined;
    if (start) |start_index| {
        if (std.mem.findScalarPos(u8, input, start_index, ']')) |end_index| {
            raw = try allocator.alloc(u8, input.len - (end_index - start_index + 1));
            @memcpy(raw[0..start_index], input[0..start_index]);
            @memcpy(raw[start_index..], input[end_index + 1 ..]);
        } else {
            raw = try allocator.dupe(u8, input);
        }
    } else {
        raw = try allocator.dupe(u8, input);
    }
    errdefer allocator.free(raw);
    const trimmed = std.mem.trim(u8, raw, " \t\r\n");
    if (trimmed.ptr == raw.ptr and trimmed.len == raw.len) return raw;
    const result = try allocator.dupe(u8, trimmed);
    allocator.free(raw);
    return result;
}

pub fn isOfType(comptime T: type, input: *const Json) bool {
    if (T == []const u8) return input.* == .string;
    return switch (@typeInfo(T)) {
        .bool => input.* == .bool,
        .int => integerValue(T, input) != null,
        .float => floatValue(T, input) != null,
        else => @compileError("unsupported JSON conversion type " ++ @typeName(T)),
    };
}

pub fn isOfTypeIfExists(
    comptime T: type,
    input: *const Json,
    name: []const u8,
) bool {
    const member = objectMember(input, name) orelse return true;
    return isOfType(T, member);
}

pub fn get(comptime T: type, input: *const Json) error{InvalidType}!T {
    if (T == []const u8) return switch (input.*) {
        .string => |string| string,
        else => error.InvalidType,
    };
    return switch (@typeInfo(T)) {
        .bool => switch (input.*) {
            .bool => |boolean| boolean,
            else => error.InvalidType,
        },
        .int => integerValue(T, input) orelse error.InvalidType,
        .float => floatValue(T, input) orelse error.InvalidType,
        else => @compileError("unsupported JSON conversion type " ++ @typeName(T)),
    };
}

pub fn getOrDefault(
    comptime T: type,
    input: *const Json,
    name: []const u8,
    default: T,
) T {
    const member = objectMember(input, name) orelse return default;
    return get(T, member) catch default;
}

fn objectMember(input: *const Json, name: []const u8) ?*const Json {
    return switch (input.*) {
        .object => |*object| object.getPtr(name),
        else => null,
    };
}

fn integerValue(comptime T: type, input: *const Json) ?T {
    const info = @typeInfo(T).int;
    return switch (input.*) {
        .integer => |integer| std.math.cast(T, integer),
        .number_string => |number| if (!std.json.isNumberFormattedLikeAnInteger(number))
            null
        else if (info.signedness == .signed)
            std.fmt.parseInt(T, number, 10) catch null
        else
            std.fmt.parseUnsigned(T, number, 10) catch null,
        else => null,
    };
}

fn floatValue(comptime T: type, input: *const Json) ?T {
    const number: f64 = switch (input.*) {
        .integer => |integer| @floatFromInt(integer),
        .float => |float| float,
        .number_string => |string| std.fmt.parseFloat(f64, string) catch return null,
        else => return null,
    };
    if (!std.math.isFinite(number)) return null;
    if (T == f32 and (number < std.math.floatMin(f32) or number > std.math.floatMax(f32)))
        return null;
    return @floatCast(number);
}

fn expectDocument(result: *StrictParseResult) !*JsonDocument {
    return switch (result.*) {
        .document => |*document| document,
        .failure => error.TestUnexpectedResult,
    };
}

test "strict parsing accepts comments, duplicate fields, and raw string whitespace" {
    var result = try jsonParseStrict(
        std.testing.allocator,
        "/* lead */ {\"b\": 1, // old\n\"b\": 2, \"s\": \"a\n\tb\"}",
    );
    defer result.deinit();
    const document = try expectDocument(&result);
    try std.testing.expectEqual(@as(i64, 2), try get(i64, objectMember(document.rootConst(), "b").?));
    try std.testing.expectEqualStrings("a\n\tb", try get([]const u8, objectMember(document.rootConst(), "s").?));
}

test "strict parsing rejects trailing garbage and unterminated comments" {
    var trailing = try jsonParseStrict(std.testing.allocator, "{} trailing");
    defer trailing.deinit();
    try std.testing.expect(trailing == .failure);

    var comment = try jsonParseStrict(std.testing.allocator, "{} /*");
    defer comment.deinit();
    try std.testing.expect(comment == .failure);
}

test "printing sorts keys, escapes Unicode, and honors arbitrary indentation" {
    var result = try jsonParseStrict(
        std.testing.allocator,
        "{\"z\":\"ऑ\",\"a\":{\"x\":1}}",
    );
    defer result.deinit();
    const document = try expectDocument(&result);
    const compact = try jsonCompactPrintAlloc(std.testing.allocator, document.rootConst());
    defer std.testing.allocator.free(compact);
    try std.testing.expectEqualStrings("{\"a\":{\"x\":1},\"z\":\"\\u0911\"}", compact);

    const pretty = try jsonPrintAlloc(
        std.testing.allocator,
        document.rootConst(),
        .{ .format = .pretty, .indent = 3 },
    );
    defer std.testing.allocator.free(pretty);
    try std.testing.expectEqualStrings(
        "{\n" ++
            "   \"a\": {\n" ++
            "      \"x\": 1\n" ++
            "   },\n" ++
            "   \"z\": \"\\u0911\"\n" ++
            "}",
        pretty,
    );
}

test "null object members are removed but null array entries remain" {
    var result = try jsonParseStrict(
        std.testing.allocator,
        "{\"a\":null,\"b\":[null,{\"c\":null,\"d\":1}]}",
    );
    defer result.deinit();
    const document = try expectDocument(&result);
    removeNullMembers(document.root());
    const compact = try jsonCompactPrintAlloc(std.testing.allocator, document.rootConst());
    defer std.testing.allocator.free(compact);
    try std.testing.expectEqualStrings("{\"b\":[null,{\"d\":1}]}", compact);
}

test "path lookup and checked numeric conversions" {
    var result = try jsonParseStrict(
        std.testing.allocator,
        "{\"a\":{\"b\":255},\"large\":18446744073709551615,\"negative\":-1}",
    );
    defer result.deinit();
    const document = try expectDocument(&result);
    try std.testing.expectEqual(@as(u8, 255), try get(u8, jsonValueByPath(document.rootConst(), "a.b").?));
    try std.testing.expect(!isOfType(u8, jsonValueByPath(document.rootConst(), "large").?));
    try std.testing.expectEqual(
        std.math.maxInt(u64),
        try get(u64, jsonValueByPath(document.rootConst(), "large").?),
    );
    try std.testing.expect(!isOfType(u64, jsonValueByPath(document.rootConst(), "negative").?));
    try std.testing.expect(jsonValueByPath(document.rootConst(), "a.missing") == null);
}

test "nlohmann error identifiers are removed and trimmed" {
    const cleaned = try removeNlohmannInternalErrorIdentifierAlloc(
        std.testing.allocator,
        "  [json.exception.parse_error.101] unexpected token  ",
    );
    defer std.testing.allocator.free(cleaned);
    try std.testing.expectEqualStrings("unexpected token", cleaned);
}
