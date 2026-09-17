// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Coherent structural translation of `SourceLocation.h/.cpp`.
//!
//! Source names are borrowed byte slices. A location must not outlive the
//! source-name owner (normally a `CharStream`, scanner, or compilation arena).

const std = @import("std");

pub const SourceLocation = struct {
    start: i32 = -1,
    end: i32 = -1,
    source_name: ?[]const u8 = null,

    pub fn eql(self: SourceLocation, other: SourceLocation) bool {
        return self.start == other.start and
            self.end == other.end and
            self.equalSources(other);
    }

    pub fn lessThan(self: SourceLocation, other: SourceLocation) bool {
        if (self.source_name == null or other.source_name == null) {
            const self_has_source: u1 = @intFromBool(self.source_name != null);
            const other_has_source: u1 = @intFromBool(other.source_name != null);
            if (self_has_source != other_has_source) {
                return self_has_source < other_has_source;
            }
        } else {
            const source_order = std.mem.order(
                u8,
                self.source_name.?,
                other.source_name.?,
            );
            if (source_order != .eq) return source_order == .lt;
        }
        if (self.start != other.start) return self.start < other.start;
        return self.end < other.end;
    }

    pub fn contains(self: SourceLocation, other: SourceLocation) bool {
        if (!self.hasText() or !other.hasText() or !self.equalSources(other)) {
            return false;
        }
        return self.start <= other.start and other.end <= self.end;
    }

    pub fn containsOffset(self: SourceLocation, position: i32) bool {
        if (!self.hasText() or position < 0) return false;
        return self.start <= position and position < self.end;
    }

    pub fn intersects(self: SourceLocation, other: SourceLocation) bool {
        if (!self.hasText() or !other.hasText() or !self.equalSources(other)) {
            return false;
        }
        return other.start < self.end and self.start < other.end;
    }

    pub fn equalSources(self: SourceLocation, other: SourceLocation) bool {
        if ((self.source_name == null) != (other.source_name == null)) return false;
        if (self.source_name) |source_name| {
            return std.mem.eql(u8, source_name, other.source_name.?);
        }
        return true;
    }

    pub fn isValid(self: SourceLocation) bool {
        return self.source_name != null or self.start != -1 or self.end != -1;
    }

    pub fn hasText(self: SourceLocation) bool {
        return self.source_name != null and self.start >= 0 and self.start <= self.end;
    }

    pub fn smallestCovering(a_value: SourceLocation, b: SourceLocation) SourceLocation {
        var a = a_value;
        if (a.source_name == null) a.source_name = b.source_name;

        if (a.start < 0) {
            a.start = b.start;
        } else if (b.start >= 0 and b.start < a.start) {
            a.start = b.start;
        }
        if (b.end > a.end) a.end = b.end;
        return a;
    }

    /// Returns allocator-owned bytes matching C++ stream rendering.
    pub fn renderAlloc(
        self: SourceLocation,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]u8 {
        if (!self.isValid()) return allocator.dupe(u8, "NO_LOCATION_SPECIFIED");
        if (self.source_name) |source_name| {
            return std.fmt.allocPrint(
                allocator,
                "{s}[{d},{d}]",
                .{ source_name, self.start, self.end },
            );
        }
        return std.fmt.allocPrint(
            allocator,
            "[{d},{d}]",
            .{ self.start, self.end },
        );
    }
};

pub const LineColumn = struct {
    line: i32 = -1,
    column: i32 = -1,
};

pub const ParseError = error{
    InvalidFormat,
    InvalidInteger,
    IntegerOverflow,
    InvalidSourceIndex,
    PositionOverflow,
};

/// Parses `start:length:sourceindex`. Source-name slices are borrowed from
/// `source_names` and retain that storage's lifetime.
pub fn parseSourceLocation(
    input: []const u8,
    source_names: []const []const u8,
) ParseError!SourceLocation {
    var parts: [3][]const u8 = undefined;
    var part_count: usize = 0;
    var iterator = std.mem.splitScalar(u8, input, ':');
    while (iterator.next()) |part| {
        if (part_count == parts.len) return error.InvalidFormat;
        parts[part_count] = part;
        part_count += 1;
    }
    if (part_count != parts.len) return error.InvalidFormat;

    const start = try parseStoi(parts[0]);
    const length = try parseStoi(parts[1]);
    const source_index = try parseStoi(parts[2]);
    const end_wide = @as(i64, start) + @as(i64, length);
    if (end_wide < std.math.minInt(i32) or end_wide > std.math.maxInt(i32)) {
        return error.PositionOverflow;
    }

    var result: SourceLocation = .{
        .start = start,
        .end = @intCast(end_wide),
    };
    if (source_index != -1) {
        if (source_index < 0 or @as(usize, @intCast(source_index)) >= source_names.len) {
            return error.InvalidSourceIndex;
        }
        result.source_name = source_names[@intCast(source_index)];
    }
    return result;
}

/// Compatibility parser for the decimal prefix accepted by `std::stoi`.
fn parseStoi(input: []const u8) ParseError!i32 {
    var index: usize = 0;
    while (index < input.len and isStoiWhitespace(input[index])) : (index += 1) {}

    var negative = false;
    if (index < input.len and (input[index] == '+' or input[index] == '-')) {
        negative = input[index] == '-';
        index += 1;
    }
    const digit_start = index;
    var magnitude: u64 = 0;
    const limit: u64 = if (negative) 2147483648 else 2147483647;
    while (index < input.len and input[index] >= '0' and input[index] <= '9') : (index += 1) {
        const digit: u64 = input[index] - '0';
        if (magnitude > (limit - digit) / 10) return error.IntegerOverflow;
        magnitude = magnitude * 10 + digit;
    }
    if (index == digit_start) return error.InvalidInteger;
    if (negative) {
        if (magnitude == 2147483648) return std.math.minInt(i32);
        return -@as(i32, @intCast(magnitude));
    }
    return @intCast(magnitude);
}

fn isStoiWhitespace(c: u8) bool {
    return c == ' ' or c == '\t' or c == '\n' or
        c == '\r' or c == 0x0b or c == 0x0c;
}

test "source location interval and ordering behavior" {
    const source = "source";
    const source_a = "sourceA";
    const source_b = "sourceB";
    try std.testing.expect((SourceLocation{}).eql(.{}));
    try std.testing.expect(!(@as(SourceLocation, .{
        .start = 0,
        .end = 3,
        .source_name = source_a,
    })).eql(.{ .start = 0, .end = 3, .source_name = source_b }));
    try std.testing.expect((@as(SourceLocation, .{
        .start = 3,
        .end = 7,
        .source_name = source,
    })).contains(.{ .start = 4, .end = 6, .source_name = source }));
    try std.testing.expect((@as(SourceLocation, .{
        .start = 3,
        .end = 7,
        .source_name = source_a,
    })).lessThan(.{ .start = 4, .end = 6, .source_name = source_b }));
}

test "source location parsing and rendering" {
    const names = [_][]const u8{ "a.sol", "b.sol" };
    const location = try parseSourceLocation(" 4junk:3:1suffix", &names);
    try std.testing.expectEqual(@as(i32, 4), location.start);
    try std.testing.expectEqual(@as(i32, 7), location.end);
    try std.testing.expectEqualStrings("b.sol", location.source_name.?);

    const rendered = try location.renderAlloc(std.testing.allocator);
    defer std.testing.allocator.free(rendered);
    try std.testing.expectEqualStrings("b.sol[4,7]", rendered);
    try std.testing.expectError(
        error.InvalidSourceIndex,
        parseSourceLocation("0:0:2", &names),
    );
}
