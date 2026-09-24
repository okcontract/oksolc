// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Coherent structural translation of `CharStream.h/.cpp`.

const std = @import("std");
const locations = @import("source_location.zig");

pub const SourceLocation = locations.SourceLocation;
pub const LineColumn = locations.LineColumn;

pub const PositionError = error{
    PositionOutOfBounds,
    InvalidRollback,
    LocationSourceMismatch,
    LocationEndOutOfBounds,
};

pub const CharStream = struct {
    source_bytes: []const u8 = "",
    name_bytes: []const u8 = "",
    imported_from_ast: bool = false,
    position_value: usize = 0,
    owner_allocator: ?std.mem.Allocator = null,

    /// Creates a stream borrowing both byte slices. They must remain stable for
    /// the stream's lifetime and for all locations derived from it.
    pub fn initBorrowed(source_bytes: []const u8, name_bytes: []const u8) CharStream {
        return .{ .source_bytes = source_bytes, .name_bytes = name_bytes };
    }

    /// Creates a stream owning copies of source and name. Call `deinit`.
    pub fn initOwned(
        allocator: std.mem.Allocator,
        source_bytes: []const u8,
        name_bytes: []const u8,
        imported_from_ast: bool,
    ) std.mem.Allocator.Error!CharStream {
        const owned_source = try allocator.dupe(u8, source_bytes);
        errdefer allocator.free(owned_source);
        const owned_name = try allocator.dupe(u8, name_bytes);
        errdefer allocator.free(owned_name);
        return .{
            .source_bytes = owned_source,
            .name_bytes = owned_name,
            .imported_from_ast = imported_from_ast,
            .owner_allocator = allocator,
        };
    }

    pub fn deinit(self: *CharStream) void {
        if (self.owner_allocator) |allocator| {
            allocator.free(self.source_bytes);
            allocator.free(self.name_bytes);
        }
        self.* = undefined;
    }

    pub fn position(self: *const CharStream) usize {
        return self.position_value;
    }

    pub fn isPastEndOfInput(self: *const CharStream, chars_forward: usize) bool {
        if (self.position_value >= self.source_bytes.len) return true;
        return chars_forward >= self.source_bytes.len - self.position_value;
    }

    pub fn isImportedFromAST(self: *const CharStream) bool {
        return self.imported_from_ast;
    }

    /// Matches `std::string::operator[]`: the byte at exactly `size()` is the
    /// terminating zero. Larger offsets are rejected.
    pub fn get(self: *const CharStream, chars_forward: usize) PositionError!u8 {
        if (chars_forward > std.math.maxInt(usize) - self.position_value) {
            return error.PositionOutOfBounds;
        }
        const index = self.position_value + chars_forward;
        if (index > self.source_bytes.len) return error.PositionOutOfBounds;
        if (index == self.source_bytes.len) return 0;
        return self.source_bytes[index];
    }

    pub fn advanceAndGet(self: *CharStream, chars: usize) u8 {
        if (self.isPastEndOfInput(0)) return 0;
        self.position_value += chars;
        if (self.isPastEndOfInput(0)) return 0;
        return self.source_bytes[self.position_value];
    }

    pub fn rollback(self: *CharStream, amount: usize) PositionError!u8 {
        if (amount > self.position_value) return error.InvalidRollback;
        self.position_value -= amount;
        return self.get(0);
    }

    pub fn setPosition(self: *CharStream, location: usize) PositionError!u8 {
        if (location > self.source_bytes.len) return error.PositionOutOfBounds;
        self.position_value = location;
        return self.get(0);
    }

    pub fn reset(self: *CharStream) void {
        self.position_value = 0;
    }

    pub fn source(self: *const CharStream) []const u8 {
        return self.source_bytes;
    }

    pub fn name(self: *const CharStream) []const u8 {
        return self.name_bytes;
    }

    pub fn size(self: *const CharStream) usize {
        return self.source_bytes.len;
    }

    /// Returns allocator-owned line bytes. If `position` points to `\n`, the
    /// preceding line is returned, matching the original implementation.
    pub fn lineAtPositionAlloc(
        self: *const CharStream,
        allocator: std.mem.Allocator,
        position_input: i32,
    ) std.mem.Allocator.Error![]u8 {
        var search_start = if (position_input < 0)
            self.source_bytes.len
        else
            @min(self.source_bytes.len, @as(usize, @intCast(position_input)));
        if (search_start > 0) search_start -= 1;

        const line_start = if (std.mem.findScalarLast(
            u8,
            self.source_bytes[0..@min(search_start + 1, self.source_bytes.len)],
            '\n',
        )) |index|
            index + 1
        else
            0;
        const line_end = if (std.mem.findScalar(
            u8,
            self.source_bytes[line_start..],
            '\n',
        )) |relative|
            line_start + relative
        else
            self.source_bytes.len;
        var effective_end = line_end;
        if (effective_end > line_start and self.source_bytes[effective_end - 1] == '\r') {
            effective_end -= 1;
        }
        return allocator.dupe(u8, self.source_bytes[line_start..effective_end]);
    }

    pub fn translatePositionToLineColumn(
        self: *const CharStream,
        position_input: i32,
    ) LineColumn {
        const search_position = if (position_input < 0)
            self.source_bytes.len
        else
            @min(self.source_bytes.len, @as(usize, @intCast(position_input)));
        var line_number: i32 = 0;
        for (self.source_bytes[0..search_position]) |c| {
            if (c == '\n') line_number += 1;
        }
        const line_start = if (search_position == 0)
            0
        else if (std.mem.findScalarLast(
            u8,
            self.source_bytes[0..search_position],
            '\n',
        )) |index|
            index + 1
        else
            0;
        return .{
            .line = line_number,
            .column = @intCast(search_position - line_start),
        };
    }

    pub fn translateLineColumnToPosition(
        self: *const CharStream,
        line_column: LineColumn,
    ) ?i32 {
        return translateLineColumnToPositionInText(self.source_bytes, line_column);
    }

    pub fn prefixMatch(self: *const CharStream, sequence: []const u8) bool {
        if (self.isPastEndOfInput(sequence.len)) return false;
        for (sequence, 0..) |expected, index| {
            const actual = self.get(index) catch return false;
            if (actual != expected) return false;
        }
        return true;
    }

    /// Returns a borrowed view into the source. It remains valid until this
    /// stream is deinitialized. Invalid/no-text locations return an empty view.
    pub fn text(
        self: *const CharStream,
        location: SourceLocation,
    ) PositionError![]const u8 {
        if (!location.hasText()) return "";
        if (!std.mem.eql(u8, location.source_name.?, self.name_bytes)) {
            return error.LocationSourceMismatch;
        }
        if (@as(usize, @intCast(location.end)) > self.source_bytes.len) {
            return error.LocationEndOutOfBounds;
        }
        return self.source_bytes[@as(usize, @intCast(location.start))..@as(usize, @intCast(location.end))];
    }

    pub fn singleLineSnippetAlloc(
        self: *const CharStream,
        allocator: std.mem.Allocator,
        location: SourceLocation,
    ) std.mem.Allocator.Error![]u8 {
        return singleLineSnippetFromTextAlloc(allocator, self.source_bytes, location);
    }

    /// Borrows source bytes until this stream is deinitialized or its source is
    /// replaced. Snippet bounds deliberately remain more permissive than text().
    pub fn singleLineSnippet(self: *const CharStream, location: SourceLocation) SingleLineSnippet {
        return singleLineSnippetFromText(self.source_bytes, location);
    }
};

pub fn translateLineColumnToPositionInText(
    text_bytes: []const u8,
    input: LineColumn,
) ?i32 {
    if (input.line < 0) return null;
    var offset: usize = 0;
    var line: i32 = 0;
    while (line < input.line) : (line += 1) {
        const relative = std.mem.findScalar(u8, text_bytes[offset..], '\n') orelse
            return null;
        offset += relative + 1;
    }
    const end_of_line = if (std.mem.findScalar(u8, text_bytes[offset..], '\n')) |relative|
        offset + relative
    else
        text_bytes.len;
    // Upstream casts the signed column to `size_t` and adds it before the
    // bounds check. Preserve that defined unsigned wraparound, including its
    // surprising acceptance of a negative column when it wraps into a prior
    // byte position.
    const column: usize = @bitCast(@as(isize, input.column));
    const result = offset +% column;
    if (result > end_of_line) return null;
    return @bitCast(@as(u32, @truncate(result)));
}

pub fn singleLineSnippetFromTextAlloc(
    allocator: std.mem.Allocator,
    source_code: []const u8,
    location: SourceLocation,
) std.mem.Allocator.Error![]u8 {
    const snippet = singleLineSnippetFromText(source_code, location);
    if (!snippet.truncated) return allocator.dupe(u8, snippet.prefix);
    return std.fmt.allocPrint(allocator, "{s}...", .{snippet.prefix});
}

/// A borrowed source prefix and its presentation-only truncation marker.
pub const SingleLineSnippet = struct {
    prefix: []const u8 = "",
    truncated: bool = false,

    pub fn writeTo(self: SingleLineSnippet, writer: anytype) !void {
        try writer.writeAll(self.prefix);
        if (self.truncated) try writer.writeAll("...");
    }
};

/// The returned prefix borrows source_code. No name equality check is performed;
/// ends are clamped and invalid/no-text ranges produce an empty snippet.
pub fn singleLineSnippetFromText(source_code: []const u8, location: SourceLocation) SingleLineSnippet {
    if (!location.hasText() or @as(usize, @intCast(location.start)) >= source_code.len) {
        return .{};
    }
    const start: usize = @intCast(location.start);
    const requested_end = @as(i64, location.end);
    const end: usize = if (requested_end <= start)
        start
    else
        @min(source_code.len, @as(usize, @intCast(requested_end)));
    const cut = source_code[start..end];
    const newline = std.mem.findAny(u8, cut, "\n\r") orelse
        return .{ .prefix = cut };
    return .{ .prefix = cut[0..newline], .truncated = true };
}

test "character stream movement and position translation" {
    var stream = CharStream.initBorrowed("now is the time for testing", "source");
    try std.testing.expectEqual(@as(u8, 'n'), try stream.get(0));
    try std.testing.expectEqual(@as(u8, 'o'), stream.advanceAndGet(1));
    try std.testing.expectEqual(@as(u8, 'n'), try stream.rollback(1));
    try std.testing.expectEqual(@as(u8, 'w'), try stream.setPosition(2));
    try std.testing.expectError(error.PositionOutOfBounds, stream.setPosition(200));

    try std.testing.expectEqual(@as(?i32, 7), translateLineColumnToPositionInText(
        "ABC\nDEF",
        .{ .line = 1, .column = 3 },
    ));
    try std.testing.expectEqual(@as(?i32, null), translateLineColumnToPositionInText(
        "ABC\nDEF",
        .{ .line = 1, .column = 4 },
    ));
}

test "owned character stream releases source and name" {
    var stream = try CharStream.initOwned(
        std.testing.allocator,
        "contract C {}",
        "C.sol",
        false,
    );
    defer stream.deinit();
    try std.testing.expectEqualStrings("contract C {}", stream.source());
    try std.testing.expectEqualStrings("C.sol", stream.name());
}

test "source snippets borrow bytes and retain permissive bounds" {
    var source = "abCDE\r\nrest".*;
    const stream = CharStream.initBorrowed(&source, "source.sol");
    const location: SourceLocation = .{ .start = 2, .end = 100, .source_name = "different.sol" };
    const view = stream.singleLineSnippet(location);
    try std.testing.expectEqual(source[2..].ptr, view.prefix.ptr);
    try std.testing.expectEqualStrings("CDE", view.prefix);
    try std.testing.expect(view.truncated);
    source[2] = 'X';
    var buffer: [16]u8 = undefined;
    var writer = std.Io.Writer.fixed(&buffer);
    try view.writeTo(&writer);
    try std.testing.expectEqualStrings("XDE...", writer.buffered());
    const owned = try singleLineSnippetFromTextAlloc(std.testing.allocator, &source, location);
    defer std.testing.allocator.free(owned);
    try std.testing.expectEqualStrings(writer.buffered(), owned);
    const no_text = stream.singleLineSnippet(.{ .start = 0, .end = 2 });
    try std.testing.expectEqualStrings("", no_text.prefix);
    try std.testing.expect(!no_text.truncated);
    var short = std.Io.Writer.fixed(buffer[0..4]);
    try std.testing.expectError(error.WriteFailed, view.writeTo(&short));
}
