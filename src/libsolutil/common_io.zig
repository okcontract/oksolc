// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Capability-oriented translation of `CommonIO.cpp`.
//!
//! Unlike the C++ entry points, whole-input operations take an explicit size
//! limit and filesystem operations take both an I/O backend and directory
//! capability.  Returned byte slices are owned by the caller.

const std = @import("std");
const builtin = @import("builtin");

pub const ReadFileError = std.Io.Dir.StatFileError ||
    std.Io.Dir.ReadFileAllocError ||
    error{NotAFile};

pub fn formatBytesAlloc(
    allocator: std.mem.Allocator,
    bytes: []const u8,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.append(allocator, '[');
    for (bytes, 0..) |byte, index| {
        if (index != 0) try output.append(allocator, ',');
        const formatted = try std.fmt.allocPrint(allocator, "{x}", .{byte});
        defer allocator.free(formatted);
        try output.appendSlice(allocator, formatted);
    }
    try output.append(allocator, ']');
    return output.toOwnedSlice(allocator);
}

/// Reads a regular file relative to `root`, following symlinks as upstream
/// does.  Directories and other non-regular filesystem nodes are rejected
/// before opening them for content reads.
pub fn readFileAsStringAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    root: std.Io.Dir,
    path: []const u8,
    max_bytes: usize,
) ReadFileError![]u8 {
    const stat = try root.statFile(io, path, .{ .follow_symlinks = true });
    if (stat.kind != .file) return error.NotAFile;
    return root.readFileAlloc(io, path, allocator, .limited(max_bytes)) catch |err| switch (err) {
        // Preserve the C++ NotAFile distinction if the node changes between
        // the stat and open operations.
        error.IsDir => error.NotAFile,
        else => |other| other,
    };
}

/// Reads a stream through EOF, bounded by `max_bytes`.
pub fn readUntilEndAlloc(
    allocator: std.mem.Allocator,
    reader: *std.Io.Reader,
    max_bytes: usize,
) std.Io.Reader.LimitedAllocError![]u8 {
    return reader.allocRemaining(allocator, .limited(max_bytes));
}

/// Tries to read exactly `length` bytes and returns any shorter prefix read at
/// EOF.  This matches `std::istream::read` plus `gcount()` in the C++ source.
pub fn readBytesAlloc(
    allocator: std.mem.Allocator,
    reader: *std.Io.Reader,
    length: usize,
) (std.mem.Allocator.Error || std.Io.Reader.ShortError)![]u8 {
    var output = try allocator.alloc(u8, length);
    errdefer allocator.free(output);
    const actual_length = try reader.readSliceShort(output);
    if (actual_length == output.len) return output;
    output = try allocator.realloc(output, actual_length);
    return output;
}

pub const StandardInputError = std.Io.File.Reader.Error ||
    std.posix.TermiosGetError ||
    std.posix.TermiosSetError;

/// Reads one byte from stdin without waiting for an end-of-line on POSIX
/// terminals. Non-terminal streams remain readable and platforms without the
/// POSIX terminal interface use the ordinary one-byte input path.
pub fn readStandardInputChar(io: std.Io) StandardInputError!?u8 {
    const supports_termios = switch (builtin.os.tag) {
        .linux,
        .driverkit,
        .ios,
        .maccatalyst,
        .macos,
        .tvos,
        .visionos,
        .watchos,
        .freebsd,
        .netbsd,
        .openbsd,
        .dragonfly,
        .haiku,
        .illumos,
        => true,
        else => false,
    };
    if (comptime supports_termios) {
        const original = std.posix.tcgetattr(std.posix.STDIN_FILENO) catch |err| switch (err) {
            // Redirected stdin is not a terminal and needs no mode change.
            error.NotATerminal => return readInputByte(io),
            else => |other| return other,
        };
        var unbuffered = original;
        unbuffered.lflag.ICANON = false;
        unbuffered.lflag.ECHO = false;
        unbuffered.cc[@intFromEnum(std.posix.V.MIN)] = 1;
        unbuffered.cc[@intFromEnum(std.posix.V.TIME)] = 0;
        try std.posix.tcsetattr(std.posix.STDIN_FILENO, .NOW, unbuffered);
        const read_result = readInputByte(io);
        const restore_result = std.posix.tcsetattr(std.posix.STDIN_FILENO, .DRAIN, original);
        const byte = try read_result;
        try restore_result;
        return byte;
    }
    return readInputByte(io);
}

fn readInputByte(io: std.Io) std.Io.File.Reader.Error!?u8 {
    var file_reader = std.Io.File.stdin().reader(io, &.{});
    var byte: [1]u8 = undefined;
    const count = file_reader.interface.readSliceShort(&byte) catch
        return file_reader.err.?;
    return if (count == 0) null else byte[0];
}

/// Allocating equivalent of the upstream stream-based `toString` helper.
pub fn toStringAlloc(allocator: std.mem.Allocator, value: anytype) std.mem.Allocator.Error![]u8 {
    return std.fmt.allocPrint(allocator, "{any}", .{value});
}

/// Resolves only paths whose first component is `.` or `..`, relative to the
/// directory containing `reference`.  Other paths are returned unchanged,
/// matching the intentionally unusual upstream contract.
pub fn absolutePathAlloc(
    allocator: std.mem.Allocator,
    path: []const u8,
    reference: []const u8,
) std.mem.Allocator.Error![]u8 {
    var components = std.Io.Dir.path.componentIterator(path);
    const first = components.next() orelse return allocator.dupe(u8, path);
    if (!std.mem.eql(u8, first.name, ".") and !std.mem.eql(u8, first.name, ".."))
        return allocator.dupe(u8, path);

    const base = std.Io.Dir.path.dirname(reference) orelse
        if (std.Io.Dir.path.isAbsolute(reference)) reference else "";
    const resolved = try std.Io.Dir.path.resolve(allocator, &.{ base, path });
    if (builtin.os.tag != .windows) return resolved;
    defer allocator.free(resolved);
    return sanitizePathAlloc(allocator, resolved);
}

/// Converts native path separators to the generic `/` spelling used by the
/// C++ `boost::filesystem::path::generic_string()` result.
pub fn sanitizePathAlloc(
    allocator: std.mem.Allocator,
    path: []const u8,
) std.mem.Allocator.Error![]u8 {
    const result = try allocator.dupe(u8, path);
    if (builtin.os.tag == .windows) std.mem.replaceScalar(u8, result, '\\', '/');
    return result;
}

test "bounded stream helpers preserve bytes and partial reads" {
    var reader: std.Io.Reader = .fixed("ABC\r\ndef");
    const first = try readBytesAlloc(std.testing.allocator, &reader, 4);
    defer std.testing.allocator.free(first);
    try std.testing.expectEqualStrings("ABC\r", first);

    const rest = try readUntilEndAlloc(std.testing.allocator, &reader, 16);
    defer std.testing.allocator.free(rest);
    try std.testing.expectEqualStrings("\ndef", rest);

    const empty = try readBytesAlloc(std.testing.allocator, &reader, 20);
    defer std.testing.allocator.free(empty);
    try std.testing.expectEqual(@as(usize, 0), empty.len);
}

test "whole-input limits are enforced" {
    var reader: std.Io.Reader = .fixed("abcd");
    try std.testing.expectError(
        error.StreamTooLong,
        readUntilEndAlloc(std.testing.allocator, &reader, 3),
    );
}

test "file reads reject directories and preserve content" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    try tmp.dir.writeFile(std.testing.io, .{
        .sub_path = "test.txt",
        .data = "ABC\ndef\n",
    });

    const content = try readFileAsStringAlloc(
        std.testing.allocator,
        std.testing.io,
        tmp.dir,
        "test.txt",
        1024,
    );
    defer std.testing.allocator.free(content);
    try std.testing.expectEqualStrings("ABC\ndef\n", content);
    try std.testing.expectError(
        error.NotAFile,
        readFileAsStringAlloc(
            std.testing.allocator,
            std.testing.io,
            tmp.dir,
            ".",
            1024,
        ),
    );
}

test "absolutePath resolves only explicit dot-relative paths" {
    const allocator = std.testing.allocator;
    const unchanged = try absolutePathAlloc(allocator, "contracts/A.sol", "/src/Main.sol");
    defer allocator.free(unchanged);
    try std.testing.expectEqualStrings("contracts/A.sol", unchanged);

    const child = try absolutePathAlloc(allocator, "./A.sol", "/src/nested/Main.sol");
    defer allocator.free(child);
    try std.testing.expectEqualStrings("/src/nested/A.sol", child);

    const parent = try absolutePathAlloc(allocator, "../A.sol", "/src/nested/Main.sol");
    defer allocator.free(parent);
    try std.testing.expectEqualStrings("/src/A.sol", parent);
}

test "toString owns its result" {
    const result = try toStringAlloc(std.testing.allocator, @as(u32, 42));
    defer std.testing.allocator.free(result);
    try std.testing.expectEqualStrings("42", result);

    const bytes = try formatBytesAlloc(std.testing.allocator, &.{ 0, 10, 255 });
    defer std.testing.allocator.free(bytes);
    try std.testing.expectEqualStrings("[0,a,ff]", bytes);
}
