// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned exception payload used while structurally translating the C++
//! exception hierarchy. Ordinary control flow uses the corresponding Zig
//! error values; the payload carries diagnostics across subsystem boundaries.

const std = @import("std");
const SourceLocation = @import("../liblangutil/source_location.zig").SourceLocation;

pub const Kind = enum {
    Exception,
    InvalidAddress,
    BadHexCharacter,
    BadHexCase,
    FileNotFound,
    NotAFile,
    DataTooLong,
    StringTooLong,
    InvalidType,
    CompilerError,
    StackTooDeepError,
    InternalCompilerError,
    FatalError,
    UnimplementedFeatureError,
    InvalidAstError,
};

pub const Failure = error{
    InvalidAddress,
    BadHexCharacter,
    BadHexCase,
    FileNotFound,
    NotAFile,
    DataTooLong,
    StringTooLong,
    InvalidType,
    CompilerError,
    StackTooDeepError,
    InternalCompilerError,
    FatalError,
    UnimplementedFeatureError,
    InvalidAstError,
};

pub const Exception = struct {
    allocator: std.mem.Allocator,
    kind: Kind = .Exception,
    comment_bytes: []u8,
    source_location: SourceLocation = .{},
    file: []u8,
    line: ?u32 = null,

    pub fn init(
        allocator: std.mem.Allocator,
        kind: Kind,
        description: []const u8,
        source_location: SourceLocation,
        file: []const u8,
        line: ?u32,
    ) !Exception {
        const owned_comment = try allocator.dupe(u8, description);
        errdefer allocator.free(owned_comment);
        const owned_file = try allocator.dupe(u8, file);
        return .{
            .allocator = allocator,
            .kind = kind,
            .comment_bytes = owned_comment,
            .source_location = source_location,
            .file = owned_file,
            .line = line,
        };
    }

    pub fn deinit(self: *Exception) void {
        self.allocator.free(self.comment_bytes);
        self.allocator.free(self.file);
        self.* = undefined;
    }

    pub fn what(self: *const Exception) []const u8 {
        return if (self.comment_bytes.len != 0) self.comment_bytes else @tagName(self.kind);
    }

    pub fn comment(self: *const Exception) ?[]const u8 {
        return if (self.comment_bytes.len == 0) null else self.comment_bytes;
    }

    pub fn lineInfoAlloc(self: *const Exception, allocator: std.mem.Allocator) ![]u8 {
        if (self.line) |line| return std.fmt.allocPrint(allocator, "{s}:{d}", .{ self.file, line });
        return std.fmt.allocPrint(allocator, "{s}:", .{self.file});
    }
};

test "exception payload owns comment and source metadata" {
    var exception = try Exception.init(
        std.testing.allocator,
        .InvalidAddress,
        "bad address",
        .{ .start = 1, .end = 2, .source_name = "a.sol" },
        "file.cpp",
        9,
    );
    defer exception.deinit();
    try std.testing.expectEqualStrings("bad address", exception.what());
    const line = try exception.lineInfoAlloc(std.testing.allocator);
    defer std.testing.allocator.free(line);
    try std.testing.expectEqualStrings("file.cpp:9", line);
}
