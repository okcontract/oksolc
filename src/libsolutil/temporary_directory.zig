// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit temporary-directory owners translated from
//! `TemporaryDirectory.cpp`.

const std = @import("std");

pub const TemporaryDirectory = struct {
    const Self = @This();

    pub const InitError = std.mem.Allocator.Error ||
        std.Io.Dir.CreateDirError ||
        std.Io.Dir.OpenError ||
        std.Io.Dir.CreateDirPathError ||
        error{ InvalidPrefix, InvalidSubdirectory };

    allocator: std.mem.Allocator,
    io: std.Io,
    parent: std.Io.Dir,
    relative_name: []u8,
    display_path: []u8,
    active: bool = true,

    /// Creates a unique child of the passed directory capability. `parent`
    /// remains borrowed. `parent_display_path` is used only for diagnostics and
    /// for the `path()` compatibility accessor.
    pub fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        parent: std.Io.Dir,
        parent_display_path: []const u8,
        prefix: []const u8,
        subdirectories: []const []const u8,
    ) InitError!Self {
        try validatePrefix(prefix);
        for (subdirectories) |subdirectory| try validateSubdirectory(subdirectory);

        var entropy: [8]u8 = undefined;
        std.Io.random(io, &entropy);
        const hex = std.fmt.bytesToHex(entropy, .lower);
        const relative_name = try std.fmt.allocPrint(
            allocator,
            "{s}-{s}-{s}-{s}-{s}",
            .{ prefix, hex[0..4], hex[4..8], hex[8..12], hex[12..16] },
        );
        errdefer allocator.free(relative_name);

        const display_path = try std.Io.Dir.path.join(
            allocator,
            &.{ parent_display_path, relative_name },
        );
        errdefer allocator.free(display_path);

        try parent.createDir(io, relative_name, .default_dir);
        errdefer parent.deleteTree(io, relative_name) catch |err| {
            std.log.err("failed to remove temporary directory '{s}': {s}", .{
                display_path,
                @errorName(err),
            });
        };

        if (subdirectories.len != 0) {
            const child = try parent.openDir(io, relative_name, .{});
            defer child.close(io);
            for (subdirectories) |subdirectory|
                try child.createDirPath(io, subdirectory);
        }

        return .{
            .allocator = allocator,
            .io = io,
            .parent = parent,
            .relative_name = relative_name,
            .display_path = display_path,
        };
    }

    pub fn path(self: *const Self) []const u8 {
        return self.display_path;
    }

    pub fn relativePath(self: *const Self) []const u8 {
        return self.relative_name;
    }

    /// Fallible cleanup for callers that need to observe deletion failures.
    pub fn cleanup(self: *Self) std.Io.Dir.DeleteTreeError!void {
        if (!self.active) return;
        try self.parent.deleteTree(self.io, self.relative_name);
        self.active = false;
    }

    pub fn deinit(self: *Self) void {
        if (self.active) self.cleanup() catch |err| {
            std.log.err("failed to remove temporary directory '{s}': {s}", .{
                self.display_path,
                @errorName(err),
            });
        };
        self.allocator.free(self.display_path);
        self.allocator.free(self.relative_name);
        self.* = undefined;
    }

    fn validatePrefix(prefix: []const u8) error{InvalidPrefix}!void {
        if (prefix.len == 0 or
            !std.mem.eql(u8, std.Io.Dir.path.basename(prefix), prefix) or
            !std.mem.eql(u8, std.Io.Dir.path.stem(prefix), prefix) or
            std.mem.eql(u8, prefix, ".") or
            std.mem.eql(u8, prefix, ".."))
            return error.InvalidPrefix;
    }

    fn validateSubdirectory(subdirectory: []const u8) error{InvalidSubdirectory}!void {
        if (subdirectory.len == 0 or std.Io.Dir.path.isAbsolute(subdirectory))
            return error.InvalidSubdirectory;
        var components = std.Io.Dir.path.componentIterator(subdirectory);
        while (components.next()) |component| {
            if (std.mem.eql(u8, component.name, ".."))
                return error.InvalidSubdirectory;
        }
    }
};

pub const TemporaryWorkingDirectory = struct {
    const Self = @This();

    allocator: std.mem.Allocator,
    io: std.Io,
    original_path: [:0]u8,
    active: bool = true,

    pub fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        new_directory: []const u8,
    ) !Self {
        const original_path = try std.process.currentPathAlloc(io, allocator);
        errdefer allocator.free(original_path);
        try std.process.setCurrentPath(io, new_directory);
        return .{
            .allocator = allocator,
            .io = io,
            .original_path = original_path,
        };
    }

    pub fn originalWorkingDirectory(self: *const Self) []const u8 {
        return self.original_path;
    }

    pub fn restore(self: *Self) !void {
        if (!self.active) return;
        try std.process.setCurrentPath(self.io, self.original_path);
        self.active = false;
    }

    pub fn deinit(self: *Self) void {
        if (self.active) self.restore() catch |err| {
            std.log.err("failed to restore working directory '{s}': {s}", .{
                self.original_path,
                @errorName(err),
            });
        };
        self.allocator.free(self.original_path);
        self.* = undefined;
    }
};

test "temporary directory owns a unique tree and removes it" {
    var root = std.testing.tmpDir(.{});
    defer root.cleanup();

    const subdirectories = [_][]const u8{ "a", "a/b/c", "x.y/z" };
    var temporary = try TemporaryDirectory.init(
        std.testing.allocator,
        std.testing.io,
        root.dir,
        "test-root",
        "temporary-directory-test",
        &subdirectories,
    );
    defer temporary.deinit();

    try std.testing.expect(std.mem.startsWith(
        u8,
        temporary.relativePath(),
        "temporary-directory-test-",
    ));
    try std.testing.expectEqual(.directory, (try root.dir.statFile(
        std.testing.io,
        temporary.relativePath(),
        .{},
    )).kind);

    const child = try root.dir.openDir(std.testing.io, temporary.relativePath(), .{});
    defer child.close(std.testing.io);
    try std.testing.expectEqual(.directory, (try child.statFile(
        std.testing.io,
        "a/b/c",
        .{},
    )).kind);
    try child.writeFile(std.testing.io, .{
        .sub_path = "owned.txt",
        .data = "delete me",
    });

    const relative_name = try std.testing.allocator.dupe(u8, temporary.relativePath());
    defer std.testing.allocator.free(relative_name);
    try temporary.cleanup();
    try std.testing.expectError(
        error.FileNotFound,
        root.dir.statFile(std.testing.io, relative_name, .{}),
    );
}

test "temporary directory rejects traversal" {
    var root = std.testing.tmpDir(.{});
    defer root.cleanup();
    const escaping = [_][]const u8{"../outside"};
    try std.testing.expectError(
        error.InvalidSubdirectory,
        TemporaryDirectory.init(
            std.testing.allocator,
            std.testing.io,
            root.dir,
            "test-root",
            "safe",
            &escaping,
        ),
    );
    try std.testing.expectError(
        error.InvalidPrefix,
        TemporaryDirectory.init(
            std.testing.allocator,
            std.testing.io,
            root.dir,
            "test-root",
            "../unsafe",
            &.{},
        ),
    );
}
