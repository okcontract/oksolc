// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Deterministic, bounded enumeration of compilation entry points. Imported
//! dependencies are discovered by the compiler's source callback instead.
const std = @import("std");

pub fn pathContainedBy(parent: []const u8, child: []const u8) bool {
    if (!std.mem.startsWith(u8, child, parent)) return false;
    if (child.len == parent.len) return true;
    if (parent.len == 0 or std.Io.Dir.path.isSep(parent[parent.len - 1])) return true;
    return std.Io.Dir.path.isSep(child[parent.len]);
}

pub fn validatePath(path: []const u8) !void {
    if (path.len == 0 or path.len > 16 * 1024 or std.Io.Dir.path.isAbsolute(path) or
        std.mem.findScalar(u8, path, 0) != null) return error.InvalidSourcePath;
    var parts = std.mem.tokenizeAny(u8, path, "/\\");
    while (parts.next()) |part| if (std.mem.eql(u8, part, "..")) return error.InvalidSourcePath;
}

pub const Names = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayList([]const u8) = .empty,

    pub fn deinit(self: *Names) void {
        for (self.items.items) |name| self.allocator.free(name);
        self.items.deinit(self.allocator);
    }

    pub fn eql(self: Names, other: Names) bool {
        if (self.items.items.len != other.items.items.len) return false;
        for (self.items.items, other.items.items) |a, b| if (!std.mem.eql(u8, a, b)) return false;
        return true;
    }
};

pub fn collectAlloc(allocator: std.mem.Allocator, io: std.Io, directory: std.Io.Dir, prefix: []const u8) !Names {
    return collectRootsAlloc(allocator, io, &.{.{ .directory = directory, .prefix = prefix }});
}

pub const Root = struct {
    /// Borrowed directory and normalized project-relative namespace prefix.
    directory: std.Io.Dir,
    prefix: []const u8,
};

/// Enumerate the union of the fixed source/test roots with one global budget.
/// An ancestor already covers a nested root; equal roots are walked once.
pub fn collectRootsAlloc(allocator: std.mem.Allocator, io: std.Io, roots: []const Root) !Names {
    var names: Names = .{ .allocator = allocator };
    errdefer names.deinit();
    var entries: usize = 0;
    next_root: for (roots, 0..) |root, index| {
        for (roots, 0..) |other, other_index| {
            if (index == other_index) continue;
            if (pathContainedBy(other.prefix, root.prefix) and
                (other.prefix.len < root.prefix.len or other_index < index)) continue :next_root;
        }
        try collect(&names, io, root.directory, root.prefix, 0, &entries);
    }
    std.mem.sort([]const u8, names.items.items, {}, struct {
        fn lessThan(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.lessThan(u8, a, b);
        }
    }.lessThan);
    return names;
}

fn collect(names: *Names, io: std.Io, directory: std.Io.Dir, prefix: []const u8, depth: usize, entries: *usize) anyerror!void {
    if (depth >= 128) return error.SourceTreeTooDeep;
    var iterator = directory.iterate();
    while (try iterator.next(io)) |entry| {
        entries.* += 1;
        if (entries.* > 100_000) return error.SourceTreeTooLarge;
        // Never silently omit a subtree whose contents cannot be inspected.
        if (entry.kind == .sym_link) return error.SourceTreeSymlink;
        if (entry.kind != .directory and !std.mem.endsWith(u8, entry.name, ".sol")) continue;
        const path = try std.Io.Dir.path.join(names.allocator, &.{ prefix, entry.name });
        defer names.allocator.free(path);
        if (path.len > 16 * 1024) return error.SourcePathTooLong;
        if (entry.kind == .directory) {
            var child = try directory.openDir(io, entry.name, .{ .iterate = true, .follow_symlinks = false });
            defer child.close(io);
            try collect(names, io, child, path, depth + 1, entries);
        } else {
            if (entry.kind != .file) return error.SourceNotRegularFile;
            if (names.items.items.len >= 4096) return error.TooManySources;
            const owned = try names.allocator.dupe(u8, path);
            errdefer names.allocator.free(owned);
            try names.items.append(names.allocator, owned);
        }
    }
}

test "source path stays relative to its project" {
    for ([_][]const u8{ "", "/src", "../src", "src/../lib", "src\x00" }) |path|
        try std.testing.expectError(error.InvalidSourcePath, validatePath(path));
    for ([_][]const u8{ "src", "contracts/nested", ".", "./src" }) |path| try validatePath(path);
}

test "source enumeration sorts roots and owns paths across allocation failure" {
    var temporary = std.testing.tmpDir(.{ .iterate = true });
    defer temporary.cleanup();
    try temporary.dir.createDir(std.testing.io, "nested", .default_dir);
    try temporary.dir.writeFile(std.testing.io, .{ .sub_path = "Z.sol", .data = "" });
    try temporary.dir.writeFile(std.testing.io, .{ .sub_path = "nested/A.sol", .data = "" });
    try temporary.dir.writeFile(std.testing.io, .{ .sub_path = "ignored.txt", .data = "" });
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn run(allocator: std.mem.Allocator, directory: std.Io.Dir) !void {
            // Each walk gets an independent directory cursor.
            var root = try directory.openDir(std.testing.io, ".", .{ .iterate = true });
            defer root.close(std.testing.io);
            var names = try collectAlloc(allocator, std.testing.io, root, "src");
            defer names.deinit();
            try std.testing.expectEqual(@as(usize, 2), names.items.items.len);
            try std.testing.expectEqualStrings("src/Z.sol", names.items.items[0]);
            try std.testing.expectEqualStrings("src/nested/A.sol", names.items.items[1]);
        }
    }.run, .{temporary.dir});
}

test "source and test root union owns sorted names and avoids overlapping walks" {
    var temporary = std.testing.tmpDir(.{ .iterate = true });
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "src/test");
    try temporary.dir.createDirPath(std.testing.io, "test");
    try temporary.dir.writeFile(std.testing.io, .{ .sub_path = "src/C.sol", .data = "" });
    try temporary.dir.writeFile(std.testing.io, .{ .sub_path = "src/test/Nested.sol", .data = "" });
    try temporary.dir.writeFile(std.testing.io, .{ .sub_path = "test/T.sol", .data = "" });
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn run(allocator: std.mem.Allocator, directory: std.Io.Dir) !void {
            var source = try directory.openDir(std.testing.io, "src", .{ .iterate = true });
            defer source.close(std.testing.io);
            var nested = try directory.openDir(std.testing.io, "src/test", .{ .iterate = true });
            defer nested.close(std.testing.io);
            var tests = try directory.openDir(std.testing.io, "test", .{ .iterate = true });
            defer tests.close(std.testing.io);
            var names = try collectRootsAlloc(allocator, std.testing.io, &.{
                .{ .directory = nested, .prefix = "src/test" },
                .{ .directory = tests, .prefix = "test" },
                .{ .directory = source, .prefix = "src" },
                .{ .directory = source, .prefix = "src" },
            });
            defer names.deinit();
            try std.testing.expectEqual(@as(usize, 3), names.items.items.len);
            try std.testing.expectEqualStrings("src/C.sol", names.items.items[0]);
            try std.testing.expectEqualStrings("src/test/Nested.sol", names.items.items[1]);
            try std.testing.expectEqualStrings("test/T.sol", names.items.items[2]);
        }
    }.run, .{temporary.dir});
}

test "source count budget is shared across disjoint roots" {
    var temporary = std.testing.tmpDir(.{ .iterate = true });
    defer temporary.cleanup();
    try temporary.dir.createDir(std.testing.io, "src", .default_dir);
    try temporary.dir.createDir(std.testing.io, "test", .default_dir);
    var source = try temporary.dir.openDir(std.testing.io, "src", .{ .iterate = true });
    defer source.close(std.testing.io);
    var tests = try temporary.dir.openDir(std.testing.io, "test", .{ .iterate = true });
    defer tests.close(std.testing.io);
    for (0..2049) |index| {
        var buffer: [32]u8 = undefined;
        const name = try std.fmt.bufPrint(&buffer, "{d}.sol", .{index});
        try source.writeFile(std.testing.io, .{ .sub_path = name, .data = "" });
        try tests.writeFile(std.testing.io, .{ .sub_path = name, .data = "" });
    }
    try std.testing.expectError(error.TooManySources, collectRootsAlloc(std.testing.allocator, std.testing.io, &.{
        .{ .directory = source, .prefix = "src" },
        .{ .directory = tests, .prefix = "test" },
    }));
}
