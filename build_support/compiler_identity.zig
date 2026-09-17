// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Content identity for compiler inputs, independent of Git state and UI assets.
//! Build rules and dependency pins are included conservatively. The CLI supplies
//! its exact request and loader context separately when authenticating receipts.
const std = @import("std");

const directories = [_][]const u8{ "src", "include", "vendor/sqlite", "build_support" };
const files = [_][]const u8{ "build.zig", "build.zig.zon" };

pub fn digest(allocator: std.mem.Allocator, io: std.Io, root: std.Io.Dir) ![64]u8 {
    var paths: std.ArrayList([]const u8) = .empty;
    defer {
        for (paths.items) |path| allocator.free(path);
        paths.deinit(allocator);
    }
    for (files) |path| {
        const owned = try allocator.dupe(u8, path);
        errdefer allocator.free(owned);
        try paths.append(allocator, owned);
    }
    for (directories) |path| {
        var directory = try root.openDir(io, path, .{ .iterate = true });
        defer directory.close(io);
        var walker = try directory.walk(allocator);
        defer {
            while (walker.inner.stack.items.len != 0) walker.leave(io);
            walker.deinit();
        }
        while (try walker.next(io)) |entry| {
            if (std.mem.eql(u8, path, "src") and std.mem.eql(u8, entry.path, "cli") and entry.kind == .directory) {
                walker.leave(io);
                continue;
            }
            switch (entry.kind) {
                .directory => {},
                .file => {
                    const full = try std.fs.path.join(allocator, &.{ path, entry.path });
                    errdefer allocator.free(full);
                    try paths.append(allocator, full);
                },
                else => return error.UnsupportedCompilerInput,
            }
        }
    }
    std.mem.sort([]const u8, paths.items, {}, struct {
        fn less(_: void, left: []const u8, right: []const u8) bool {
            return std.mem.lessThan(u8, left, right);
        }
    }.less);
    var hash = std.crypto.hash.sha2.Sha256.init(.{});
    hash.update("oksolc.compiler-content.v1\x00");
    for (paths.items) |path| {
        const content = try root.readFileAlloc(io, path, allocator, .limited(64 * 1024 * 1024));
        defer allocator.free(content);
        var file_hash: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(content, &file_hash, .{});
        // NUL is forbidden in filesystem names; fixed-size digests frame bytes.
        hash.update(path);
        hash.update("\x00");
        hash.update(&file_hash);
    }
    return std.fmt.bytesToHex(hash.finalResult(), .lower);
}

/// Recheck after compilation: never publish an artifact with an identity read
/// before a concurrent source edit. The same implementation owns both checks.
pub fn main(init: std.process.Init) !void {
    var args = try std.process.Args.Iterator.initAllocator(init.minimal.args, init.gpa);
    defer args.deinit();
    _ = args.next();
    const path = args.next() orelse return error.MissingRoot;
    const expected = args.next() orelse return error.MissingIdentity;
    var root = try std.Io.Dir.cwd().openDir(init.io, path, .{});
    defer root.close(init.io);
    const actual = try digest(init.gpa, init.io, root);
    if (!std.mem.eql(u8, &actual, expected)) return error.CompilerInputsChangedDuringBuild;
}

test "compiler identity follows input bytes without Git and ignores UI and documentation" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const io = std.testing.io;
    for (directories) |path| try temporary.dir.createDirPath(io, path);
    for (files) |path| try temporary.dir.writeFile(io, .{ .sub_path = path, .data = "build inputs" });
    try temporary.dir.writeFile(io, .{ .sub_path = "src/compiler.zig", .data = "first" });
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn run(allocator: std.mem.Allocator, root: std.Io.Dir) !void {
            _ = try digest(allocator, std.testing.io, root);
        }
    }.run, .{temporary.dir});
    const before = try digest(std.testing.allocator, io, temporary.dir);
    try temporary.dir.createDirPath(io, "src/cli/browser");
    try temporary.dir.writeFile(io, .{ .sub_path = "src/cli/browser/app.js", .data = "changed UI" });
    try temporary.dir.writeFile(io, .{ .sub_path = "README.md", .data = "changed docs" });
    try std.testing.expectEqual(before, try digest(std.testing.allocator, io, temporary.dir));
    try temporary.dir.writeFile(io, .{ .sub_path = "src/compiler.zig", .data = "other" });
    try std.testing.expect(!std.mem.eql(u8, &before, &try digest(std.testing.allocator, io, temporary.dir)));
    try temporary.dir.writeFile(io, .{ .sub_path = "src/compiler.zig", .data = "first" });
    try std.testing.expectEqual(before, try digest(std.testing.allocator, io, temporary.dir));
    try temporary.dir.writeFile(io, .{ .sub_path = "src/new.zig", .data = "new input" });
    try std.testing.expect(!std.mem.eql(u8, &before, &try digest(std.testing.allocator, io, temporary.dir)));
    try temporary.dir.deleteFile(io, "src/new.zig");
    try temporary.dir.writeFile(io, .{ .sub_path = "build.zig.zon", .data = "new dependency pin" });
    try std.testing.expect(!std.mem.eql(u8, &before, &try digest(std.testing.allocator, io, temporary.dir)));
}
