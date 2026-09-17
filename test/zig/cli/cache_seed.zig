// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Seeds the isolated user-cache maintenance smoke test without requiring a
//! persistent-safe compiler identity from the actual compiler input contents.

const std = @import("std");
const solidity = @import("solidity");
const authentication_key = [_]u8{0x5a} ** 32;

pub fn main(init: std.process.Init) !void {
    const arguments = try init.minimal.args.toSlice(init.arena.allocator());
    if (arguments.len < 2) return error.InvalidArguments;
    if (std.mem.eql(u8, arguments[1], "configure")) {
        if (arguments.len != 2) return error.InvalidArguments;
        return writeTrustedConfiguration(init);
    }
    if (!std.mem.eql(u8, arguments[1], "seed") or arguments.len != 3)
        return error.InvalidArguments;
    const cache_home = init.environ_map.get("XDG_CACHE_HOME") orelse
        return error.CacheLocationUnavailable;
    if (!std.Io.Dir.path.isAbsolute(cache_home))
        return error.CacheLocationUnavailable;
    const project_root = try std.Io.Dir.cwd().realPathFileAlloc(
        init.io,
        arguments[2],
        init.gpa,
    );
    defer init.gpa.free(project_root);
    var digest: [std.crypto.hash.sha2.Sha256.digest_length]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(project_root, &digest, .{});
    const digest_hex = std.fmt.bytesToHex(digest, .lower);
    const database_path = try std.Io.Dir.path.join(
        init.gpa,
        &.{ cache_home, "oksolc", "projects-v2", &digest_hex, "artifacts.sqlite" },
    );
    defer init.gpa.free(database_path);
    if (std.Io.Dir.path.dirname(database_path)) |directory|
        try std.Io.Dir.cwd().createDirPath(init.io, directory);

    var store = try solidity.incremental.SqliteStore.initWithOptions(
        init.gpa,
        init.io,
        database_path,
        authentication_key,
        .{ .limits = .unlimited },
    );
    defer store.deinit();

    var builder = solidity.incremental.PhaseKeyBuilder.init(
        .exact_response,
        solidity.incremental.CompilerFingerprint.init("cli-cache-smoke"),
    );
    builder.addInputBytes("seed");
    try store.put(
        .{ .kind = .exact_response, .key = builder.finish() },
        "seed",
        &.{},
    );
}

fn writeTrustedConfiguration(init: std.process.Init) !void {
    const config_home = init.environ_map.get("XDG_CONFIG_HOME") orelse
        return error.ConfigLocationUnavailable;
    if (!std.Io.Dir.path.isAbsolute(config_home))
        return error.ConfigLocationUnavailable;
    const directory_path = try std.Io.Dir.path.join(
        init.gpa,
        &.{ config_home, "oksolc" },
    );
    defer init.gpa.free(directory_path);
    try std.Io.Dir.cwd().createDirPath(init.io, directory_path);
    const config_path = try std.Io.Dir.path.join(
        init.gpa,
        &.{ directory_path, "config.toml" },
    );
    defer init.gpa.free(config_path);
    try std.Io.Dir.cwd().writeFile(init.io, .{
        .sub_path = config_path,
        .data = "# Trusted external configuration for cache smoke tests.\n" ++
            "cache = true\n" ++
            "parallel = false\n",
    });
}
