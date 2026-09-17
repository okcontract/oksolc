// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");

/// Both tools consume one immutable copy. A source edit cannot land between
/// checking TypeScript and bundling JavaScript from that checked source.
pub fn build(b: *std.Build, cli: *std.Build.Module) void {
    const tsc = b.option([]const u8, "tsc", "System TypeScript 7 compiler") orelse "tsc";
    const bun = b.option([]const u8, "bun", "System Bun bundler") orelse "bun";
    const typescript_version = std.mem.trim(u8, @embedFile("../src/cli/browser/typescript-version"), "\r\n");
    const bun_version = std.mem.trim(u8, @embedFile("../src/cli/browser/bun-version"), "\r\n");
    const check_tsc = b.addSystemCommand(&.{ tsc, "--version" });
    check_tsc.expectStdOutEqual(b.fmt("Version {s}\n", .{typescript_version}));
    check_tsc.has_side_effects = true;
    const check_bun = b.addSystemCommand(&.{ bun, "--version" });
    check_bun.expectStdOutEqual(b.fmt("{s}\n", .{bun_version}));
    check_bun.has_side_effects = true;

    const inputs = b.addWriteFiles();
    const source = inputs.addCopyDirectory(b.path("src/cli/browser"), "browser", .{
        .include_extensions = &.{ ".ts", ".json" },
    });
    const typecheck = b.addSystemCommand(&.{ tsc, "--pretty", "false", "--project" });
    typecheck.addDirectoryArg(source);
    // TS diagnostics are written to stdout. Inherit it so failures are visible,
    // and run the inexpensive check even when Bun's bundle is already cached.
    typecheck.stdio = .inherit;
    typecheck.step.dependOn(&check_tsc.step);
    b.step("typecheck-browser", "Check all browser TypeScript with strict TS7").dependOn(&typecheck.step);

    const bundle = b.addSystemCommand(&.{ bun, "build" });
    bundle.addFileArg(source.path(b, "app.ts"));
    bundle.addArgs(&.{ "--target=browser", "--format=esm", "--env=disable", "--outdir" });
    const output = bundle.addOutputDirectoryArg("browser");
    bundle.setCwd(source);
    bundle.step.dependOn(&typecheck.step);
    bundle.step.dependOn(&check_bun.step);
    cli.addAnonymousImport("browser_app", .{ .root_source_file = output.path(b, "app.js") });

    const install = b.addInstallDirectory(.{
        .source_dir = output,
        .install_dir = .prefix,
        .install_subdir = "browser",
    });
    b.step("build-browser", "Check and bundle browser assets into zig-out/browser").dependOn(&install.step);

    const tests = b.addSystemCommand(&.{ bun, "test" });
    tests.addFileArg(b.path("test/zig/cli/browser_types.test.js"));
    tests.step.dependOn(&typecheck.step);
    tests.step.dependOn(&check_bun.step);
    b.step("test-browser-types", "Test browser API validation and artifact preservation").dependOn(&tests.step);
}
