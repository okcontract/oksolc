// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Git owns repository configuration, fetching and pinned recursive checkouts.
//! This module only selects declared submodules from Solidity remapping targets.
const std = @import("std");
const Input = @import("input.zig");
const ImportRemapper = @import("solidity").libsolidity.@"interface/import_remapper";
const ProjectSources = @import("project_sources.zig");

const Module = struct {
    path: []const u8,
    absolute: []const u8,
    selected: bool = false,
};

pub fn run(allocator: std.mem.Allocator, io: std.Io, project_root: []const u8, jobs: u16) !void {
    // All metadata and argument slices share this invocation's lifetime.
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const scratch = arena.allocator();
    const root_output = try gitOutputAlloc(scratch, io, &.{ "git", "-C", project_root, "rev-parse", "--show-toplevel" }, false);
    if (!std.mem.endsWith(u8, root_output, "\n")) return error.InvalidGitOutput;
    const repository = root_output[0 .. root_output.len - 1];
    if (!std.Io.Dir.path.isAbsolute(repository)) return error.InvalidGitOutput;
    const manifest_path = try std.Io.Dir.path.join(scratch, &.{ repository, ".gitmodules" });
    const manifest_exists = exists: {
        _ = std.Io.Dir.cwd().statFile(io, manifest_path, .{}) catch |err| switch (err) {
            error.FileNotFound => break :exists false,
            else => return err,
        };
        break :exists true;
    };
    // Git parses its own config syntax, including quoted names and paths.
    const config = if (manifest_exists)
        try gitOutputAlloc(scratch, io, &.{ "git", "-C", repository, "config", "--null", "--no-includes", "--file", ".gitmodules", "--get-regexp", "^submodule\\..*\\.path$" }, true)
    else
        "";
    const modules = try modulesAlloc(scratch, repository, config);
    const remappings = try Input.readRemappingsAlloc(scratch, io, project_root);
    if (remappings) |contents| {
        var lines = Input.RemappingLines.init(contents);
        var count: usize = 0;
        while (lines.next()) |line| {
            count += 1;
            if (count > 4096) return error.TooManyRemappings;
            const remapping = ImportRemapper.parseRemapping(line) orelse {
                try report(io, "Invalid Solidity remapping: {s}\n", .{line});
                return error.InvalidRemapping;
            };
            if (std.mem.findScalar(u8, remapping.target, 0) != null) return error.InvalidRemapping;
            const target = try std.Io.Dir.path.resolve(scratch, &.{ project_root, remapping.target });
            const directory_target = remapping.target.len == 0 or std.Io.Dir.path.isSep(remapping.target[remapping.target.len - 1]);
            var matched = false;
            for (modules) |*module| {
                if (matches(module.absolute, target, directory_target)) {
                    module.selected = true;
                    matched = true;
                }
            }
            if (!matched and !try localTargetExists(io, target, directory_target)) {
                try report(io, "No Git submodule or local source provides remapping target '{s}'. Correct remappings.txt or declare the library with git submodule add.\n", .{remapping.target});
                return error.UnmanagedRemapping;
            }
        }
    } else {
        for (modules) |*module| module.selected = true;
    }

    var argv: std.ArrayList([]const u8) = .empty;
    defer argv.deinit(scratch);
    try argv.appendSlice(scratch, &.{ "git", "--literal-pathspecs", "-C", repository, "submodule", "update", "--init", "--recursive", "--checkout", "--jobs", try std.fmt.allocPrint(scratch, "{d}", .{jobs}), "--" });
    var selected: usize = 0;
    for (modules) |module| if (module.selected) {
        try argv.append(scratch, module.path);
        selected += 1;
    };
    if (selected == 0) {
        try report(io, "No Git submodules to install.\n", .{});
        return;
    }
    try report(io, "Installing {d} Git submodule(s) and their nested dependencies at recorded commits.\n", .{selected});
    // The final operation is Git itself: preserve terminal input, credentials,
    // progress, signals and its exact exit status without supervising its tree.
    if (std.process.can_replace)
        return std.process.replace(io, .{ .argv = argv.items, .expand_arg0 = .expand });
    var child = try std.process.spawn(io, .{ .argv = argv.items, .expand_arg0 = .expand });
    defer child.kill(io);
    const term = try child.wait(io);
    if (term != .exited or term.exited != 0) return error.GitFailed;
}

fn gitOutputAlloc(allocator: std.mem.Allocator, io: std.Io, argv: []const []const u8, allow_no_matches: bool) ![]u8 {
    const output = std.process.run(allocator, io, .{
        .argv = argv,
        .expand_arg0 = .expand,
        .stdout_limit = .limited(1024 * 1024),
        .stderr_limit = .limited(1024 * 1024),
        .timeout = .{ .duration = .{ .clock = .awake, .raw = .fromSeconds(30) } },
    }) catch |err| switch (err) {
        error.FileNotFound => {
            try report(io, "Git is required by oksolc install; install git and make it available on PATH.\n", .{});
            return error.GitNotInstalled;
        },
        else => return err,
    };
    errdefer allocator.free(output.stdout);
    defer allocator.free(output.stderr);
    if (output.stderr.len != 0) try std.Io.File.stderr().writeStreamingAll(io, output.stderr);
    if (output.term != .exited or (output.term.exited != 0 and
        !(allow_no_matches and output.term.exited == 1 and output.stdout.len == 0 and output.stderr.len == 0))) return error.GitFailed;
    return output.stdout;
}

/// Returned paths borrow config; absolute paths and the array belong to allocator.
fn modulesAlloc(allocator: std.mem.Allocator, repository: []const u8, config: []const u8) ![]Module {
    var modules: std.ArrayList(Module) = .empty;
    errdefer {
        for (modules.items) |module| allocator.free(module.absolute);
        modules.deinit(allocator);
    }
    var records = std.mem.splitScalar(u8, config, 0);
    while (records.next()) |record| {
        if (record.len == 0) {
            if (records.next() != null) return error.InvalidGitOutput;
            break;
        }
        if (!std.mem.endsWith(u8, config, "\x00")) return error.InvalidGitOutput;
        const separator = std.mem.findScalar(u8, record, '\n') orelse return error.InvalidGitOutput;
        const path = record[separator + 1 ..];
        ProjectSources.validatePath(path) catch return error.InvalidSubmodulePath;
        const absolute = try std.Io.Dir.path.resolve(allocator, &.{ repository, path });
        errdefer allocator.free(absolute);
        if (!ProjectSources.pathContainedBy(repository, absolute) or std.mem.eql(u8, absolute, repository)) return error.InvalidSubmodulePath;
        if (modules.items.len >= 4096) return error.TooManySubmodules;
        try modules.append(allocator, .{ .path = path, .absolute = absolute });
    }
    std.mem.sort(Module, modules.items, {}, struct {
        fn lessThan(_: void, a: Module, b: Module) bool {
            return std.mem.lessThan(u8, a.absolute, b.absolute);
        }
    }.lessThan);
    for (modules.items, 0..) |module, i| {
        if (i != 0 and std.mem.eql(u8, modules.items[i - 1].absolute, module.absolute)) return error.DuplicateSubmodulePath;
    }
    return modules.toOwnedSlice(allocator);
}

fn matches(module: []const u8, target: []const u8, directory_target: bool) bool {
    // A broad target can produce paths in several modules. A non-directory
    // target is a textual prefix, as in prefix=lib/Math followed by .sol.
    return ProjectSources.pathContainedBy(module, target) or if (directory_target) ProjectSources.pathContainedBy(target, module) else std.mem.startsWith(u8, module, target);
}

fn localTargetExists(io: std.Io, target: []const u8, directory_target: bool) !bool {
    if (std.Io.Dir.cwd().statFile(io, target, .{})) |stat| return !directory_target or stat.kind == .directory else |err| switch (err) {
        error.FileNotFound => {},
        else => return err,
    }
    if (directory_target) return false;
    const parent = std.Io.Dir.path.dirname(target) orelse return false;
    var directory = std.Io.Dir.cwd().openDir(io, parent, .{ .iterate = true }) catch |err| switch (err) {
        error.FileNotFound => return false,
        else => return err,
    };
    defer directory.close(io);
    var entries = directory.iterate();
    while (try entries.next(io)) |entry| {
        if (std.mem.startsWith(u8, entry.name, std.Io.Dir.path.basename(target))) return true;
    }
    return false;
}

fn report(io: std.Io, comptime format: []const u8, args: anytype) !void {
    var buffer: [1024]u8 = undefined;
    var writer = std.Io.File.stderr().writer(io, &buffer);
    try writer.interface.print(format, args);
    try writer.interface.flush();
}

test "install matches nested, broad and textual-prefix remapping targets" {
    try std.testing.expect(matches("/project/lib/pkg", "/project/lib/pkg/src", true));
    try std.testing.expect(!matches("/project/lib/pkg", "/project/lib/pkg-other/src", true));
    try std.testing.expect(matches("/project/lib/pkg", "/project/lib", true));
    try std.testing.expect(matches("/project/lib/pkg-extra", "/project/lib/pkg", false));
    try std.testing.expect(!matches("/project/lib/pkg-extra", "/project/lib/pkg", true));
}

test "install owns sorted paths and rejects malformed Git metadata across OOM" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn check(allocator: std.mem.Allocator) !void {
            const modules = try modulesAlloc(allocator, "/project", "submodule.b.path\nlib/b\x00submodule.a.path\nlib/a [x]\x00");
            defer allocator.free(modules);
            defer for (modules) |module| allocator.free(module.absolute);
            try std.testing.expectEqualStrings("lib/a [x]", modules[0].path);
            try std.testing.expectEqualStrings("/project/lib/b", modules[1].absolute);
        }
    }.check, .{});
    for ([_][]const u8{ "../outside", ".", "/absolute" }) |path| {
        const config = try std.fmt.allocPrint(std.testing.allocator, "submodule.a.path\n{s}\x00", .{path});
        defer std.testing.allocator.free(config);
        try std.testing.expectError(error.InvalidSubmodulePath, modulesAlloc(std.testing.allocator, "/project", config));
    }
    try std.testing.expectError(error.InvalidGitOutput, modulesAlloc(std.testing.allocator, "/project", "bad"));
    try std.testing.expectError(error.DuplicateSubmodulePath, modulesAlloc(std.testing.allocator, "/project", "submodule.a.path\nlib/a\x00submodule.b.path\nlib/a\x00"));
}
