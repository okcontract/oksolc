// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! CLI for the via-IR Zig compiler.
//!
//! Supports `--version` and `--standard-json` for Foundry integration.
//! The `compile` command enables via-IR compilation and optimization;
//! `standard-json` accepts requests through the machine interface.

const std = @import("std");
const builtin = @import("builtin");
const clap = @import("clap");
const solidity = @import("solidity");
const toml = @import("toml");
const ProjectSources = @import("project_sources.zig");
const BrowserLive = @import("browser/live.zig").Status;

const Profiler = solidity.libsolutil.profiler.Profiler;
const max_input_bytes = 256 * 1024 * 1024;
const max_source_bytes = 64 * 1024 * 1024;
const max_total_loaded_source_bytes = 64 * 1024 * 1024;
const max_source_path_bytes = 16 * 1024;
const max_source_roots = 128;
const max_project_config_bytes = 16 * 1024;
const max_serve_header_bytes = 16 * 1024;
const max_default_parallel_jobs = 2;
const default_watch_poll_milliseconds = 250;
const application_directory = "oksolc";
const user_config_filename = "config.toml";
const cache_authentication_key_filename = "cache-authentication-key-v1";
const cache_authentication_key_environment = "OKSOLC_CACHE_AUTH_KEY";
const cache_projects_directory = "projects-v2";
const artifact_cache_database = "artifacts.sqlite";
const project_config_filename = "oksolc.toml";
const repository_marker = ".git";

const main_params = clap.parseParamsComptime(
    \\-h, --help                       Display this help and exit.
    \\--version                        Display a solc-compatible version and exit.
    \\--standard-json                  Read Standard JSON from stdin (Foundry compatibility).
    \\--no-cache                      Do not read or write the persistent SQLite cache.
    \\--allow-paths <PATHS>            Additional allowed roots; not searched (comma-separated).
    \\--base-path <PATH>               Root for Standard JSON source lookups.
    \\--include-path <PATH>...         Additional lookup root; requires --base-path (repeatable).
    \\<COMMAND>
    \\
);

const main_parsers = .{
    .PATHS = clap.parsers.string,
    .PATH = clap.parsers.string,
    .COMMAND = clap.parsers.string,
};

const compile_params = clap.parseParamsComptime(
    \\-h, --help                      Display help for the compile command.
    \\-o, --output <FILE>             Write Standard JSON output to FILE instead of stdout.
    \\--parallel                      Compile independent contract backends in parallel.
    \\-j, --jobs <JOBS>               Total compiler jobs (requires --parallel; default: at most 2).
    \\--progress                      Display compilation progress on a terminal.
    \\--profile-optimizer <FILE>      Write request-scoped phase/pass timings as JSON.
    \\--no-cache                     Do not read or write the persistent SQLite cache.
    \\<SOURCE>...
    \\
);

const compile_parsers = .{
    .PATH = clap.parsers.string,
    .FILE = clap.parsers.string,
    .JOBS = clap.parsers.int(usize, 10),
    .SOURCE = clap.parsers.string,
    .SIZE = clap.parsers.string,
};

const standard_json_params = clap.parseParamsComptime(
    \\-h, --help                      Display help for the standard-json command.
    \\-o, --output <FILE>             Write Standard JSON output to FILE instead of stdout.
    \\--parallel                      Compile independent contract backends in parallel.
    \\-j, --jobs <JOBS>               Total compiler jobs (requires --parallel; default: at most 2).
    \\--progress                      Display compilation progress on a terminal.
    \\--profile-optimizer <FILE>      Write request-scoped phase/pass timings as JSON.
    \\--no-cache                     Do not read or write the persistent SQLite cache.
    \\--allow-paths <PATHS>           Additional allowed roots; not searched (comma-separated).
    \\--base-path <PATH>              Root for Standard JSON source lookups.
    \\--include-path <PATH>...        Additional lookup root; requires --base-path (repeatable).
    \\<INPUT>
    \\
);

const standard_json_parsers = .{
    .FILE = clap.parsers.string,
    .JOBS = clap.parsers.int(usize, 10),
    .PATHS = clap.parsers.string,
    .PATH = clap.parsers.string,
    .INPUT = clap.parsers.string,
    .SIZE = clap.parsers.string,
};

const browse_params = clap.parseParamsComptime(
    \\-h, --help                      Display browser help.
    \\--request <FILE>                Compile a Standard JSON request (or - for stdin).
    \\--import-output <FILE>          Browse existing output with --request, without recompiling.
    \\--database <FILE>               Snapshot database (default: <project>/.oksolc/browser.sqlite; :memory: for ephemeral).
    \\--port <PORT>                   Localhost port (default: 8080).
    \\--parallel                      Compile with bounded parallel jobs.
    \\-j, --jobs <JOBS>               Total compiler jobs (requires --parallel).
    \\--profile-optimizer <FILE>      Write compiler profiling data.
    \\--no-cache                     Disable the persistent compiler cache.
    \\--base-path <PATH>              Root for compiler source lookups.
    \\--include-path <PATH>...        Additional compiler source lookup roots.
    \\--allow-paths <PATHS>           Additional allowed source roots (comma-separated).
    \\<SOURCE>...
    \\
);
const browse_parsers = .{
    .FILE = clap.parsers.string,
    .PORT = clap.parsers.int(u16, 10),
    .JOBS = clap.parsers.int(usize, 10),
    .SIZE = clap.parsers.string,
    .PATH = clap.parsers.string,
    .PATHS = clap.parsers.string,
    .SOURCE = clap.parsers.string,
};

const serve_params = clap.parseParamsComptime(
    \\-h, --help                      Display help for the serve command.
    \\--browse                        Serve the live compiler browser on localhost.
    \\--database <FILE>              Browser database (default: <project-root>/.oksolc/browser.sqlite).
    \\--port <PORT>                  Browser port (default: 8080; requires --browse).
    \\--stdio                         Serve framed Standard JSON requests instead of watching sources.
    \\--source-path <PATH>            Project source directory (default: source-path in oksolc.toml, or src).
    \\--poll-ms <MILLISECONDS>        Source polling interval (default: 250).
    \\--parallel                      Compile independent contract backends in parallel.
    \\-j, --jobs <JOBS>               Total compiler jobs (requires --parallel; default: at most 2).
    \\--no-cache                     Do not read or write the persistent SQLite cache.
    \\--allow-paths <PATHS>           Additional allowed roots; not searched (comma-separated).
    \\--base-path <PATH>              Root for Standard JSON source lookups.
    \\--include-path <PATH>...        Additional lookup root; requires --base-path (repeatable).
    \\
);

const serve_parsers = .{
    .PORT = clap.parsers.int(u16, 10),
    .JOBS = clap.parsers.int(usize, 10),
    .PATHS = clap.parsers.string,
    .PATH = clap.parsers.string,
    .SIZE = clap.parsers.string,
    .FILE = clap.parsers.string,
    .MILLISECONDS = clap.parsers.int(u64, 10),
};

const watch_params = clap.parseParamsComptime(
    \\-h, --help                      Display help for the watch command.
    \\-o, --output <FILE>             Replace FILE with the latest Standard JSON output.
    \\--parallel                      Compile independent contract backends in parallel.
    \\-j, --jobs <JOBS>               Total compiler jobs (requires --parallel; default: at most 2).
    \\--poll-ms <MILLISECONDS>        Poll interval (default: 250).
    \\--once                          Compile once and exit (useful for automation).
    \\--no-cache                     Do not read or write the persistent SQLite cache.
    \\--allow-paths <PATHS>           Additional allowed roots; not searched (comma-separated).
    \\--base-path <PATH>              Root for Standard JSON source lookups.
    \\--include-path <PATH>...        Additional lookup root; requires --base-path (repeatable).
    \\<INPUT>
    \\
);

const watch_parsers = .{
    .FILE = clap.parsers.string,
    .JOBS = clap.parsers.int(usize, 10),
    .MILLISECONDS = clap.parsers.int(u64, 10),
    .PATHS = clap.parsers.string,
    .PATH = clap.parsers.string,
    .INPUT = clap.parsers.string,
    .SIZE = clap.parsers.string,
};

const cache_params = clap.parseParamsComptime(
    \\-h, --help                      Display help for cache maintenance.
    \\--max-bytes <SIZE>              Prune to SIZE bytes (supports KiB, MiB, GiB).
    \\--max-entries <ENTRIES>         Prune to at most ENTRIES artifacts.
    \\<OPERATION>
    \\
);

const cache_parsers = .{
    .SIZE = clap.parsers.string,
    .ENTRIES = clap.parsers.int(u64, 10),
    .OPERATION = clap.parsers.string,
};

const clean_params = clap.parseParamsComptime(
    \\-h, --help  Display help for the clean command.
    \\
);

pub fn main(init: std.process.Init) !void {
    var iterator = try init.minimal.args.iterateAllocator(init.gpa);
    defer iterator.deinit();
    _ = iterator.next();

    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &main_params,
        main_parsers,
        &iterator,
        .{
            .allocator = init.gpa,
            .diagnostic = &diagnostic,
            .terminating_positional = 0,
        },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();

    if (result.args.help != 0) return writeMainHelp(init.io);
    if (result.args.version != 0) {
        if (result.args.@"standard-json" != 0 or
            result.args.@"no-cache" != 0 or
            result.args.@"allow-paths" != null or
            result.args.@"base-path" != null or
            result.args.@"include-path".len != 0 or
            result.positionals[0] != null)
        {
            try std.Io.File.stderr().writeStreamingAll(
                init.io,
                "--version cannot be combined with other arguments\n",
            );
            return error.InvalidArgument;
        }
        return writeVersion(init, true);
    }
    if (result.args.@"standard-json" != 0) {
        if (result.positionals[0] != null) {
            try std.Io.File.stderr().writeStreamingAll(
                init.io,
                "--standard-json cannot be combined with a command\n",
            );
            return error.InvalidArgument;
        }
        return foundryStandardJsonCommand(
            init,
            result.args.@"base-path",
            result.args.@"include-path",
            result.args.@"allow-paths",
            result.args.@"no-cache" != 0,
        );
    }
    if (result.args.@"allow-paths" != null or
        result.args.@"base-path" != null or
        result.args.@"include-path".len != 0)
    {
        try std.Io.File.stderr().writeStreamingAll(
            init.io,
            "path options require --standard-json\n",
        );
        return error.InvalidArgument;
    }
    const command = result.positionals[0] orelse return writeMainHelp(init.io);
    if (std.mem.eql(u8, command, "compile"))
        return compileCommand(
            init,
            &iterator,
            result.args.@"no-cache" != 0,
        );
    if (std.mem.eql(u8, command, "standard-json"))
        return standardJsonCommand(
            init,
            &iterator,
            result.args.@"no-cache" != 0,
        );
    if (std.mem.eql(u8, command, "browse"))
        return browseCommand(init, &iterator, result.args.@"no-cache" != 0);
    if (std.mem.eql(u8, command, "serve"))
        return serveCommand(
            init,
            &iterator,
            result.args.@"no-cache" != 0,
        );
    if (std.mem.eql(u8, command, "watch"))
        return watchCommand(
            init,
            &iterator,
            result.args.@"no-cache" != 0,
        );
    if (result.args.@"no-cache" != 0) {
        try std.Io.File.stderr().writeStreamingAll(
            init.io,
            "--no-cache requires a compilation command\n",
        );
        return error.InvalidArgument;
    }
    if (std.mem.eql(u8, command, "cache"))
        return cacheCommand(init, &iterator);
    if (std.mem.eql(u8, command, "clean"))
        return cleanCommand(init, &iterator);
    if (std.mem.eql(u8, command, "install"))
        return installCommand(init, &iterator);
    if (std.mem.eql(u8, command, "version"))
        return versionCommand(init, &iterator);
    if (std.mem.eql(u8, command, "help"))
        return writeMainHelp(init.io);

    try std.Io.File.stderr().writeStreamingAll(init.io, "unknown command; see `oksolc help`\n");
    return error.UnknownCommand;
}

fn foundryStandardJsonCommand(
    init: std.process.Init,
    base_path: ?[]const u8,
    include_paths: []const []const u8,
    allow_paths: ?[]const u8,
    no_cache: bool,
) !void {
    try validateSourcePathArguments(base_path, include_paths);
    var parallel_options = try resolveParallelOptions(
        init,
        base_path,
        false,
        null,
        no_cache,
    );
    defer parallel_options.deinit();
    const input = try readInputAlloc(init, "-");
    defer init.gpa.free(input);
    try compileAndWrite(
        init,
        input,
        null,
        null,
        false,
        parallel_options.enabled,
        parallel_options.jobs,
        parallel_options.project_root,
        parallel_options.security_root,
        parallel_options.cache,
        .{
            .base_path = base_path orelse ".",
            .include_paths = include_paths,
            .allow_paths = allow_paths,
        },
    );
}

fn compileCommand(
    init: std.process.Init,
    iterator: *std.process.Args.Iterator,
    global_no_cache: bool,
) !void {
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &compile_params,
        compile_parsers,
        iterator,
        .{ .allocator = init.gpa, .diagnostic = &diagnostic },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();

    if (result.args.help != 0) return writeCompileHelp(init.io);
    const source_paths = result.positionals[0];
    if (source_paths.len == 0) {
        try std.Io.File.stderr().writeStreamingAll(init.io, "compile requires at least one Solidity source\n");
        return error.MissingSource;
    }
    var parallel_options = try resolveParallelOptions(
        init,
        null,
        result.args.parallel != 0,
        result.args.jobs,
        global_no_cache or result.args.@"no-cache" != 0,
    );
    defer parallel_options.deinit();

    var loaded_sources = try CompileInput.loadSourcesAt(init.gpa, init.io, source_paths, parallel_options.project_root);
    defer loaded_sources.deinit();
    const remappings = try CompileInput.readRemappingsAlloc(init.gpa, init.io, parallel_options.project_root);
    defer if (remappings) |contents| init.gpa.free(contents);
    const input = try CompileInput.buildAlloc(init.gpa, loaded_sources.sources, .{ .remappings = remappings });
    defer init.gpa.free(input);
    try compileAndWrite(
        init,
        input,
        result.args.output,
        result.args.@"profile-optimizer",
        result.args.progress != 0,
        parallel_options.enabled,
        parallel_options.jobs,
        parallel_options.project_root,
        parallel_options.security_root,
        parallel_options.cache,
        .{ .base_path = parallel_options.project_root },
    );
}

fn standardJsonCommand(
    init: std.process.Init,
    iterator: *std.process.Args.Iterator,
    global_no_cache: bool,
) !void {
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &standard_json_params,
        standard_json_parsers,
        iterator,
        .{ .allocator = init.gpa, .diagnostic = &diagnostic },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();

    if (result.args.help != 0) return writeStandardJsonHelp(init.io);
    try validateSourcePathArguments(
        result.args.@"base-path",
        result.args.@"include-path",
    );
    var parallel_options = try resolveParallelOptions(
        init,
        result.args.@"base-path",
        result.args.parallel != 0,
        result.args.jobs,
        global_no_cache or result.args.@"no-cache" != 0,
    );
    defer parallel_options.deinit();
    const input = try readInputAlloc(init, result.positionals[0]);
    defer init.gpa.free(input);
    try compileAndWrite(
        init,
        input,
        result.args.output,
        result.args.@"profile-optimizer",
        result.args.progress != 0,
        parallel_options.enabled,
        parallel_options.jobs,
        parallel_options.project_root,
        parallel_options.security_root,
        parallel_options.cache,
        .{
            .base_path = result.args.@"base-path" orelse ".",
            .include_paths = result.args.@"include-path",
            .allow_paths = result.args.@"allow-paths",
        },
    );
}

fn browseCommand(init: std.process.Init, iterator: *std.process.Args.Iterator, global_no_cache: bool) !void {
    const BrowserStore = @import("browser/store.zig").Store;
    const BrowserServer = @import("browser/server.zig");
    const Capture = @import("browser/capture.zig").Capture;
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(clap.Help, &browse_params, browse_parsers, iterator, .{ .allocator = init.gpa, .diagnostic = &diagnostic }) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();
    if (result.args.help != 0) {
        try std.Io.File.stdout().writeStreamingAll(init.io, "usage: oksolc browse [--request FILE | SOURCE...] [--database FILE] [--port 8080]\n\nCompile sources, import output with --request and --import-output, or reopen saved snapshots.\nDefaults to .oksolc/browser.sqlite in the nearest project root (oksolc.toml or .git).\nThe server binds only to 127.0.0.1. Browser compilation requests source ASTs for navigation.\n\n");
        return clap.helpToFile(init.io, .stdout(), clap.Help, &browse_params, .{});
    }
    const paths = result.positionals[0];
    const has_input = result.args.request != null or paths.len != 0;
    if (result.args.request != null and paths.len != 0) return error.ConflictingBrowseInputs;
    if (result.args.@"import-output" != null and result.args.request == null) return error.ImportRequiresRequest;
    const compiling = has_input and result.args.@"import-output" == null;
    if (!compiling and result.args.@"profile-optimizer" != null) return error.ProfileRequiresCompilation;
    const port = result.args.port orelse 8080;
    if (port == 0) return error.InvalidPort;
    try validateSourcePathArguments(result.args.@"base-path", result.args.@"include-path");
    const database_path = try browserDatabasePathAlloc(init, result.args.database, result.args.@"base-path");
    defer init.gpa.free(database_path);
    var store = try BrowserStore.open(init.gpa, init.io, database_path);
    defer store.deinit();
    if (has_input) {
        var resolved: ?ParallelOptions = if (compiling) try resolveParallelOptions(init, result.args.@"base-path", result.args.parallel != 0, result.args.jobs, global_no_cache or result.args.@"no-cache" != 0) else null;
        defer if (resolved) |*options| options.deinit();
        const request = if (result.args.request) |path| read: {
            const original = try readInputAlloc(init, path);
            defer init.gpa.free(original);
            break :read if (result.args.@"import-output" != null) try init.gpa.dupe(u8, original) else try CompileInput.withAstAlloc(init.gpa, original);
        } else source: {
            var loaded = try CompileInput.loadSourcesAt(init.gpa, init.io, paths, resolved.?.project_root);
            defer loaded.deinit();
            const remappings = try CompileInput.readRemappingsAlloc(init.gpa, init.io, resolved.?.project_root);
            defer if (remappings) |contents| init.gpa.free(contents);
            break :source try CompileInput.buildAlloc(init.gpa, loaded.sources, .{ .ast = true, .remappings = remappings });
        };
        defer init.gpa.free(request);
        if (result.args.@"import-output") |path| {
            const output = try readDocumentAlloc(init, path, @import("browser/store.zig").max_document_bytes);
            defer init.gpa.free(output);
            _ = try store.importCompilation(init.gpa, result.args.request.?, .imported, request, output, &.{});
        } else {
            const options = &resolved.?;
            const jobs = if (options.enabled) options.jobs orelse defaultParallelJobs() else 1;
            var backend: std.Io.Threaded = undefined;
            const compiler_io: ?std.Io = if (options.enabled) io: {
                backend = .init(std.heap.smp_allocator, .{ .async_limit = .limited(jobs - 1) });
                break :io backend.io();
            } else null;
            defer if (options.enabled) backend.deinit();
            var loader = try FileSourceLoader.init(init.gpa, init.io, .{
                .base_path = if (result.args.request == null) options.project_root else result.args.@"base-path" orelse ".",
                .include_paths = result.args.@"include-path",
                .allow_paths = result.args.@"allow-paths",
            });
            defer loader.deinit();
            var capture: Capture = .{ .allocator = init.gpa, .loader = loader.interface() };
            defer capture.deinit();
            var session = try WorkflowSession.init(init, options.project_root, options.security_root, options.cache);
            defer session.deinit();
            var profiler = Profiler.init(init.gpa, init.io);
            defer profiler.deinit();
            session.setOptimizerProfiler(if (result.args.@"profile-optimizer" != null) &profiler else null);
            var output = try session.compiler().compile(init.gpa, .{
                .input = request,
                .io = compiler_io,
                .source_loader = capture.interface(),
            });
            defer output.deinit();
            const captured = try capture.listAlloc(init.gpa);
            defer init.gpa.free(captured);
            _ = try store.importCompilation(init.gpa, result.args.request orelse paths[0], .compiled, request, output.bytes, captured);
            if (result.args.@"profile-optimizer") |path| {
                const report = try profiler.reportJsonAlloc(init.gpa);
                defer init.gpa.free(report);
                try writeOutput(init.io, path, report);
            }
        }
    }
    // Every compilation owner is destroyed before the server starts.
    try BrowserServer.run(init.gpa, init.io, &store, port, null);
}

fn browserDatabasePathAlloc(init: std.process.Init, explicit: ?[]const u8, base_path: ?[]const u8) ![]u8 {
    if (explicit) |path| return init.gpa.dupe(u8, path);
    const project_root = try projectRootAlloc(init, base_path);
    defer init.gpa.free(project_root);
    const directory_path = try std.Io.Dir.path.join(init.gpa, &.{ project_root, ".oksolc" });
    defer init.gpa.free(directory_path);
    var directory = try std.Io.Dir.cwd().createDirPathOpen(init.io, directory_path, .{
        .open_options = .{ .follow_symlinks = false },
        .permissions = secure_directory_permissions,
    });
    defer directory.close(init.io);
    return std.Io.Dir.path.join(init.gpa, &.{ directory_path, "browser.sqlite" });
}

fn serveCommand(
    init: std.process.Init,
    iterator: *std.process.Args.Iterator,
    global_no_cache: bool,
) !void {
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &serve_params,
        serve_parsers,
        iterator,
        .{ .allocator = init.gpa, .diagnostic = &diagnostic },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();

    if (result.args.help != 0) return writeServeHelp(init.io);
    if (result.args.stdio != 0 and (result.args.@"source-path" != null or
        result.args.@"poll-ms" != null or result.args.browse != 0))
        return error.ConflictingServeModes;
    if (result.args.browse == 0 and (result.args.database != null or result.args.port != null)) return error.BrowserOptionsRequireBrowse;
    const port = result.args.port orelse 8080;
    if (port == 0) return error.InvalidPort;
    try validateSourcePathArguments(
        result.args.@"base-path",
        result.args.@"include-path",
    );
    var options = try resolveParallelOptions(
        init,
        result.args.@"base-path",
        result.args.parallel != 0,
        result.args.jobs,
        global_no_cache or result.args.@"no-cache" != 0,
    );
    defer options.deinit();
    const jobs = if (options.enabled)
        options.jobs orelse defaultParallelJobs()
    else
        1;

    var parallel_backend: std.Io.Threaded = undefined;
    const compiler_io: ?std.Io = if (options.enabled) io: {
        parallel_backend = .init(std.heap.smp_allocator, .{
            .async_limit = .limited(jobs - 1),
        });
        break :io parallel_backend.io();
    } else null;
    defer if (options.enabled) parallel_backend.deinit();

    const defer_session = result.args.stdio == 0 and result.args.browse != 0 and options.cache.enabled;
    var session = if (defer_session)
        WorkflowSession{ .memory = solidity.CompilerSession.init(init.gpa) }
    else
        try WorkflowSession.init(init, options.project_root, options.security_root, options.cache);
    defer session.deinit();
    if (result.args.stdio == 0) {
        const source_path = result.args.@"source-path" orelse options.source_path;
        try ProjectSources.validatePath(source_path);
        const poll_ms = result.args.@"poll-ms" orelse default_watch_poll_milliseconds;
        if (poll_ms == 0 or poll_ms > std.math.maxInt(i64)) return error.InvalidPollInterval;
        const directory_path = try std.Io.Dir.path.resolve(init.gpa, &.{ options.project_root, source_path });
        defer init.gpa.free(directory_path);
        if (!pathContainedBy(options.project_root, directory_path)) return error.InvalidSourcePath;
        const prefix = std.mem.trimStart(u8, directory_path[options.project_root.len..], "/\\");
        var loader = try FileSourceLoader.init(init.gpa, init.io, .{
            .base_path = options.project_root,
            .include_paths = result.args.@"include-path",
            .allow_paths = result.args.@"allow-paths",
        });
        defer loader.deinit();
        var store: ?@import("browser/store.zig").Store = if (result.args.browse != 0) store: {
            const database_path = try browserDatabasePathAlloc(init, result.args.database, options.project_root);
            defer init.gpa.free(database_path);
            break :store try @import("browser/store.zig").Store.open(init.gpa, init.io, database_path);
        } else null;
        defer if (store) |*value| value.deinit();
        var live: BrowserLive = .{
            .io = init.io,
            .source_path = if (prefix.len == 0) "." else prefix,
            .snapshot = .{ .state = .{ .phase = .starting }, .latest = if (store) |*value| try value.latest() else null },
        };
        // Browser snapshots resume by default. Other compiler artifacts retain
        // their separate opt-in policy; no-cache skips every persistent reuse.
        const resume_key = if (store != null and !global_no_cache and result.args.@"no-cache" == 0 and solidity.incremental.CompilerFingerprint.current().isPersistentSafe())
            options.cache.authentication_key orelse loadOrCreateCacheAuthenticationKey(init, options.security_root) catch |err| switch (err) {
                error.OutOfMemory, error.InvalidCacheAuthenticationKey => return err,
                else => null,
            }
        else
            null;
        var service: SourceService = .{
            .allocator = init.gpa,
            .io = init.io,
            .compiler_io = compiler_io,
            .compiler = session.compiler(),
            .deferred_session = if (defer_session) .{ .owner = &session, .process_init = init, .security_root = options.security_root, .cache_policy = options.cache } else null,
            .loader = &loader,
            .directory_path = directory_path,
            .project_root = options.project_root,
            .prefix = prefix,
            .poll_ms = poll_ms,
            .store = if (store) |*value| value else null,
            .live = if (store != null) &live else null,
            .resume_key = resume_key,
            .jobs = jobs,
        };
        defer service.deinit();
        if (store) |*value| {
            var future = try init.io.concurrent(SourceService.run, .{&service});
            const browser_result = @import("browser/server.zig").run(init.gpa, init.io, value, port, &live);
            // Join the watcher before propagating either task's result.
            const watcher_result = future.cancel(init.io);
            try browser_result;
            return watcher_result catch |err| switch (err) {
                error.Canceled => {},
                else => return err,
            };
        }
        try service.update();
        return service.run();
    }
    const filesystem_roots_configured = result.args.@"base-path" != null or
        result.args.@"include-path".len != 0 or
        result.args.@"allow-paths" != null;
    var loader_state: ?FileSourceLoader = if (filesystem_roots_configured)
        try FileSourceLoader.init(init.gpa, init.io, .{
            .base_path = result.args.@"base-path",
            .include_paths = result.args.@"include-path",
            .allow_paths = result.args.@"allow-paths",
        })
    else
        null;
    defer if (loader_state) |*loader| loader.deinit();
    var read_buffer: [16 * 1024]u8 = undefined;
    var reader = std.Io.File.stdin().reader(init.io, &read_buffer);
    var write_buffer: [16 * 1024]u8 = undefined;
    var writer = std.Io.File.stdout().writer(init.io, &write_buffer);

    while (try readServeFrameAlloc(&reader.interface, init.gpa)) |input| {
        defer init.gpa.free(input);
        if (loader_state) |*loader| loader.reset();
        var output = try session.compiler().compile(init.gpa, .{
            .input = input,
            .io = compiler_io,
            .source_loader = if (loader_state) |*loader|
                loader.interface()
            else
                null,
        });
        defer output.deinit();
        try writeServeFrame(&writer.interface, output.bytes);
        try writer.interface.flush();
    }
}

/// One owner retains the compiler session and the last observed read set.
/// Polling uses contents, so same-size edits and coarse timestamps are safe.
const SourceService = struct {
    const Capture = @import("browser/capture.zig").Capture;
    const Resume = @import("browser/resume.zig");
    allocator: std.mem.Allocator,
    io: std.Io,
    compiler_io: ?std.Io,
    compiler: solidity.standard_json.Compiler,
    /// Created by this worker only after workspace publication and a snapshot
    /// miss. All borrowed process/configuration state outlives the worker join.
    deferred_session: ?struct {
        owner: *WorkflowSession,
        process_init: std.process.Init,
        security_root: []const u8,
        cache_policy: CachePolicy,
    } = null,
    loader: *FileSourceLoader,
    directory_path: []const u8,
    project_root: []const u8,
    prefix: []const u8,
    poll_ms: u64,
    names: ?ProjectSources.Names = null,
    capture: ?Capture = null,
    remappings: ?[]const u8 = null,
    store: ?*@import("browser/store.zig").Store = null,
    live: ?*BrowserLive = null,
    resume_key: ?Resume.Key = null,
    jobs: usize = 1,
    /// One completed compiler result awaiting publication. The request and full
    /// callback read set belong to this owner, never to an update's scratch arena.
    pending: ?struct {
        input: []u8,
        output: solidity.standard_json.Output,
        capture: Capture,
    } = null,

    fn discardPending(self: *SourceService) void {
        if (self.pending) |*pending| {
            self.allocator.free(pending.input);
            pending.output.deinit();
            pending.capture.deinit();
            self.pending = null;
        }
    }

    fn deinit(self: *SourceService) void {
        self.discardPending();
        if (self.names) |*names| names.deinit();
        if (self.capture) |*capture| capture.deinit();
        if (self.remappings) |text| self.allocator.free(text);
    }

    fn contextDigest(self: *SourceService, allocator: std.mem.Allocator) ![64]u8 {
        const Root = struct { path: []const u8, lookup: bool };
        const roots = try allocator.alloc(Root, self.loader.roots.items.len);
        defer allocator.free(roots);
        for (self.loader.roots.items, roots) |root, *entry| entry.* = .{ .path = root.canonical_path, .lookup = root.lookup };
        const fingerprint = solidity.incremental.CompilerFingerprint.current();
        const context = try std.json.Stringify.valueAlloc(allocator, .{
            .compiler = std.fmt.bytesToHex(fingerprint.bytes()[0..32].*, .lower),
            .project = self.project_root,
            .source_path = self.directory_path,
            .roots = roots,
            .max_source_bytes = self.loader.max_total_bytes,
            .parallel = self.compiler_io != null,
            .jobs = self.jobs,
        }, .{});
        defer allocator.free(context);
        return @import("browser/store.zig").digest(context);
    }

    fn tryResume(self: *SourceService, context: []const u8, input: []const u8, capture: *Capture) !?i64 {
        // SQL/parser copies die before a miss starts the compiler. Only replayed
        // source bytes owned by the invocation allocator can move out.
        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();
        const allocator = arena.allocator();
        self.live.?.set(.{ .phase = .checking });
        const candidate = try self.store.?.resumeAlloc(allocator, context) orelse return null;
        if (!std.mem.eql(u8, input, candidate.request) or !Resume.authentic(self.resume_key.?, candidate)) return null;
        self.loader.reset();
        defer self.loader.reset();
        var replay: Capture = .{ .allocator = self.allocator, .loader = self.loader.interface() };
        defer replay.deinit();
        if (!try replay.restore(allocator, candidate.receipt.manifest) or !replay.includes(capture)) return null;
        std.mem.swap(Capture, capture, &replay);
        return candidate.id;
    }

    fn run(self: *SourceService) anyerror!void {
        errdefer |err| if (self.live) |live| live.set(.{ .phase = .stopped, .failure = @errorName(err) });
        var last_error: ?anyerror = null;
        var initial = self.names == null;
        while (true) {
            if (!initial) try std.Io.sleep(self.io, .fromMilliseconds(@intCast(self.poll_ms)), .awake);
            initial = false;
            self.update() catch |err| {
                if (err == error.Canceled) return error.Canceled;
                if (last_error) |previous| if (previous == err) continue;
                last_error = err;
                var buffer: [512]u8 = undefined;
                const message = if (self.pending) |pending|
                    try std.fmt.bufPrint(&buffer, "oksolc serve: {s}; completed output retained (request {d} bytes, output {d} bytes), retrying publication.\n", .{ @errorName(err), pending.input.len, pending.output.bytes.len })
                else
                    try std.fmt.bufPrint(&buffer, "oksolc serve: {s}; last output is stale, retrying.\n", .{@errorName(err)});
                try std.Io.File.stderr().writeStreamingAll(self.io, message);
                continue;
            };
            if (last_error != null) try std.Io.File.stderr().writeStreamingAll(self.io, "oksolc serve: source watching recovered.\n");
            last_error = null;
        }
    }

    fn compileAndPublish(self: *SourceService, scratch: std.mem.Allocator, input: []const u8, capture: *Capture, context: ?[64]u8) !void {
        if (self.deferred_session) |pending| {
            const replacement = try WorkflowSession.init(pending.process_init, self.project_root, pending.security_root, pending.cache_policy);
            pending.owner.deinit();
            pending.owner.* = replacement;
            self.compiler = pending.owner.compiler();
            self.deferred_session = null;
        }
        if (self.pending == null) {
            // Allocate the retained request before starting expensive work, so
            // an allocation failure cannot discard an already finished result.
            const owned_input = try self.allocator.dupe(u8, input);
            errdefer self.allocator.free(owned_input);
            // Each request has its own loader budget. Capture keeps the read set
            // consistent for publication, including source edits.
            self.loader.reset();
            const output = try self.compiler.compile(self.allocator, .{
                .input = input,
                .progress = if (self.live) |live| live.reporter() else null,
                .io = self.compiler_io,
                .source_loader = capture.interface(),
            });
            self.pending = .{
                .input = owned_input,
                .output = output,
                .capture = .{ .allocator = self.allocator, .loader = self.loader.interface() },
            };
        } else {
            std.debug.assert(std.mem.eql(u8, self.pending.?.input, input));
            // update checked the complete read set before selecting this phase.
            std.mem.swap(Capture, capture, &self.pending.?.capture);
            self.pending.?.capture.deinit();
            self.pending.?.capture = .{ .allocator = self.allocator, .loader = self.loader.interface() };
        }
        // A failed save moves the exact read set alongside the finished output.
        // The next poll retries publication, including after a rolled-back SQL
        // transaction, without invoking the compiler again for unchanged inputs.
        errdefer std.mem.swap(Capture, capture, &self.pending.?.capture);
        const output = self.pending.?.output;
        if (self.store) |store| {
            self.live.?.set(.{ .phase = .publishing });
            const captured = try capture.listAlloc(scratch);
            const manifest = if (context != null) try capture.manifestAlloc(scratch) else null;
            const tag = if (manifest) |value| Resume.seal(self.resume_key.?, &context.?, input, output.bytes, value) else null;
            const receipt: ?@import("browser/store.zig").Receipt = if (manifest) |value| .{ .context = &context.?, .manifest = value, .seal = &tag.? } else null;
            const id = try store.publish(self.allocator, if (self.prefix.len == 0) "." else self.prefix, .compiled, input, output.bytes, captured, receipt);
            self.live.?.published(id, false);
        } else {
            try writeOutput(self.io, null, output.bytes);
            if (!std.mem.endsWith(u8, output.bytes, "\n")) try std.Io.File.stdout().writeStreamingAll(self.io, "\n");
        }
        self.discardPending();
    }

    fn update(self: *SourceService) !void {
        errdefer |err| if (self.live) |live| live.set(.{ .phase = .stale, .failure = @errorName(err) });
        // Loader capabilities are pinned directory handles. A moved project or
        // include root must not keep supplying bytes from its old location.
        for (self.loader.roots.items) |root| {
            var buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
            const length = try root.directory.realPath(self.io, &buffer);
            if (!std.mem.eql(u8, root.canonical_path, buffer[0..length])) return error.SourceRootChanged;
        }
        // Settings, projected roots and request JSON share one phase lifetime.
        var arena = std.heap.ArenaAllocator.init(self.allocator);
        defer arena.deinit();
        const scratch = arena.allocator();
        var directory = try self.loader.openCanonicalDirectory(self.directory_path, true);
        defer directory.close(self.io);
        var names = try ProjectSources.collectRootsAlloc(self.allocator, self.io, &.{.{ .directory = directory, .prefix = self.prefix }});
        defer names.deinit();
        var remappings = try CompileInput.readRemappingsAlloc(self.allocator, self.io, self.project_root);
        defer if (remappings) |text| self.allocator.free(text);
        self.loader.reset();
        if (self.names) |previous| {
            if (optionalTextEqual(self.remappings, remappings) and
                previous.eql(names) and !try self.capture.?.changed(self.allocator))
            {
                self.discardPending();
                if (self.live) |live| live.set(.{});
                return;
            }
        }
        // Once a new revision starts, the previous successful read set cannot
        // justify the current page after a save failure. Reverting an edit
        // must restore that page.
        if (self.names) |*previous| previous.deinit();
        self.names = null;
        if (self.live) |live| live.set(.{ .phase = .reading, .total_items = names.items.items.len });
        self.loader.reset();
        var capture: Capture = .{ .allocator = self.allocator, .loader = self.loader.interface() };
        defer capture.deinit();
        // Nothing borrowed from the request arena survives publication or the
        // compilation's join. Captured source bytes have separate ownership.
        const roots = try scratch.alloc(CompileInput.Source, names.items.items.len);
        for (names.items.items, roots, 0..) |name, *root, index| {
            const read = try capture.interface().read(scratch, "source", name);
            if (read != .contents) return error.SourceReadFailed;
            root.* = .{ .name = name, .content = read.contents };
            if (self.live) |live| live.set(.{ .phase = .reading, .completed_items = index + 1, .total_items = roots.len });
        }
        const input = try CompileInput.buildAlloc(scratch, roots, .{ .ast = true, .remappings = remappings });
        const context = if (self.store != null and self.resume_key != null) try self.contextDigest(scratch) else null;
        if (self.pending) |*pending| {
            self.loader.reset();
            if (!std.mem.eql(u8, input, pending.input) or
                !pending.capture.includes(&capture) or try pending.capture.changed(self.allocator))
                self.discardPending();
        }
        if (self.pending == null) if (self.store) |store| {
            try store.replaceWorkspace(try capture.listAlloc(scratch));
            self.live.?.workspaceChanged();
        };
        const reused = if (self.pending == null and context != null) try self.tryResume(&context.?, input, &capture) else null;
        if (reused) |id| {
            self.live.?.published(id, true);
        } else {
            try self.compileAndPublish(scratch, input, &capture, context);
        }
        if (self.live) |live| live.set(.{});
        // Publication succeeded: move ownership, retaining only the new read
        // set so dependencies removed by an edit stop triggering compilation.
        if (self.names) |*previous| previous.deinit();
        self.names = names;
        names = .{ .allocator = self.allocator };
        if (self.capture) |*previous| previous.deinit();
        self.capture = capture;
        capture = .{ .allocator = self.allocator, .loader = self.loader.interface() };
        if (self.remappings) |previous| self.allocator.free(previous);
        self.remappings = remappings;
        remappings = null;
    }
};

fn optionalTextEqual(left: ?[]const u8, right: ?[]const u8) bool {
    return if (left) |previous| if (right) |current| std.mem.eql(u8, previous, current) else false else right == null;
}

fn watchCommand(
    init: std.process.Init,
    iterator: *std.process.Args.Iterator,
    global_no_cache: bool,
) !void {
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &watch_params,
        watch_parsers,
        iterator,
        .{ .allocator = init.gpa, .diagnostic = &diagnostic },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();

    if (result.args.help != 0) return writeWatchHelp(init.io);
    try validateSourcePathArguments(
        result.args.@"base-path",
        result.args.@"include-path",
    );
    const input_path = result.positionals[0] orelse return error.MissingInput;
    if (result.args.output) |output_path|
        if (std.mem.eql(u8, input_path, output_path)) return error.DuplicateOutputPath;
    const poll_milliseconds = result.args.@"poll-ms" orelse
        default_watch_poll_milliseconds;
    if (poll_milliseconds == 0 or poll_milliseconds > std.math.maxInt(i64))
        return error.InvalidPollInterval;

    var options = try resolveParallelOptions(
        init,
        result.args.@"base-path",
        result.args.parallel != 0,
        result.args.jobs,
        global_no_cache or result.args.@"no-cache" != 0,
    );
    defer options.deinit();
    const jobs = if (options.enabled)
        options.jobs orelse defaultParallelJobs()
    else
        1;
    var parallel_backend: std.Io.Threaded = undefined;
    const compiler_io: ?std.Io = if (options.enabled) io: {
        parallel_backend = .init(std.heap.smp_allocator, .{
            .async_limit = .limited(jobs - 1),
        });
        break :io parallel_backend.io();
    } else null;
    defer if (options.enabled) parallel_backend.deinit();

    var session = try WorkflowSession.init(
        init,
        options.project_root,
        options.security_root,
        options.cache,
    );
    defer session.deinit();
    var loader_state = try FileSourceLoader.init(init.gpa, init.io, .{
        .base_path = result.args.@"base-path" orelse ".",
        .include_paths = result.args.@"include-path",
        .allow_paths = result.args.@"allow-paths",
    });
    defer loader_state.deinit();
    var last_digest: ?solidity.libsolutil.fixed_hash.H256 = null;
    var last_stamp: ?WatchStamp = null;

    while (true) {
        const stamp = try watchStamp(init.io, input_path);
        if (stamp == null) {
            if (last_digest == null) return error.FileNotFound;
        } else if (last_stamp == null or !stamp.?.eql(last_stamp.?)) {
            const input = std.Io.Dir.cwd().readFileAlloc(
                init.io,
                input_path,
                init.gpa,
                .limited(max_input_bytes),
            ) catch |err| switch (err) {
                error.FileNotFound => null,
                else => return err,
            };
            if (input) |bytes| {
                defer init.gpa.free(bytes);
                const digest = solidity.libsolutil.keccak256.keccak256(bytes);
                const changed = if (last_digest) |*previous|
                    !previous.eql(&digest)
                else
                    true;
                last_stamp = stamp;
                if (changed) {
                    loader_state.reset();
                    var output = try session.compiler().compile(init.gpa, .{
                        .input = bytes,
                        .io = compiler_io,
                        .source_loader = loader_state.interface(),
                    });
                    defer output.deinit();
                    try writeOutput(init.io, result.args.output, output.bytes);
                    last_digest = digest;
                }
            } else if (last_digest == null) {
                return error.FileNotFound;
            }
        }

        if (result.args.once != 0) return;
        try std.Io.sleep(
            init.io,
            .fromMilliseconds(@intCast(poll_milliseconds)),
            .awake,
        );
    }
}

fn cacheCommand(
    init: std.process.Init,
    iterator: *std.process.Args.Iterator,
) !void {
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &cache_params,
        cache_parsers,
        iterator,
        .{ .allocator = init.gpa, .diagnostic = &diagnostic },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();
    if (result.args.help != 0) return writeCacheHelp(init.io);

    const operation = result.positionals[0] orelse return writeCacheHelp(init.io);
    const project_root = try projectRootAlloc(init, null);
    defer init.gpa.free(project_root);
    const security_root = try securityRootAlloc(init.gpa, init.io, project_root);
    defer init.gpa.free(security_root);
    const config = try loadProjectConfig(init, project_root, security_root);
    defer config.deinit(init.gpa);
    const default_store_options: solidity.incremental.SqliteStoreOptions = .{};
    const configured_limits: solidity.incremental.CacheLimits = .{
        .max_entries = config.cache_max_entries orelse
            default_store_options.limits.max_entries,
        .max_bytes = config.cache_max_bytes orelse
            default_store_options.limits.max_bytes,
    };
    const busy_timeout_ms = config.cache_busy_timeout_ms orelse
        default_store_options.busy_timeout_ms;
    const requested_limits: solidity.incremental.CacheLimits = .{
        .max_entries = result.args.@"max-entries" orelse configured_limits.max_entries,
        .max_bytes = if (result.args.@"max-bytes") |value|
            parseByteSize(value) catch return error.InvalidByteSize
        else
            configured_limits.max_bytes,
    };
    const is_stats = std.mem.eql(u8, operation, "stats");
    const is_prune = std.mem.eql(u8, operation, "prune");
    if (!is_stats and !is_prune) return error.UnknownCacheOperation;
    if (is_stats and
        (result.args.@"max-bytes" != null or result.args.@"max-entries" != null))
    {
        return error.CacheLimitsRequirePrune;
    }

    const path = try artifactCachePathAlloc(init, project_root);
    defer init.gpa.free(path);
    if (pathContainedBy(security_root, path))
        return error.CacheDirectoryInsideProject;
    const exists = exists: {
        std.Io.Dir.cwd().access(init.io, path, .{}) catch |err| switch (err) {
            error.FileNotFound => break :exists false,
            else => return err,
        };
        break :exists true;
    };
    if (!exists) return writeJsonLine(init, .{
        .operation = operation,
        .path = path,
        .exists = false,
        .max_entries = requested_limits.max_entries,
        .max_bytes = requested_limits.max_bytes,
    });
    if (!try prepareTrustedArtifactCacheDirectory(
        init.gpa,
        init.io,
        path,
        security_root,
    ))
        return error.CacheDirectoryUnavailable;
    const authentication_key = try loadOrCreateCacheAuthenticationKey(init, security_root);

    var store = try solidity.incremental.SqliteStore.initWithOptions(
        init.gpa,
        init.io,
        path,
        authentication_key,
        .{
            .limits = .unlimited,
            .busy_timeout_ms = busy_timeout_ms,
        },
    );
    defer store.deinit();
    if (is_stats) {
        const summary = try store.summary();
        const physical = try cachePhysicalSizes(init.gpa, init.io, path);
        return writeJsonLine(init, .{
            .operation = operation,
            .path = path,
            .exists = true,
            .entries = summary.entries,
            .logical_bytes = summary.logical_bytes,
            .epoch = summary.epoch,
            .database_bytes = physical.database,
            .wal_bytes = physical.wal,
            .shared_memory_bytes = physical.shared_memory,
            .physical_bytes = physical.total(),
            .max_entries = configured_limits.max_entries,
            .max_bytes = configured_limits.max_bytes,
        });
    }

    const report = try store.prune(requested_limits);
    const physical = try cachePhysicalSizes(init.gpa, init.io, path);
    return writeJsonLine(init, .{
        .operation = operation,
        .path = path,
        .exists = true,
        .before_entries = report.before.entries,
        .before_logical_bytes = report.before.logical_bytes,
        .after_entries = report.after.entries,
        .after_logical_bytes = report.after.logical_bytes,
        .entries_removed = report.entries_removed,
        .logical_bytes_removed = report.logical_bytes_removed,
        .physical_bytes = physical.total(),
        .max_entries = requested_limits.max_entries,
        .max_bytes = requested_limits.max_bytes,
    });
}

fn cleanCommand(
    init: std.process.Init,
    iterator: *std.process.Args.Iterator,
) !void {
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &clean_params,
        clap.parsers.default,
        iterator,
        .{ .allocator = init.gpa, .diagnostic = &diagnostic },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();
    if (result.args.help != 0) return writeCleanHelp(init.io);

    const project_root = try projectRootAlloc(init, null);
    defer init.gpa.free(project_root);
    const security_root = try securityRootAlloc(init.gpa, init.io, project_root);
    defer init.gpa.free(security_root);
    const cache_path = try artifactCacheDirectoryPathAlloc(init, project_root);
    defer init.gpa.free(cache_path);
    if (pathContainedBy(security_root, cache_path))
        return error.CacheDirectoryInsideProject;
    const removed = try deleteCacheDirectory(init, cache_path, security_root);
    return writeJsonLine(init, .{
        .operation = "clean",
        .project_root = project_root,
        .path = cache_path,
        .removed = removed,
    });
}

const CachePhysicalSizes = struct {
    database: u64,
    wal: u64,
    shared_memory: u64,

    fn total(self: CachePhysicalSizes) u64 {
        return self.database +| self.wal +| self.shared_memory;
    }
};

fn cachePhysicalSizes(
    allocator: std.mem.Allocator,
    io: std.Io,
    database_path: []const u8,
) !CachePhysicalSizes {
    return .{
        .database = try fileSizeOrZero(io, database_path),
        .wal = try suffixedFileSizeOrZero(allocator, io, database_path, "-wal"),
        .shared_memory = try suffixedFileSizeOrZero(
            allocator,
            io,
            database_path,
            "-shm",
        ),
    };
}

fn suffixedFileSizeOrZero(
    allocator: std.mem.Allocator,
    io: std.Io,
    path: []const u8,
    suffix: []const u8,
) !u64 {
    const suffixed = try std.fmt.allocPrint(allocator, "{s}{s}", .{ path, suffix });
    defer allocator.free(suffixed);
    return fileSizeOrZero(io, suffixed);
}

fn fileSizeOrZero(io: std.Io, path: []const u8) !u64 {
    const stat = std.Io.Dir.cwd().statFile(io, path, .{}) catch |err| switch (err) {
        error.FileNotFound => return 0,
        else => return err,
    };
    if (stat.kind != .file) return error.NotAFile;
    return stat.size;
}

fn installCommand(init: std.process.Init, iterator: *std.process.Args.Iterator) !void {
    const params = comptime clap.parseParamsComptime(
        \\-h, --help           Display library installation help.
        \\--base-path <PATH>   Project directory (default: detected project root).
        \\-j, --jobs <JOBS>    Parallel Git clone jobs (default: 4).
        \\
    );
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(clap.Help, &params, .{
        .PATH = clap.parsers.string,
        .JOBS = clap.parsers.int(u16, 10),
    }, iterator, .{ .allocator = init.gpa, .diagnostic = &diagnostic }) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();
    if (result.args.help != 0) {
        try std.Io.File.stdout().writeStreamingAll(
            init.io,
            "usage: oksolc install [--base-path PATH] [--jobs JOBS]\n\n" ++
                "Use system Git to install submodules selected by remappings.txt, including\n" ++
                "nested dependencies, at the commits recorded by the project. Without\n" ++
                "remappings.txt, install all submodules declared in .gitmodules.\n\n",
        );
        return clap.helpToFile(init.io, .stdout(), clap.Help, &params, .{});
    }
    const jobs = result.args.jobs orelse 4;
    if (jobs == 0) return error.InvalidJobs;
    if (result.args.@"base-path") |path| if (path.len == 0) return error.InvalidBasePath;
    const project_root = try projectRootAlloc(init, result.args.@"base-path");
    defer init.gpa.free(project_root);
    return @import("install.zig").run(init.gpa, init.io, project_root, jobs);
}

fn writeJsonLine(init: std.process.Init, value: anytype) !void {
    const encoded = try std.json.Stringify.valueAlloc(init.gpa, value, .{});
    defer init.gpa.free(encoded);
    var buffer: [4096]u8 = undefined;
    var writer = std.Io.File.stdout().writer(init.io, &buffer);
    try writer.interface.writeAll(encoded);
    try writer.interface.writeByte('\n');
    try writer.interface.flush();
}

fn versionCommand(
    init: std.process.Init,
    iterator: *std.process.Args.Iterator,
) !void {
    const params = comptime clap.parseParamsComptime(
        \\-h, --help  Display version-command help.
        \\
    );
    var diagnostic: clap.Diagnostic = .{};
    var result = clap.parseEx(
        clap.Help,
        &params,
        clap.parsers.default,
        iterator,
        .{ .allocator = init.gpa, .diagnostic = &diagnostic },
    ) catch |err| {
        try diagnostic.reportToFile(init.io, .stderr(), err);
        return err;
    };
    defer result.deinit();

    try writeVersion(init, false);
}

fn writeVersion(init: std.process.Init, solc_compatible: bool) !void {
    const version = solidity.libsolidity.@"interface/version".VersionString;
    var buffer: [256]u8 = undefined;
    var writer = std.Io.File.stdout().writer(init.io, &buffer);
    if (solc_compatible)
        try writer.interface.print(
            "oksolc, a solidity compiler commandline interface\nVersion: {s}\n",
            .{version},
        )
    else
        try writer.interface.print("oksolc {s}\n", .{version});
    try writer.interface.flush();
}

const ProjectConfig = struct {
    /// Owned by the allocator supplied to parseProjectConfig/mergeProjectConfig.
    source_path: ?[]const u8 = null,
    parallel: ?bool = null,
    jobs: ?usize = null,
    cache: ?bool = null,
    cache_max_bytes: ?u64 = null,
    cache_max_entries: ?u64 = null,
    cache_busy_timeout_ms: ?u32 = null,

    fn deinit(self: ProjectConfig, allocator: std.mem.Allocator) void {
        if (self.source_path) |path| allocator.free(path);
    }
};

const CachePolicy = struct {
    enabled: bool,
    authentication_key: ?solidity.incremental.CacheAuthenticationKey,
    limits: solidity.incremental.CacheLimits,
    busy_timeout_ms: u32,
};

const ParallelOptions = struct {
    allocator: std.mem.Allocator,
    project_root: []u8,
    security_root: []u8,
    enabled: bool,
    jobs: ?usize,
    cache: CachePolicy,
    source_path: []const u8,

    fn deinit(self: *ParallelOptions) void {
        self.allocator.free(self.project_root);
        self.allocator.free(self.security_root);
        self.allocator.free(self.source_path);
        self.* = undefined;
    }
};

fn resolveParallelOptions(
    init: std.process.Init,
    base_path: ?[]const u8,
    cli_parallel: bool,
    cli_jobs: ?usize,
    cli_no_cache: bool,
) !ParallelOptions {
    const project_root = try projectRootAlloc(init, base_path);
    errdefer init.gpa.free(project_root);
    const security_root = try securityRootAlloc(init.gpa, init.io, project_root);
    errdefer init.gpa.free(security_root);
    const config = try loadProjectConfig(init, project_root, security_root);
    defer config.deinit(init.gpa);
    const enabled = cli_parallel or (config.parallel orelse false);
    const jobs = cli_jobs orelse config.jobs;
    if (!enabled and jobs != null) return error.JobsRequireParallel;
    if (jobs) |count| if (count == 0) return error.InvalidJobCount;
    const default_store_options: solidity.incremental.SqliteStoreOptions = .{};
    const cache_requested = persistentCacheEnabled(config, cli_no_cache);
    const authentication_key = if (cache_requested)
        loadOrCreateCacheAuthenticationKey(init, security_root) catch |err| switch (err) {
            error.OutOfMemory, error.InvalidCacheAuthenticationKey => return err,
            else => null,
        }
    else
        null;
    const source_path = try init.gpa.dupe(u8, config.source_path orelse "src");
    errdefer init.gpa.free(source_path);
    return .{
        .allocator = init.gpa,
        .project_root = project_root,
        .security_root = security_root,
        .enabled = enabled,
        .jobs = jobs,
        .source_path = source_path,
        .cache = .{
            .enabled = cache_requested and authentication_key != null,
            .authentication_key = authentication_key,
            .limits = .{
                .max_entries = config.cache_max_entries orelse
                    default_store_options.limits.max_entries,
                .max_bytes = config.cache_max_bytes orelse
                    default_store_options.limits.max_bytes,
            },
            .busy_timeout_ms = config.cache_busy_timeout_ms orelse
                default_store_options.busy_timeout_ms,
        },
    };
}

fn loadProjectConfig(
    init: std.process.Init,
    project_root: []const u8,
    security_root: []const u8,
) !ProjectConfig {
    var config: ProjectConfig = .{};
    errdefer config.deinit(init.gpa);
    const user_config_path = try userConfigPathAlloc(init);
    defer if (user_config_path) |path| init.gpa.free(path);
    if (user_config_path) |path| {
        if (try loadConfigFile(init, path)) |user_config| {
            defer user_config.deinit(init.gpa);
            const canonical_path = try std.Io.Dir.cwd().realPathFileAlloc(
                init.io,
                path,
                init.gpa,
            );
            defer init.gpa.free(canonical_path);
            const merged = try mergeProjectConfig(
                init.gpa,
                config,
                if (pathContainedBy(security_root, canonical_path))
                    restrictProjectCacheOptIn(user_config)
                else
                    user_config,
            );
            config.deinit(init.gpa);
            config = merged;
        }
    }

    const project_config_path = try std.Io.Dir.path.join(
        init.gpa,
        &.{ project_root, project_config_filename },
    );
    defer init.gpa.free(project_config_path);
    if (try loadConfigFile(init, project_config_path)) |overrides| {
        defer overrides.deinit(init.gpa);
        const merged = try mergeProjectConfig(init.gpa, config, restrictProjectCacheOptIn(overrides));
        config.deinit(init.gpa);
        config = merged;
    }
    return config;
}

/// Project-controlled configuration may disable a user-authorized cache, but
/// cannot opt into persistence on its own. The opt-in trust decision belongs
/// to the user configuration stored outside the repository.
fn restrictProjectCacheOptIn(project: ProjectConfig) ProjectConfig {
    var restricted = project;
    if (restricted.cache == true) restricted.cache = null;
    return restricted;
}

fn loadConfigFile(
    init: std.process.Init,
    path: []const u8,
) !?ProjectConfig {
    const contents = std.Io.Dir.cwd().readFileAlloc(
        init.io,
        path,
        init.gpa,
        .limited(max_project_config_bytes),
    ) catch |err| switch (err) {
        error.FileNotFound => return null,
        else => return err,
    };
    defer init.gpa.free(contents);
    return @as(?ProjectConfig, try parseProjectConfig(init.gpa, contents));
}

fn mergeProjectConfig(
    allocator: std.mem.Allocator,
    defaults: ProjectConfig,
    overrides: ProjectConfig,
) !ProjectConfig {
    var result: ProjectConfig = .{
        .source_path = if (overrides.source_path orelse defaults.source_path) |path| try allocator.dupe(u8, path) else null,
        .parallel = overrides.parallel orelse defaults.parallel,
        .jobs = overrides.jobs orelse defaults.jobs,
        .cache = overrides.cache orelse defaults.cache,
        .cache_max_bytes = overrides.cache_max_bytes orelse defaults.cache_max_bytes,
        .cache_max_entries = overrides.cache_max_entries orelse defaults.cache_max_entries,
        .cache_busy_timeout_ms = overrides.cache_busy_timeout_ms orelse
            defaults.cache_busy_timeout_ms,
    };
    errdefer result.deinit(allocator);
    return result;
}

fn parseProjectConfig(
    allocator: std.mem.Allocator,
    contents: []const u8,
) !ProjectConfig {
    var parser = toml.Parser(toml.Table).init(allocator);
    defer parser.deinit();
    var parsed = parser.parseString(contents) catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        else => return error.InvalidProjectConfig,
    };
    defer parsed.deinit();

    var config: ProjectConfig = .{};
    errdefer config.deinit(allocator);
    var entries = parsed.value.iterator();
    while (entries.next()) |entry| {
        const key = entry.key_ptr.*;
        const value = entry.value_ptr;
        if (std.mem.eql(u8, key, "source-path")) {
            if (value.* != .string) return error.InvalidProjectConfig;
            try ProjectSources.validatePath(value.string);
            config.source_path = try allocator.dupe(u8, value.string);
        } else if (std.mem.eql(u8, key, "parallel")) {
            config.parallel = tomlBoolean(value) orelse
                return error.InvalidProjectConfig;
        } else if (std.mem.eql(u8, key, "jobs")) {
            config.jobs = tomlUnsigned(usize, value) orelse
                return error.InvalidProjectConfig;
            if (config.jobs.? == 0) return error.InvalidJobCount;
        } else if (std.mem.eql(u8, key, "cache")) {
            config.cache = tomlBoolean(value) orelse
                return error.InvalidProjectConfig;
        } else if (std.mem.eql(u8, key, "cache-max-bytes")) {
            config.cache_max_bytes = tomlByteSize(value) catch
                return error.InvalidProjectConfig;
        } else if (std.mem.eql(u8, key, "cache-max-entries")) {
            config.cache_max_entries = tomlUnsigned(u64, value) orelse
                return error.InvalidProjectConfig;
        } else if (std.mem.eql(u8, key, "cache-busy-timeout-ms")) {
            config.cache_busy_timeout_ms = tomlUnsigned(u32, value) orelse
                return error.InvalidProjectConfig;
            if (config.cache_busy_timeout_ms.? > std.math.maxInt(i32))
                return error.InvalidProjectConfig;
        } else {
            return error.UnknownProjectConfigKey;
        }
    }
    return config;
}

fn persistentCacheEnabled(config: ProjectConfig, cli_no_cache: bool) bool {
    return !cli_no_cache and (config.cache orelse false);
}

fn tomlBoolean(value: *const toml.Value) ?bool {
    return switch (value.*) {
        .boolean => |boolean| boolean,
        else => null,
    };
}

fn tomlUnsigned(comptime T: type, value: *const toml.Value) ?T {
    return switch (value.*) {
        .integer => |integer| std.math.cast(T, integer),
        else => null,
    };
}

fn tomlByteSize(value: *const toml.Value) !u64 {
    return switch (value.*) {
        .integer => |integer| std.math.cast(u64, integer) orelse
            error.InvalidByteSize,
        .string => |string| parseByteSize(string),
        else => error.InvalidByteSize,
    };
}

fn parseByteSize(value: []const u8) !u64 {
    const suffixes = [_]struct { name: []const u8, multiplier: u64 }{
        .{ .name = "GiB", .multiplier = 1024 * 1024 * 1024 },
        .{ .name = "MiB", .multiplier = 1024 * 1024 },
        .{ .name = "KiB", .multiplier = 1024 },
        .{ .name = "B", .multiplier = 1 },
    };
    for (suffixes) |suffix| {
        if (!std.mem.endsWith(u8, value, suffix.name)) continue;
        const digits = value[0 .. value.len - suffix.name.len];
        if (digits.len == 0) return error.InvalidByteSize;
        const count = try std.fmt.parseUnsigned(u64, digits, 10);
        return try std.math.mul(u64, count, suffix.multiplier);
    }
    return std.fmt.parseUnsigned(u64, value, 10);
}

const CompileInput = @import("input.zig");

const WorkflowSession = union(enum) {
    memory: solidity.CompilerSession,
    sqlite: solidity.SqliteCompilerSession,

    fn init(
        process_init: std.process.Init,
        project_root: []const u8,
        security_root: []const u8,
        cache_policy: CachePolicy,
    ) !WorkflowSession {
        if (!cache_policy.enabled)
            return .{ .memory = solidity.CompilerSession.init(process_init.gpa) };
        const authentication_key = cache_policy.authentication_key orelse
            return error.CacheAuthenticationUnavailable;
        const compiler_fingerprint = solidity.incremental.CompilerFingerprint.current();
        if (!compiler_fingerprint.isPersistentSafe())
            return .{ .memory = solidity.CompilerSession.init(process_init.gpa) };
        const cache_path = artifactCachePathAlloc(
            process_init,
            project_root,
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => return .{
                .memory = solidity.CompilerSession.init(process_init.gpa),
            },
        };
        defer process_init.gpa.free(cache_path);
        if (pathContainedBy(security_root, cache_path))
            return .{ .memory = solidity.CompilerSession.init(process_init.gpa) };
        const trusted_directory = prepareTrustedArtifactCacheDirectory(
            process_init.gpa,
            process_init.io,
            cache_path,
            security_root,
        ) catch |err| switch (err) {
            error.OutOfMemory => return err,
            else => false,
        };
        if (!trusted_directory)
            return .{ .memory = solidity.CompilerSession.init(process_init.gpa) };
        return .{ .sqlite = solidity.SqliteCompilerSession.initWithOptions(
            process_init.gpa,
            process_init.io,
            cache_path,
            compiler_fingerprint,
            authentication_key,
            .{ .store = .{
                .limits = cache_policy.limits,
                .busy_timeout_ms = cache_policy.busy_timeout_ms,
            } },
        ) };
    }

    fn deinit(self: *WorkflowSession) void {
        switch (self.*) {
            .memory => |*session| session.deinit(),
            .sqlite => |*session| session.deinit(),
        }
        self.* = undefined;
    }

    fn compiler(self: *WorkflowSession) solidity.standard_json.Compiler {
        return switch (self.*) {
            .memory => |*session| session.compiler(),
            .sqlite => |*session| session.compiler(),
        };
    }

    fn setOptimizerProfiler(self: *WorkflowSession, profiler: ?*Profiler) void {
        switch (self.*) {
            .memory => |*session| session.setOptimizerProfiler(profiler),
            .sqlite => |*session| session.setOptimizerProfiler(profiler),
        }
    }
};

const WatchStamp = struct {
    inode: std.Io.File.INode,
    size: u64,
    modified_nanoseconds: i96,
    changed_nanoseconds: i96,

    fn eql(self: WatchStamp, other: WatchStamp) bool {
        return self.inode == other.inode and
            self.size == other.size and
            self.modified_nanoseconds == other.modified_nanoseconds and
            self.changed_nanoseconds == other.changed_nanoseconds;
    }
};

fn watchStamp(io: std.Io, path: []const u8) !?WatchStamp {
    const stat = std.Io.Dir.cwd().statFile(io, path, .{}) catch |err| switch (err) {
        error.FileNotFound => return null,
        else => return err,
    };
    if (stat.kind != .file) return error.NotAFile;
    return .{
        .inode = stat.inode,
        .size = stat.size,
        .modified_nanoseconds = stat.mtime.nanoseconds,
        .changed_nanoseconds = stat.ctime.nanoseconds,
    };
}

fn readServeFrameAlloc(
    reader: *std.Io.Reader,
    allocator: std.mem.Allocator,
) !?[]u8 {
    var content_length: ?usize = null;
    var header_bytes: usize = 0;
    var saw_header = false;
    while (true) {
        const raw_line = (try reader.takeDelimiter('\n')) orelse {
            if (!saw_header) return null;
            return error.IncompleteFrameHeader;
        };
        saw_header = true;
        const encoded_line_length = std.math.add(usize, raw_line.len, 1) catch
            return error.FrameHeaderTooLarge;
        if (encoded_line_length > max_serve_header_bytes -| header_bytes)
            return error.FrameHeaderTooLarge;
        header_bytes += encoded_line_length;
        const line = std.mem.trimEnd(u8, raw_line, "\r");
        if (line.len == 0) break;

        const delimiter = std.mem.findScalar(u8, line, ':') orelse
            return error.InvalidFrameHeader;
        const name = std.mem.trim(u8, line[0..delimiter], " \t");
        const value = std.mem.trim(u8, line[delimiter + 1 ..], " \t");
        if (!std.ascii.eqlIgnoreCase(name, "Content-Length")) continue;
        if (content_length != null) return error.DuplicateContentLength;
        content_length = std.fmt.parseUnsigned(usize, value, 10) catch
            return error.InvalidContentLength;
        if (content_length.? > max_input_bytes) return error.InputTooLarge;
    }

    const length = content_length orelse return error.MissingContentLength;
    return try reader.readAlloc(allocator, length);
}

fn writeServeFrame(writer: *std.Io.Writer, bytes: []const u8) !void {
    try writer.print("Content-Length: {d}\r\n\r\n", .{bytes.len});
    try writer.writeAll(bytes);
}

fn compileAndWrite(
    init: std.process.Init,
    input: []const u8,
    output_path: ?[]const u8,
    profile_path: ?[]const u8,
    show_progress: bool,
    parallel: bool,
    requested_jobs: ?usize,
    project_root: []const u8,
    security_root: []const u8,
    cache_policy: CachePolicy,
    source_paths: SourcePathConfiguration,
) !void {
    if (profile_path) |path| {
        if (std.mem.eql(u8, path, "-")) return error.InvalidProfilePath;
        if (output_path) |output|
            if (std.mem.eql(u8, path, output)) return error.DuplicateOutputPath;
    }
    if (!parallel and requested_jobs != null) return error.JobsRequireParallel;
    const parallel_jobs = if (parallel)
        requested_jobs orelse defaultParallelJobs()
    else
        1;
    if (parallel_jobs == 0) return error.InvalidJobCount;

    var parallel_backend: std.Io.Threaded = undefined;
    const compiler_io: ?std.Io = if (parallel) io: {
        parallel_backend = .init(std.heap.smp_allocator, .{
            .async_limit = .limited(parallel_jobs - 1),
        });
        break :io parallel_backend.io();
    } else null;
    defer if (parallel) parallel_backend.deinit();

    var progress = CliProgress.init(init.io, show_progress);
    defer progress.deinit();
    var loader_state = try FileSourceLoader.init(init.gpa, init.io, source_paths);
    defer loader_state.deinit();
    var profiler = Profiler.init(init.gpa, init.io);
    defer profiler.deinit();
    var session = try WorkflowSession.init(
        init,
        project_root,
        security_root,
        cache_policy,
    );
    defer session.deinit();
    session.setOptimizerProfiler(if (profile_path != null) &profiler else null);
    var output = try session.compiler().compile(init.gpa, .{
        .input = input,
        .io = compiler_io,
        .source_loader = loader_state.interface(),
        .progress = progress.reporter(),
    });
    defer output.deinit();
    if (output_path == null or std.mem.eql(u8, output_path.?, "-"))
        progress.finish()
    else
        progress.report(.{
            .stage = .writing_output,
            .item_name = output_path.?,
        });
    try writeOutput(init.io, output_path, output.bytes);
    if (profile_path) |path| {
        const report = try profiler.reportJsonAlloc(init.gpa);
        defer init.gpa.free(report);
        try writeOutput(init.io, path, report);
    }
}

fn userConfigPathAlloc(init: std.process.Init) !?[]u8 {
    return xdgApplicationPathAlloc(
        init.gpa,
        init.environ_map.get("XDG_CONFIG_HOME"),
        init.environ_map.get("HOME"),
        ".config",
        user_config_filename,
    );
}

fn cacheAuthenticationKeyPathAlloc(init: std.process.Init) !?[]u8 {
    return xdgApplicationPathAlloc(
        init.gpa,
        init.environ_map.get("XDG_CONFIG_HOME"),
        init.environ_map.get("HOME"),
        ".config",
        cache_authentication_key_filename,
    );
}

const secure_key_permissions = if (@hasDecl(std.Io.File.Permissions, "fromMode"))
    std.Io.File.Permissions.fromMode(0o600)
else
    std.Io.File.Permissions.default_file;

fn loadOrCreateCacheAuthenticationKey(
    init: std.process.Init,
    security_root: []const u8,
) !solidity.incremental.CacheAuthenticationKey {
    if (init.environ_map.get(cache_authentication_key_environment)) |encoded|
        return parseCacheAuthenticationKey(encoded);

    const path = (try cacheAuthenticationKeyPathAlloc(init)) orelse
        return error.CacheAuthenticationUnavailable;
    defer init.gpa.free(path);
    const directory_path = std.Io.Dir.path.dirname(path) orelse
        return error.CacheAuthenticationUnavailable;
    var directory = try std.Io.Dir.cwd().createDirPathOpen(
        init.io,
        directory_path,
        .{
            .open_options = .{
                .iterate = false,
                .follow_symlinks = false,
            },
            .permissions = secure_directory_permissions,
        },
    );
    defer directory.close(init.io);
    try directory.setPermissions(init.io, secure_directory_permissions);

    const canonical_directory = try std.Io.Dir.cwd().realPathFileAlloc(
        init.io,
        directory_path,
        init.gpa,
    );
    defer init.gpa.free(canonical_directory);
    if (pathContainedBy(security_root, canonical_directory))
        return error.CacheAuthenticationKeyInsideProject;

    const filename = std.Io.Dir.path.basename(path);
    var generated: solidity.incremental.CacheAuthenticationKey = undefined;
    try std.Io.randomSecure(init.io, &generated);
    var created = directory.createFile(init.io, filename, .{
        .read = true,
        .truncate = false,
        .exclusive = true,
        .permissions = secure_key_permissions,
    }) catch |err| switch (err) {
        error.PathAlreadyExists => null,
        else => return err,
    };
    if (created) |*file| {
        defer file.close(init.io);
        try file.setPermissions(init.io, secure_key_permissions);
        try file.writeStreamingAll(init.io, &generated);
        try file.sync(init.io);
        return generated;
    }

    var existing = try directory.openFile(init.io, filename, .{
        .mode = .read_only,
        .allow_directory = false,
        .follow_symlinks = false,
    });
    defer existing.close(init.io);
    const stat = try existing.stat(init.io);
    if (stat.kind != .file) return error.InvalidCacheAuthenticationKeyFile;
    try existing.setPermissions(init.io, secure_key_permissions);
    var stored: [@sizeOf(solidity.incremental.CacheAuthenticationKey) + 1]u8 = undefined;
    const count = try existing.readPositionalAll(init.io, &stored, 0);
    if (count != @sizeOf(solidity.incremental.CacheAuthenticationKey))
        return error.InvalidCacheAuthenticationKeyFile;
    var result: solidity.incremental.CacheAuthenticationKey = undefined;
    @memcpy(&result, stored[0..result.len]);
    return result;
}

fn parseCacheAuthenticationKey(
    encoded: []const u8,
) !solidity.incremental.CacheAuthenticationKey {
    if (encoded.len != @sizeOf(solidity.incremental.CacheAuthenticationKey) * 2)
        return error.InvalidCacheAuthenticationKey;
    var result: solidity.incremental.CacheAuthenticationKey = undefined;
    _ = std.fmt.hexToBytes(&result, encoded) catch
        return error.InvalidCacheAuthenticationKey;
    return result;
}

const pathContainedBy = ProjectSources.pathContainedBy;

fn projectRootAlloc(
    init: std.process.Init,
    explicit_base_path: ?[]const u8,
) ![]u8 {
    if (explicit_base_path) |path| {
        if (path.len != 0) return canonicalDirectoryAlloc(init, path);
    }

    const current = try canonicalDirectoryAlloc(init, ".");
    defer init.gpa.free(current);
    return findProjectRootAlloc(init.gpa, init.io, current);
}

fn findProjectRootAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    start: []const u8,
) ![]u8 {
    var candidate: []const u8 = start;
    while (true) {
        if (try childPathExists(allocator, io, candidate, project_config_filename) or
            try childPathExists(allocator, io, candidate, repository_marker))
        {
            return allocator.dupe(u8, candidate);
        }
        const parent = std.Io.Dir.path.dirname(candidate) orelse break;
        if (std.mem.eql(u8, parent, candidate)) break;
        candidate = parent;
    }
    return allocator.dupe(u8, start);
}

/// Cache trust follows the complete enclosing worktree, independently of the
/// narrower directory selected as the compilation project. Choosing an
/// explicit base path or a nested oksolc.toml must not make repository-owned
/// configuration, keys, or databases appear external.
fn securityRootAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    project_root: []const u8,
) ![]u8 {
    var candidate: []const u8 = project_root;
    while (true) {
        if (try childPathExists(allocator, io, candidate, repository_marker))
            return allocator.dupe(u8, candidate);
        const parent = std.Io.Dir.path.dirname(candidate) orelse break;
        if (std.mem.eql(u8, parent, candidate)) break;
        candidate = parent;
    }
    return allocator.dupe(u8, project_root);
}

fn canonicalDirectoryAlloc(init: std.process.Init, path: []const u8) ![]u8 {
    const canonical = try std.Io.Dir.cwd().realPathFileAlloc(
        init.io,
        path,
        init.gpa,
    );
    defer init.gpa.free(canonical);
    const stat = try std.Io.Dir.cwd().statFile(init.io, canonical, .{});
    if (stat.kind != .directory) return error.NotDir;
    return init.gpa.dupe(u8, canonical);
}

fn childPathExists(
    allocator: std.mem.Allocator,
    io: std.Io,
    parent: []const u8,
    child: []const u8,
) !bool {
    const path = try std.Io.Dir.path.join(allocator, &.{ parent, child });
    defer allocator.free(path);
    _ = std.Io.Dir.cwd().statFile(
        io,
        path,
        .{ .follow_symlinks = false },
    ) catch |err| switch (err) {
        error.FileNotFound => return false,
        else => return err,
    };
    return true;
}

fn deleteCacheDirectory(
    init: std.process.Init,
    cache_path: []const u8,
    security_root: []const u8,
) !bool {
    const stat = std.Io.Dir.cwd().statFile(
        init.io,
        cache_path,
        .{ .follow_symlinks = false },
    ) catch |err| switch (err) {
        error.FileNotFound => return false,
        else => return err,
    };
    if (stat.kind != .directory) return error.CachePathNotDirectory;
    const canonical_path = try std.Io.Dir.cwd().realPathFileAlloc(
        init.io,
        cache_path,
        init.gpa,
    );
    defer init.gpa.free(canonical_path);
    if (!std.mem.eql(u8, cache_path, canonical_path))
        return error.CachePathAlias;
    if (pathContainedBy(security_root, canonical_path))
        return error.CacheDirectoryInsideProject;

    const parent_path = std.Io.Dir.path.dirname(canonical_path) orelse
        return error.CacheLocationUnavailable;
    var parent = try std.Io.Dir.cwd().openDir(init.io, parent_path, .{
        .iterate = true,
        .follow_symlinks = false,
    });
    defer parent.close(init.io);
    try parent.deleteTree(init.io, std.Io.Dir.path.basename(canonical_path));
    return true;
}

fn userCacheProjectsPathAlloc(init: std.process.Init) !?[]u8 {
    return xdgApplicationPathAlloc(
        init.gpa,
        init.environ_map.get("XDG_CACHE_HOME"),
        init.environ_map.get("HOME"),
        ".cache",
        cache_projects_directory,
    );
}

fn artifactCacheDirectoryUnderRootAlloc(
    allocator: std.mem.Allocator,
    cache_projects_root: []const u8,
    project_root: []const u8,
) ![]u8 {
    var digest: [std.crypto.hash.sha2.Sha256.digest_length]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(project_root, &digest, .{});
    const digest_hex = std.fmt.bytesToHex(digest, .lower);
    return std.Io.Dir.path.join(
        allocator,
        &.{ cache_projects_root, &digest_hex },
    );
}

fn artifactCacheDirectoryPathAlloc(
    init: std.process.Init,
    project_root: []const u8,
) ![]u8 {
    const raw_root = (try userCacheProjectsPathAlloc(init)) orelse
        return error.CacheLocationUnavailable;
    defer init.gpa.free(raw_root);
    const cache_projects_root = try std.Io.Dir.path.resolve(init.gpa, &.{raw_root});
    defer init.gpa.free(cache_projects_root);
    return artifactCacheDirectoryUnderRootAlloc(
        init.gpa,
        cache_projects_root,
        project_root,
    );
}

fn artifactCachePathAlloc(
    init: std.process.Init,
    project_root: []const u8,
) ![]u8 {
    const directory = try artifactCacheDirectoryPathAlloc(init, project_root);
    defer init.gpa.free(directory);
    return std.Io.Dir.path.join(
        init.gpa,
        &.{ directory, artifact_cache_database },
    );
}

fn xdgApplicationPathAlloc(
    allocator: std.mem.Allocator,
    xdg_home: ?[]const u8,
    home: ?[]const u8,
    default_home_component: []const u8,
    filename: []const u8,
) !?[]u8 {
    if (xdg_home) |path| {
        if (path.len != 0 and std.Io.Dir.path.isAbsolute(path))
            return try std.Io.Dir.path.join(allocator, &.{
                path,
                application_directory,
                filename,
            });
    }
    if (home) |path| {
        if (path.len != 0 and std.Io.Dir.path.isAbsolute(path))
            return try std.Io.Dir.path.join(allocator, &.{
                path,
                default_home_component,
                application_directory,
                filename,
            });
    }
    return null;
}

const secure_directory_permissions = if (@hasDecl(std.Io.Dir.Permissions, "fromMode"))
    std.Io.Dir.Permissions.fromMode(0o700)
else
    std.Io.Dir.Permissions.default_dir;

fn prepareArtifactCacheDirectory(io: std.Io, database_path: []const u8) bool {
    const directory_path = std.Io.Dir.path.dirname(database_path) orelse return false;
    var directory = std.Io.Dir.cwd().createDirPathOpen(
        io,
        directory_path,
        .{
            .open_options = .{
                .iterate = true,
                .follow_symlinks = false,
            },
            .permissions = secure_directory_permissions,
        },
    ) catch return false;
    defer directory.close(io);
    directory.setPermissions(io, secure_directory_permissions) catch return false;
    return true;
}

fn prepareTrustedArtifactCacheDirectory(
    allocator: std.mem.Allocator,
    io: std.Io,
    database_path: []const u8,
    security_root: []const u8,
) !bool {
    if (!prepareArtifactCacheDirectory(io, database_path)) return false;
    const directory_path = std.Io.Dir.path.dirname(database_path) orelse
        return false;
    const canonical_directory = std.Io.Dir.cwd().realPathFileAlloc(
        io,
        directory_path,
        allocator,
    ) catch |err| switch (err) {
        error.OutOfMemory => return err,
        else => return false,
    };
    defer allocator.free(canonical_directory);
    return std.mem.eql(u8, directory_path, canonical_directory) and
        !pathContainedBy(security_root, canonical_directory);
}

fn defaultParallelJobs() usize {
    const cpu_count = std.Thread.getCpuCount() catch 1;
    return @max(@as(usize, 1), @min(cpu_count, max_default_parallel_jobs));
}

const CliProgress = struct {
    enabled: bool = false,
    root: std.Progress.Node = .none,
    active: std.Progress.Node = .none,
    active_stage: ?solidity.standard_json.ProgressStage = null,

    fn init(io: std.Io, enabled: bool) CliProgress {
        if (!enabled) return .{};
        return .{
            .enabled = true,
            .root = std.Progress.start(io, .{ .root_name = "oksolc" }),
        };
    }

    fn deinit(self: *CliProgress) void {
        self.finish();
        self.* = undefined;
    }

    fn finish(self: *CliProgress) void {
        if (!self.enabled) return;
        self.active.end();
        self.root.end();
        self.enabled = false;
        self.root = .none;
        self.active = .none;
        self.active_stage = null;
    }

    fn reporter(self: *CliProgress) ?solidity.standard_json.ProgressReporter {
        if (!self.enabled) return null;
        return .{ .context = self, .report_fn = reportOpaque };
    }

    fn reportOpaque(
        opaque_context: ?*anyopaque,
        update: solidity.standard_json.ProgressUpdate,
    ) void {
        const self: *CliProgress = @ptrCast(@alignCast(opaque_context.?));
        self.report(update);
    }

    fn report(
        self: *CliProgress,
        update: solidity.standard_json.ProgressUpdate,
    ) void {
        if (!self.enabled) return;
        const label = stageLabel(update.stage);
        if (self.active_stage != update.stage) {
            self.active.end();
            self.active = self.root.start(label, update.estimated_total_items);
            self.active_stage = update.stage;
        }

        var name_buffer: [std.Progress.Node.max_name_len]u8 = undefined;
        const name = if (update.item_name.len == 0)
            label
        else
            std.fmt.bufPrint(
                &name_buffer,
                "{s}: {s}",
                .{ label, update.item_name },
            ) catch label;
        self.active.setName(name);
        self.active.setEstimatedTotalItems(update.estimated_total_items);
        self.active.setCompletedItems(update.completed_items);
    }

    fn stageLabel(stage: solidity.standard_json.ProgressStage) []const u8 {
        return switch (stage) {
            .parsing_sources => "Parsing sources",
            .analyzing_sources => "Analyzing sources",
            .generating_contracts => "Generating contracts",
            .compiling_yul => "Compiling Yul",
            .writing_output => "Writing output",
        };
    }
};

const SourcePathConfiguration = struct {
    base_path: ?[]const u8,
    include_paths: []const []const u8 = &.{},
    allow_paths: ?[]const u8 = null,
    max_total_bytes: usize = max_total_loaded_source_bytes,
};

const FileSourceLoader = struct {
    const Root = struct {
        canonical_path: []u8,
        directory: std.Io.Dir,
        lookup: bool,
    };

    const ReadAttempt = union(enum) {
        contents: []u8,
        not_found,
        denied,
        too_large,
    };

    allocator: std.mem.Allocator,
    io: std.Io,
    roots: std.ArrayList(Root) = .empty,
    loaded_bytes: usize = 0,
    max_total_bytes: usize,

    fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        configuration: SourcePathConfiguration,
    ) !FileSourceLoader {
        var self: FileSourceLoader = .{
            .allocator = allocator,
            .io = io,
            .max_total_bytes = configuration.max_total_bytes,
        };
        errdefer self.deinit();
        if (configuration.base_path) |path| try self.addRoot(path, true);
        for (configuration.include_paths) |path| try self.addRoot(path, true);
        if (configuration.allow_paths) |paths| {
            var iterator = std.mem.splitScalar(u8, paths, ',');
            while (iterator.next()) |path| {
                if (path.len == 0) return error.InvalidAllowedPath;
                try self.addRoot(path, false);
            }
        }
        return self;
    }

    fn deinit(self: *FileSourceLoader) void {
        for (self.roots.items) |root| {
            root.directory.close(self.io);
            self.allocator.free(root.canonical_path);
        }
        self.roots.deinit(self.allocator);
        self.* = undefined;
    }

    fn reset(self: *FileSourceLoader) void {
        self.loaded_bytes = 0;
    }

    fn interface(self: *FileSourceLoader) solidity.standard_json.SourceLoader {
        return .{ .context = self, .read_fn = read };
    }

    fn addRoot(self: *FileSourceLoader, path: []const u8, lookup: bool) !void {
        if (path.len == 0) return error.InvalidSourceRoot;
        const canonical = if (std.Io.Dir.path.isAbsolute(path))
            try std.Io.Dir.path.resolve(self.allocator, &.{path})
        else canonical: {
            const current_directory = try std.Io.Dir.cwd().realPathFileAlloc(
                self.io,
                ".",
                self.allocator,
            );
            defer self.allocator.free(current_directory);
            break :canonical try std.Io.Dir.path.resolve(
                self.allocator,
                &.{ current_directory, path },
            );
        };
        errdefer self.allocator.free(canonical);
        for (self.roots.items) |*root| {
            if (!std.mem.eql(u8, root.canonical_path, canonical)) continue;
            root.lookup = root.lookup or lookup;
            self.allocator.free(canonical);
            return;
        }
        if (self.roots.items.len >= max_source_roots)
            return error.TooManySourceRoots;
        var directory = try self.openCanonicalDirectory(canonical, false);
        errdefer directory.close(self.io);
        try self.roots.append(self.allocator, .{
            .canonical_path = canonical,
            .directory = directory,
            .lookup = lookup,
        });
    }

    fn read(
        opaque_context: ?*anyopaque,
        allocator: std.mem.Allocator,
        kind: []const u8,
        path: []const u8,
    ) solidity.standard_json.SourceReadError!solidity.standard_json.SourceReadResult {
        const self: *FileSourceLoader = @ptrCast(@alignCast(opaque_context orelse
            return error.InternalFailure));
        if (!std.mem.eql(u8, kind, "source")) return .unsupported;
        return switch (try self.readPathAlloc(allocator, path)) {
            .contents => |contents| .{ .contents = contents },
            .not_found => .{ .failure = try allocator.dupe(
                u8,
                "Source file not found in configured roots.",
            ) },
            .denied => .{ .failure = try allocator.dupe(
                u8,
                "Source path is outside configured roots or is not a regular file.",
            ) },
            .too_large => .{ .failure = try allocator.dupe(
                u8,
                "Total loaded source byte limit exceeded.",
            ) },
        };
    }

    fn readPathAlloc(
        self: *FileSourceLoader,
        allocator: std.mem.Allocator,
        raw_path: []const u8,
    ) error{OutOfMemory}!ReadAttempt {
        const path = if (std.mem.startsWith(u8, raw_path, "file://"))
            raw_path["file://".len..]
        else
            raw_path;
        if (path.len == 0 or path.len > max_source_path_bytes) return .denied;

        if (std.Io.Dir.path.isAbsolute(path)) {
            const candidate = try std.Io.Dir.path.resolve(allocator, &.{path});
            defer allocator.free(candidate);
            return self.readAuthorizedCandidateAlloc(allocator, candidate);
        }

        for (self.roots.items) |*lookup_root| {
            if (!lookup_root.lookup) continue;
            const candidate = try std.Io.Dir.path.resolve(
                allocator,
                &.{ lookup_root.canonical_path, path },
            );
            defer allocator.free(candidate);
            switch (try self.readAuthorizedCandidateAlloc(allocator, candidate)) {
                .not_found => continue,
                else => |attempt| return attempt,
            }
        }
        return .not_found;
    }

    fn readAuthorizedCandidateAlloc(
        self: *FileSourceLoader,
        allocator: std.mem.Allocator,
        candidate: []const u8,
    ) error{OutOfMemory}!ReadAttempt {
        for (self.roots.items) |*root| {
            if (!pathContainedBy(root.canonical_path, candidate)) continue;
            return self.readCandidateAlloc(allocator, root, candidate);
        }
        return .denied;
    }

    fn readCandidateAlloc(
        self: *FileSourceLoader,
        allocator: std.mem.Allocator,
        root: *const Root,
        candidate: []const u8,
    ) error{OutOfMemory}!ReadAttempt {
        if (!pathContainedBy(root.canonical_path, candidate)) return .denied;
        var relative = candidate[root.canonical_path.len..];
        while (relative.len != 0 and std.Io.Dir.path.isSep(relative[0]))
            relative = relative[1..];
        if (relative.len == 0) return .denied;
        return self.readRelativeFileAlloc(allocator, root, relative);
    }

    fn readRelativeFileAlloc(
        self: *FileSourceLoader,
        allocator: std.mem.Allocator,
        root: *const Root,
        relative: []const u8,
    ) error{OutOfMemory}!ReadAttempt {
        var owned_parent: ?std.Io.Dir = null;
        defer if (owned_parent) |directory| directory.close(self.io);
        var component_start: usize = 0;
        var index: usize = 0;
        while (index <= relative.len) : (index += 1) {
            if (index != relative.len and !std.Io.Dir.path.isSep(relative[index]))
                continue;
            const component = relative[component_start..index];
            if (component.len == 0 or
                std.mem.eql(u8, component, ".") or
                std.mem.eql(u8, component, ".."))
            {
                return .denied;
            }
            const parent = owned_parent orelse root.directory;
            if (index == relative.len) {
                const path_stat = parent.statFile(self.io, component, .{
                    .follow_symlinks = false,
                }) catch |err| switch (err) {
                    error.FileNotFound => return .not_found,
                    else => return .denied,
                };
                if (path_stat.kind != .file) return .denied;
                var file = openSourceFileNonblocking(parent, self.io, component) catch |err| switch (err) {
                    error.FileNotFound => return .not_found,
                    else => return .denied,
                };
                defer file.close(self.io);
                const stat = file.stat(self.io) catch return .denied;
                if (stat.kind != .file or stat.inode != path_stat.inode)
                    return .denied;
                const size = std.math.cast(usize, stat.size) orelse
                    return .too_large;
                const remaining = self.max_total_bytes -| self.loaded_bytes;
                if (size > max_source_bytes or size > remaining)
                    return .too_large;
                var buffer: [16 * 1024]u8 = undefined;
                var reader = file.reader(self.io, &buffer);
                const contents = reader.interface.allocRemaining(
                    allocator,
                    .limited(@min(max_source_bytes, remaining)),
                ) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.StreamTooLong => return .too_large,
                    else => return .denied,
                };
                self.loaded_bytes = std.math.add(
                    usize,
                    self.loaded_bytes,
                    contents.len,
                ) catch {
                    allocator.free(contents);
                    return .too_large;
                };
                return .{ .contents = contents };
            }

            const next = parent.openDir(self.io, component, .{
                .iterate = false,
                .follow_symlinks = false,
            }) catch |err| switch (err) {
                error.FileNotFound => return .not_found,
                else => return .denied,
            };
            if (owned_parent) |directory| directory.close(self.io);
            owned_parent = next;
            component_start = index + 1;
        }
        unreachable;
    }

    fn openCanonicalDirectory(
        self: *FileSourceLoader,
        canonical: []const u8,
        iterate: bool,
    ) !std.Io.Dir {
        const parsed = std.Io.Dir.path.parsePath(canonical);
        if (parsed.root.len == 0) return error.SourceRootNotAbsolute;
        var current = try std.Io.Dir.cwd().openDir(self.io, parsed.root, .{
            .iterate = iterate,
            .follow_symlinks = false,
        });
        errdefer current.close(self.io);

        var component_start = parsed.root.len;
        while (component_start < canonical.len and
            std.Io.Dir.path.isSep(canonical[component_start]))
        {
            component_start += 1;
        }
        var index = component_start;
        while (index <= canonical.len) : (index += 1) {
            if (index != canonical.len and
                !std.Io.Dir.path.isSep(canonical[index]))
            {
                continue;
            }
            const component = canonical[component_start..index];
            if (component.len == 0) break;
            const next = try current.openDir(self.io, component, .{
                .iterate = iterate,
                .follow_symlinks = false,
            });
            current.close(self.io);
            current = next;
            component_start = index + 1;
        }

        var actual_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
        const actual_length = try current.realPath(self.io, &actual_buffer);
        if (!std.mem.eql(u8, canonical, actual_buffer[0..actual_length]))
            return error.SourceRootChanged;
        return current;
    }
};

fn validateSourcePathArguments(
    base_path: ?[]const u8,
    include_paths: []const []const u8,
) !void {
    if (base_path) |path| if (path.len == 0) return error.InvalidBasePath;
    if (include_paths.len != 0 and base_path == null)
        return error.IncludePathRequiresBasePath;
    for (include_paths) |path|
        if (path.len == 0) return error.InvalidIncludePath;
}

fn openSourceFileNonblocking(
    parent: std.Io.Dir,
    io: std.Io,
    component: []const u8,
) !std.Io.File {
    if (comptime builtin.os.tag == .windows or
        builtin.os.tag == .wasi or
        builtin.os.tag == .uefi)
    {
        return parent.openFile(io, component, .{
            .mode = .read_only,
            .allow_directory = false,
            .follow_symlinks = false,
        });
    }

    var flags: std.posix.O = .{
        .ACCMODE = .RDONLY,
        .NOFOLLOW = true,
    };
    if (@hasField(std.posix.O, "CLOEXEC")) flags.CLOEXEC = true;
    if (@hasField(std.posix.O, "NONBLOCK")) flags.NONBLOCK = true;
    const handle = try std.posix.openat(parent.handle, component, flags, 0);
    return .{
        .handle = handle,
        .flags = .{ .nonblocking = @hasField(std.posix.O, "NONBLOCK") },
    };
}

fn readInputAlloc(init: std.process.Init, path: ?[]const u8) ![]u8 {
    return readDocumentAlloc(init, path, max_input_bytes);
}

fn readDocumentAlloc(init: std.process.Init, path: ?[]const u8, max_bytes: usize) ![]u8 {
    if (path) |input_path| if (!std.mem.eql(u8, input_path, "-"))
        return std.Io.Dir.cwd().readFileAlloc(
            init.io,
            input_path,
            init.gpa,
            .limited(max_bytes),
        );

    var buffer: [16 * 1024]u8 = undefined;
    var reader = std.Io.File.stdin().reader(init.io, &buffer);
    return reader.interface.allocRemaining(init.gpa, .limited(max_bytes));
}

fn writeOutput(io: std.Io, path: ?[]const u8, bytes: []const u8) !void {
    if (path == null or std.mem.eql(u8, path.?, "-"))
        return std.Io.File.stdout().writeStreamingAll(io, bytes);

    var output = try std.Io.Dir.cwd().createFileAtomic(io, path.?, .{
        .make_path = true,
        .replace = true,
    });
    defer output.deinit(io);
    try output.file.writeStreamingAll(io, bytes);
    try output.replace(io);
}

fn writeMainHelp(io: std.Io) !void {
    try std.Io.File.stdout().writeStreamingAll(io,
        \\oksolc — A Solidity compiler
        \\project: https://github.com/okcontract/solidity-zig
        \\
        \\usage:
        \\  oksolc --standard-json [--base-path PATH] [--include-path PATH]... [--allow-paths PATHS] [--no-cache]
        \\  oksolc browse [--request FILE | SOURCE...] [--import-output FILE] [--database FILE] [--port 8080]
        \\  oksolc compile [-o FILE] [--parallel [-j JOBS]] [--no-cache] [--progress] [--profile-optimizer FILE] <SOURCE>...
        \\  oksolc standard-json [-o FILE] [--base-path PATH] [--include-path PATH]... [--allow-paths PATHS] [--parallel [-j JOBS]] [--no-cache] [--progress] [--profile-optimizer FILE] [INPUT]
        \\  oksolc serve [--browse | --stdio] [--source-path PATH] [--base-path PATH] [--include-path PATH]... [--allow-paths PATHS] [--parallel [-j JOBS]] [--no-cache]
        \\  oksolc watch [-o FILE] [--base-path PATH] [--include-path PATH]... [--allow-paths PATHS] [--parallel [-j JOBS]] [--no-cache] [--poll-ms MILLISECONDS] [--once] INPUT
        \\  oksolc cache stats
        \\  oksolc cache prune [--max-bytes SIZE] [--max-entries ENTRIES]
        \\  oksolc install [--base-path PATH] [--jobs JOBS]
        \\  oksolc clean
        \\  oksolc version
        \\
        \\`compile` always uses via-IR with optimization enabled. Use
        \\`standard-json` for explicit artifact and frontend-only requests.
        \\Source commands resolve project-relative names and remappings.txt.
        \\
    );
}

fn writeCompileHelp(io: std.Io) !void {
    try std.Io.File.stdout().writeStreamingAll(
        io,
        "usage: oksolc compile [-o FILE] [--parallel [-j JOBS]] [--no-cache] [--progress] [--profile-optimizer FILE] <SOURCE>...\n\n",
    );
    try clap.helpToFile(io, .stdout(), clap.Help, &compile_params, .{});
}

fn writeStandardJsonHelp(io: std.Io) !void {
    try std.Io.File.stdout().writeStreamingAll(
        io,
        "usage: oksolc standard-json [-o FILE] [--base-path PATH] [--include-path PATH]... " ++
            "[--allow-paths PATHS] [--parallel [-j JOBS]] [--no-cache] [--progress] " ++
            "[--profile-optimizer FILE] [INPUT]\n\n",
    );
    try clap.helpToFile(io, .stdout(), clap.Help, &standard_json_params, .{});
}

fn writeServeHelp(io: std.Io) !void {
    try std.Io.File.stdout().writeStreamingAll(
        io,
        "usage: oksolc serve [--browse | --stdio] [--source-path PATH] [--base-path PATH] [--include-path PATH]... " ++
            "[--allow-paths PATHS] [--parallel [-j JOBS]] [--no-cache]\n\n" ++
            "Watch source-path in oksolc.toml (default: src), compiling roots and used imports.\n" ++
            "Emit Standard JSON per line; --browse publishes live SQL snapshots at localhost:8080.\n" ++
            "--stdio selects Content-Length framed requests instead.\n\n",
    );
    try clap.helpToFile(io, .stdout(), clap.Help, &serve_params, .{});
}

fn writeWatchHelp(io: std.Io) !void {
    try std.Io.File.stdout().writeStreamingAll(
        io,
        "usage: oksolc watch [-o FILE] [--base-path PATH] [--include-path PATH]... " ++
            "[--allow-paths PATHS] [--parallel [-j JOBS]] " ++
            "[--no-cache] [--poll-ms MILLISECONDS] [--once] INPUT\n\n" ++
            "Watch a Standard JSON file. Without -o, each compact response is written to stdout.\n\n",
    );
    try clap.helpToFile(io, .stdout(), clap.Help, &watch_params, .{});
}

fn writeCacheHelp(io: std.Io) !void {
    try std.Io.File.stdout().writeStreamingAll(
        io,
        "usage: oksolc cache (stats|prune) [--max-bytes SIZE] " ++
            "[--max-entries ENTRIES]\n\n" ++
            "Inspect or prune the current project's external SQLite artifact cache. " ++
            "Prune defaults to configured limits.\n\n",
    );
    try clap.helpToFile(io, .stdout(), clap.Help, &cache_params, .{});
}

fn writeCleanHelp(io: std.Io) !void {
    try std.Io.File.stdout().writeStreamingAll(
        io,
        "usage: oksolc clean\n\n" ++
            "Remove the current project's generated external cache directory.\n\n",
    );
    try clap.helpToFile(io, .stdout(), clap.Help, &clean_params, .{});
}

test "filesystem source loader confines reads to canonical regular files" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "base/contracts");
    try temporary.dir.createDirPath(std.testing.io, "outside");
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "base/contracts/A.sol",
        .data = "contract A {}",
    });
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "outside/Secret.sol",
        .data = "secret",
    });
    const base_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/base",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(base_path);
    const outside_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/outside/Secret.sol",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(outside_path);
    const canonical_outside = try std.Io.Dir.cwd().realPathFileAlloc(
        std.testing.io,
        outside_path,
        std.testing.allocator,
    );
    defer std.testing.allocator.free(canonical_outside);

    var loader = try FileSourceLoader.init(
        std.testing.allocator,
        std.testing.io,
        .{ .base_path = base_path },
    );
    defer loader.deinit();

    const allowed = try loader.readPathAlloc(
        std.testing.allocator,
        "contracts/A.sol",
    );
    switch (allowed) {
        .contents => |contents| {
            defer std.testing.allocator.free(contents);
            try std.testing.expectEqualStrings("contract A {}", contents);
        },
        else => return error.UnexpectedSourceReadResult,
    }
    switch (try loader.readPathAlloc(std.testing.allocator, canonical_outside)) {
        .denied => {},
        else => return error.UnexpectedSourceReadResult,
    }
    switch (try loader.readPathAlloc(std.testing.allocator, "contracts")) {
        .denied => {},
        else => return error.UnexpectedSourceReadResult,
    }
}

test "filesystem source loader searches includes and only directly addresses allow roots" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "base");
    try temporary.dir.createDirPath(std.testing.io, "include");
    try temporary.dir.createDirPath(std.testing.io, "allowed");
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "include/Library.sol",
        .data = "library Library {}",
    });
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "base/Inside.sol",
        .data = "contract Inside {}",
    });
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "allowed/Direct.sol",
        .data = "contract Direct {}",
    });
    const base_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/base",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(base_path);
    const include_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/include",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(include_path);
    const allowed_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/allowed",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(allowed_path);
    const canonical_allowed = try std.Io.Dir.cwd().realPathFileAlloc(
        std.testing.io,
        allowed_path,
        std.testing.allocator,
    );
    defer std.testing.allocator.free(canonical_allowed);
    const direct_path = try std.fmt.allocPrint(
        std.testing.allocator,
        "{s}/Direct.sol",
        .{canonical_allowed},
    );
    defer std.testing.allocator.free(direct_path);
    var loader = try FileSourceLoader.init(
        std.testing.allocator,
        std.testing.io,
        .{
            .base_path = base_path,
            .include_paths = &.{include_path},
            .allow_paths = allowed_path,
        },
    );
    defer loader.deinit();

    const included = try loader.readPathAlloc(
        std.testing.allocator,
        "./Library.sol",
    );
    switch (included) {
        .contents => |contents| {
            defer std.testing.allocator.free(contents);
            try std.testing.expectEqualStrings("library Library {}", contents);
        },
        else => return error.UnexpectedSourceReadResult,
    }
    const direct = try loader.readPathAlloc(std.testing.allocator, direct_path);
    switch (direct) {
        .contents => |contents| {
            defer std.testing.allocator.free(contents);
            try std.testing.expectEqualStrings("contract Direct {}", contents);
        },
        else => return error.UnexpectedSourceReadResult,
    }
    const inside = try loader.readPathAlloc(
        std.testing.allocator,
        "./Inside.sol",
    );
    switch (inside) {
        .contents => |contents| {
            defer std.testing.allocator.free(contents);
            try std.testing.expectEqualStrings("contract Inside {}", contents);
        },
        else => return error.UnexpectedSourceReadResult,
    }
    const allowed_relative = try loader.readPathAlloc(
        std.testing.allocator,
        "../allowed/Direct.sol",
    );
    switch (allowed_relative) {
        .contents => |contents| {
            defer std.testing.allocator.free(contents);
            try std.testing.expectEqualStrings("contract Direct {}", contents);
        },
        else => return error.UnexpectedSourceReadResult,
    }
    switch (try loader.readPathAlloc(std.testing.allocator, "Direct.sol")) {
        .not_found => {},
        else => return error.UnexpectedSourceReadResult,
    }
}

test "filesystem source loader rejects symlink escapes" {
    if (comptime builtin.os.tag == .windows)
        return error.SkipZigTest;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "base");
    try temporary.dir.createDirPath(std.testing.io, "outside");
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "outside/Secret.sol",
        .data = "secret",
    });
    try temporary.dir.symLink(
        std.testing.io,
        "../outside/Secret.sol",
        "base/file-link.sol",
        .{},
    );
    try temporary.dir.symLink(
        std.testing.io,
        "../outside",
        "base/directory-link",
        .{ .is_directory = true },
    );
    const base_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/base",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(base_path);
    var loader = try FileSourceLoader.init(
        std.testing.allocator,
        std.testing.io,
        .{ .base_path = base_path },
    );
    defer loader.deinit();

    switch (try loader.readPathAlloc(std.testing.allocator, "file-link.sol")) {
        .denied => {},
        else => return error.UnexpectedSourceReadResult,
    }
    switch (try loader.readPathAlloc(
        std.testing.allocator,
        "directory-link/Secret.sol",
    )) {
        .denied => {},
        else => return error.UnexpectedSourceReadResult,
    }
}

test "filesystem source loader rejects symlinks in configured roots" {
    if (comptime builtin.os.tag == .windows)
        return error.SkipZigTest;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "target/root");
    try temporary.dir.symLink(
        std.testing.io,
        "target/root",
        "root-link",
        .{ .is_directory = true },
    );
    const linked_root = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/root-link",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(linked_root);

    if (FileSourceLoader.init(
        std.testing.allocator,
        std.testing.io,
        .{ .base_path = linked_root },
    )) |initialized| {
        var loader = initialized;
        loader.deinit();
        return error.UnexpectedSourceRootOpen;
    } else |_| {}
}

test "filesystem source loader rejects a swapped root ancestor" {
    if (comptime builtin.os.tag == .windows)
        return error.SkipZigTest;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "stable/parent/root");
    try temporary.dir.createDirPath(std.testing.io, "outside/root");
    const original_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/stable/parent/root",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(original_path);
    const canonical = try std.Io.Dir.cwd().realPathFileAlloc(
        std.testing.io,
        original_path,
        std.testing.allocator,
    );
    defer std.testing.allocator.free(canonical);

    try temporary.dir.rename(
        "stable/parent",
        temporary.dir,
        "stable/original-parent",
        std.testing.io,
    );
    try temporary.dir.symLink(
        std.testing.io,
        "../outside",
        "stable/parent",
        .{ .is_directory = true },
    );

    var loader: FileSourceLoader = .{
        .allocator = std.testing.allocator,
        .io = std.testing.io,
        .max_total_bytes = max_total_loaded_source_bytes,
    };
    defer loader.deinit();
    if (loader.openCanonicalDirectory(canonical, false)) |directory| {
        directory.close(std.testing.io);
        return error.UnexpectedSourceRootOpen;
    } else |_| {}
}

test "filesystem source loader rejects a FIFO without blocking" {
    if (comptime builtin.os.tag == .windows or
        builtin.os.tag == .wasi or
        builtin.os.tag == .uefi or
        !builtin.link_libc)
    {
        return error.SkipZigTest;
    }

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "base");
    const base_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/base",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(base_path);
    const fifo_path = try std.fmt.allocPrintSentinel(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/base/source.pipe",
        .{&temporary.sub_path},
        0,
    );
    defer std.testing.allocator.free(fifo_path);
    const fifo = struct {
        extern "c" fn mkfifo(path: [*:0]const u8, mode: std.c.mode_t) c_int;
    }.mkfifo;
    try std.testing.expectEqual(@as(c_int, 0), fifo(fifo_path.ptr, 0o600));

    var loader = try FileSourceLoader.init(
        std.testing.allocator,
        std.testing.io,
        .{ .base_path = base_path },
    );
    defer loader.deinit();
    switch (try loader.readPathAlloc(std.testing.allocator, "source.pipe")) {
        .denied => {},
        else => return error.UnexpectedSourceReadResult,
    }
}

test "filesystem source path arguments reject empty and implicit roots" {
    try std.testing.expectError(
        error.InvalidBasePath,
        validateSourcePathArguments("", &.{}),
    );
    try std.testing.expectError(
        error.IncludePathRequiresBasePath,
        validateSourcePathArguments(null, &.{"include"}),
    );
    try std.testing.expectError(
        error.InvalidIncludePath,
        validateSourcePathArguments(".", &.{""}),
    );
}

test "filesystem source loader enforces a per-request total byte limit" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "base");
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "base/A.sol",
        .data = "123",
    });
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "base/B.sol",
        .data = "45",
    });
    const base_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/base",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(base_path);
    var loader = try FileSourceLoader.init(
        std.testing.allocator,
        std.testing.io,
        .{ .base_path = base_path, .max_total_bytes = 4 },
    );
    defer loader.deinit();

    const first = try loader.readPathAlloc(std.testing.allocator, "A.sol");
    switch (first) {
        .contents => |contents| std.testing.allocator.free(contents),
        else => return error.UnexpectedSourceReadResult,
    }
    switch (try loader.readPathAlloc(std.testing.allocator, "B.sol")) {
        .too_large => {},
        else => return error.UnexpectedSourceReadResult,
    }
    loader.reset();
    const after_reset = try loader.readPathAlloc(std.testing.allocator, "B.sol");
    switch (after_reset) {
        .contents => |contents| std.testing.allocator.free(contents),
        else => return error.UnexpectedSourceReadResult,
    }
}

test "default parallel job policy is bounded and nonzero" {
    try std.testing.expect(defaultParallelJobs() >= 1);
    try std.testing.expect(defaultParallelJobs() <= max_default_parallel_jobs);
}

test "project config accepts parallel and cache policy" {
    const config = try parseProjectConfig(
        std.testing.allocator,
        "parallel = true\n" ++
            "jobs = 2\n" ++
            "cache = false\n" ++
            "cache-max-bytes = \"2GiB\"\n" ++
            "cache-max-entries = 4096\n" ++
            "cache-busy-timeout-ms = 50\n",
    );
    defer config.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(?bool, true), config.parallel);
    try std.testing.expectEqual(@as(?usize, 2), config.jobs);
    try std.testing.expectEqual(@as(?bool, false), config.cache);
    try std.testing.expectEqual(@as(?u64, 2 * 1024 * 1024 * 1024), config.cache_max_bytes);
    try std.testing.expectEqual(@as(?u64, 4096), config.cache_max_entries);
    try std.testing.expectEqual(@as(?u32, 50), config.cache_busy_timeout_ms);
    try std.testing.expectError(
        error.InvalidProjectConfig,
        parseProjectConfig(std.testing.allocator, "parallel = \"yes\"\n"),
    );
    try std.testing.expectError(
        error.UnknownProjectConfigKey,
        parseProjectConfig(std.testing.allocator, "unknown = true\n"),
    );
    try std.testing.expectError(
        error.InvalidProjectConfig,
        parseProjectConfig(std.testing.allocator, "jobs = -1\n"),
    );
    try std.testing.expectError(
        error.InvalidProjectConfig,
        parseProjectConfig(std.testing.allocator, "cache = \"off\"\n"),
    );
}

test "source path config owns merged strings and rejects escaping paths" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn run(allocator: std.mem.Allocator) !void {
            const defaults = try parseProjectConfig(allocator, "source-path = \"src\"\n");
            defer defaults.deinit(allocator);
            const overrides = try parseProjectConfig(allocator, "source-path = \"contracts\"\n");
            defer overrides.deinit(allocator);
            const merged = try mergeProjectConfig(allocator, defaults, overrides);
            defer merged.deinit(allocator);
            try std.testing.expectEqualStrings("contracts", merged.source_path.?);
            const fallback = try mergeProjectConfig(allocator, defaults, .{});
            defer fallback.deinit(allocator);
            try std.testing.expectEqualStrings("src", fallback.source_path.?);
        }
    }.run, .{});
    try std.testing.expectError(error.InvalidSourcePath, parseProjectConfig(std.testing.allocator, "source-path = \"../lib\"\n"));
    try std.testing.expectError(error.InvalidProjectConfig, parseProjectConfig(std.testing.allocator, "source-path = false\n"));
}

test "persistent cache is opt-in and the CLI disable takes precedence" {
    try std.testing.expect(!persistentCacheEnabled(.{}, false));
    try std.testing.expect(!persistentCacheEnabled(.{ .cache = false }, false));
    try std.testing.expect(persistentCacheEnabled(.{ .cache = true }, false));
    try std.testing.expect(!persistentCacheEnabled(.{ .cache = true }, true));
}

test "cache authentication keys require exactly 256 bits of hexadecimal" {
    const expected = [_]u8{0x5a} ** 32;
    try std.testing.expectEqual(
        expected,
        try parseCacheAuthenticationKey("5a" ** 32),
    );
    try std.testing.expectError(
        error.InvalidCacheAuthenticationKey,
        parseCacheAuthenticationKey("5a" ** 31),
    );
    try std.testing.expectError(
        error.InvalidCacheAuthenticationKey,
        parseCacheAuthenticationKey("zz" ** 32),
    );
}

test "cache byte sizes accept binary suffixes and reject invalid values" {
    try std.testing.expectEqual(@as(u64, 17), try parseByteSize("17"));
    try std.testing.expectEqual(@as(u64, 17), try parseByteSize("17B"));
    try std.testing.expectEqual(@as(u64, 2 * 1024), try parseByteSize("2KiB"));
    try std.testing.expectEqual(@as(u64, 3 * 1024 * 1024), try parseByteSize("3MiB"));
    try std.testing.expectEqual(
        @as(u64, 4 * 1024 * 1024 * 1024),
        try parseByteSize("4GiB"),
    );
    try std.testing.expectError(error.InvalidCharacter, parseByteSize("1MB"));
    try std.testing.expectError(error.Overflow, parseByteSize("18446744073709551615GiB"));
}

test "XDG user config path prefers an absolute override and falls back to HOME" {
    const explicit = (try xdgApplicationPathAlloc(
        std.testing.allocator,
        "/var/config",
        "/home/example",
        ".config",
        user_config_filename,
    )).?;
    defer std.testing.allocator.free(explicit);
    try std.testing.expectEqualStrings(
        "/var/config/oksolc/config.toml",
        explicit,
    );

    const fallback = (try xdgApplicationPathAlloc(
        std.testing.allocator,
        "relative-is-invalid",
        "/home/example",
        ".config",
        user_config_filename,
    )).?;
    defer std.testing.allocator.free(fallback);
    try std.testing.expectEqualStrings(
        "/home/example/.config/oksolc/config.toml",
        fallback,
    );

    try std.testing.expectEqual(
        @as(?[]u8, null),
        try xdgApplicationPathAlloc(
            std.testing.allocator,
            null,
            null,
            ".config",
            user_config_filename,
        ),
    );
}

test "project cache paths are segregated below an external cache root" {
    const directory = try artifactCacheDirectoryUnderRootAlloc(
        std.testing.allocator,
        "/var/cache/oksolc/projects-v2",
        "/work/repository",
    );
    defer std.testing.allocator.free(directory);
    try std.testing.expect(std.mem.startsWith(
        u8,
        directory,
        "/var/cache/oksolc/projects-v2/",
    ));
    try std.testing.expectEqual(
        @as(usize, "/var/cache/oksolc/projects-v2/".len + 64),
        directory.len,
    );
    try std.testing.expect(!pathContainedBy("/work/repository", directory));
}

test "project discovery prefers the nearest config and stops at a repository" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "repo/.git");
    try temporary.dir.createDirPath(std.testing.io, "repo/contracts/nested");

    const repository_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/repo",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(repository_path);
    const repository = try std.Io.Dir.cwd().realPathFileAlloc(
        std.testing.io,
        repository_path,
        std.testing.allocator,
    );
    defer std.testing.allocator.free(repository);
    const nested_path = try std.Io.Dir.path.join(
        std.testing.allocator,
        &.{ repository, "contracts", "nested" },
    );
    defer std.testing.allocator.free(nested_path);

    const outer = try findProjectRootAlloc(
        std.testing.allocator,
        std.testing.io,
        nested_path,
    );
    defer std.testing.allocator.free(outer);
    try std.testing.expectEqualStrings(repository, outer);

    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "repo/contracts/oksolc.toml",
        .data = "parallel = false\n",
    });
    const nested_project = try findProjectRootAlloc(
        std.testing.allocator,
        std.testing.io,
        nested_path,
    );
    defer std.testing.allocator.free(nested_project);
    const expected_nested = try std.Io.Dir.path.join(
        std.testing.allocator,
        &.{ repository, "contracts" },
    );
    defer std.testing.allocator.free(expected_nested);
    try std.testing.expectEqualStrings(expected_nested, nested_project);
}

test "cache security boundary covers the enclosing repository" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDirPath(std.testing.io, "repo/.git");
    try temporary.dir.createDirPath(std.testing.io, "repo/nested/project");

    const repository_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/repo",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(repository_path);
    const repository = try std.Io.Dir.cwd().realPathFileAlloc(
        std.testing.io,
        repository_path,
        std.testing.allocator,
    );
    defer std.testing.allocator.free(repository);
    const project = try std.Io.Dir.path.join(
        std.testing.allocator,
        &.{ repository, "nested", "project" },
    );
    defer std.testing.allocator.free(project);

    const boundary = try securityRootAlloc(
        std.testing.allocator,
        std.testing.io,
        project,
    );
    defer std.testing.allocator.free(boundary);
    try std.testing.expectEqualStrings(repository, boundary);
}

test "artifact cache directory is private even when it already exists" {
    if (comptime !@hasDecl(std.Io.Dir.Permissions, "toMode")) return;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDir(
        std.testing.io,
        "cache-dir",
        std.Io.Dir.Permissions.fromMode(0o755),
    );
    const database_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache-dir/artifacts.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(database_path);
    try std.testing.expect(prepareArtifactCacheDirectory(
        std.testing.io,
        database_path,
    ));
    const directory_path = std.Io.Dir.path.dirname(database_path).?;
    const stat = try std.Io.Dir.cwd().statFile(std.testing.io, directory_path, .{});
    try std.testing.expectEqual(
        @as(std.posix.mode_t, 0o700),
        stat.permissions.toMode() & 0o777,
    );
}

test "artifact cache directory rejects a symlink without changing its target" {
    if (comptime @import("builtin").os.tag == .windows)
        return error.SkipZigTest;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDir(
        std.testing.io,
        "outside",
        std.Io.Dir.Permissions.fromMode(0o755),
    );
    try temporary.dir.symLink(
        std.testing.io,
        "outside",
        "cache-dir",
        .{ .is_directory = true },
    );
    const database_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache-dir/artifacts.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(database_path);

    try std.testing.expect(!prepareArtifactCacheDirectory(
        std.testing.io,
        database_path,
    ));
    const target_stat = try temporary.dir.statFile(
        std.testing.io,
        "outside",
        .{},
    );
    try std.testing.expectEqual(
        @as(std.posix.mode_t, 0o755),
        target_stat.permissions.toMode() & 0o777,
    );
    try std.testing.expectError(
        error.FileNotFound,
        temporary.dir.access(std.testing.io, "outside/artifacts.sqlite", .{}),
    );
}

test "project config overrides user defaults except for cache opt-in" {
    const merged = try mergeProjectConfig(
        std.testing.allocator,
        .{
            .parallel = true,
            .jobs = 4,
            .cache = false,
            .cache_max_bytes = 1,
            .cache_max_entries = 2,
            .cache_busy_timeout_ms = 3,
        },
        restrictProjectCacheOptIn(.{
            .jobs = 2,
            .cache = true,
            .cache_max_bytes = 4,
            .cache_busy_timeout_ms = 5,
        }),
    );
    try std.testing.expectEqual(@as(?bool, true), merged.parallel);
    try std.testing.expectEqual(@as(?usize, 2), merged.jobs);
    try std.testing.expectEqual(@as(?bool, false), merged.cache);
    try std.testing.expectEqual(@as(?u64, 4), merged.cache_max_bytes);
    try std.testing.expectEqual(@as(?u64, 2), merged.cache_max_entries);
    try std.testing.expectEqual(@as(?u32, 5), merged.cache_busy_timeout_ms);

    defer merged.deinit(std.testing.allocator);
    const trusted_opt_in = try mergeProjectConfig(
        std.testing.allocator,
        .{ .cache = true },
        restrictProjectCacheOptIn(.{ .cache = true }),
    );
    defer trusted_opt_in.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(?bool, true), trusted_opt_in.cache);

    const project_opt_out = try mergeProjectConfig(
        std.testing.allocator,
        .{ .cache = true },
        restrictProjectCacheOptIn(.{ .cache = false }),
    );
    defer project_opt_out.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(?bool, false), project_opt_out.cache);
}

test "serve framing accepts CRLF and LF messages" {
    var reader: std.Io.Reader = .fixed(
        "Content-Type: application/json\r\n" ++
            "Content-Length: 2\r\n\r\n{}" ++
            "content-length: 2\n\n[]",
    );
    const first = (try readServeFrameAlloc(&reader, std.testing.allocator)).?;
    defer std.testing.allocator.free(first);
    try std.testing.expectEqualStrings("{}", first);
    const second = (try readServeFrameAlloc(&reader, std.testing.allocator)).?;
    defer std.testing.allocator.free(second);
    try std.testing.expectEqualStrings("[]", second);
    try std.testing.expectEqual(
        @as(?[]u8, null),
        try readServeFrameAlloc(&reader, std.testing.allocator),
    );

    var output_buffer: [64]u8 = undefined;
    var writer: std.Io.Writer = .fixed(&output_buffer);
    try writeServeFrame(&writer, "{}");
    try std.testing.expectEqualStrings(
        "Content-Length: 2\r\n\r\n{}",
        writer.buffered(),
    );
}

test "serve framing rejects ambiguous or oversized messages" {
    var duplicate: std.Io.Reader = .fixed(
        "Content-Length: 0\nContent-Length: 0\n\n",
    );
    try std.testing.expectError(
        error.DuplicateContentLength,
        readServeFrameAlloc(&duplicate, std.testing.allocator),
    );

    var missing: std.Io.Reader = .fixed("Content-Type: application/json\n\n");
    try std.testing.expectError(
        error.MissingContentLength,
        readServeFrameAlloc(&missing, std.testing.allocator),
    );

    var oversized: std.Io.Reader = .fixed(
        "Content-Length: 268435457\n\n",
    );
    try std.testing.expectError(
        error.InputTooLarge,
        readServeFrameAlloc(&oversized, std.testing.allocator),
    );
}

test "live workspace and progress are readable while the initial compiler is blocked" {
    const Fixture = struct {
        io: std.Io,
        entered: std.Io.Event = .unset,
        release: std.Io.Event = .unset,

        fn compile(context: *anyopaque, allocator: std.mem.Allocator, request: solidity.standard_json.Request) solidity.standard_json.CompileError!solidity.standard_json.Output {
            const self: *@This() = @ptrCast(@alignCast(context));
            request.progress.?.report(.{ .stage = .generating_contracts, .completed_items = 1, .estimated_total_items = 3, .item_name = "Initial" });
            self.entered.set(self.io);
            self.release.wait(self.io) catch return error.InternalFailure;
            return .{ .allocator = allocator, .bytes = try allocator.dupe(u8, "{}") };
        }
    };
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.writeFile(io, .{ .sub_path = "Initial.sol", .data = "contract Initial {}" });
    const root = try temporary.dir.realPathFileAlloc(io, ".", allocator);
    defer allocator.free(root);
    var loader = try FileSourceLoader.init(allocator, io, .{ .base_path = root });
    defer loader.deinit();
    var store = try @import("browser/store.zig").Store.open(allocator, io, ":memory:");
    defer store.deinit();
    var live: BrowserLive = .{ .io = io, .source_path = "." };
    var fixture: Fixture = .{ .io = io };
    var service: SourceService = .{
        .allocator = allocator,
        .io = io,
        .compiler_io = null,
        .compiler = .{ .context = &fixture, .compile_fn = Fixture.compile },
        .loader = &loader,
        .directory_path = root,
        .project_root = root,
        .prefix = "",
        .poll_ms = 30,
        .store = &store,
        .live = &live,
    };
    defer service.deinit();
    var future = try io.concurrent(SourceService.update, .{&service});
    defer {
        fixture.release.set(io);
        future.cancel(io) catch {};
    }
    try fixture.entered.waitTimeout(io, .{ .duration = .{ .clock = .awake, .raw = .fromSeconds(10) } });
    try std.testing.expectEqual(@as(?i64, null), try store.latest());
    const pending = live.get();
    try std.testing.expectEqual(.compiling, pending.state.phase);
    try std.testing.expectEqual(@as(usize, 1), pending.state.completed_items);
    try std.testing.expectEqual(@as(usize, 3), pending.state.total_items);
    const file = (try store.fileAlloc(allocator, 0, "Initial.sol")).?;
    defer allocator.free(file.content.?);
    try std.testing.expectEqualStrings("contract Initial {}", file.content.?);
    fixture.release.set(io);
    try future.await(io);
    try std.testing.expectEqual(.watching, live.get().state.phase);
    try std.testing.expectEqual(@as(?i64, 1), live.get().current);
}

test "live publication retries retain output and invalidate changed request or import bytes" {
    const Fixture = struct {
        calls: usize = 0,

        fn compile(context: *anyopaque, allocator: std.mem.Allocator, request: solidity.standard_json.Request) solidity.standard_json.CompileError!solidity.standard_json.Output {
            const self: *@This() = @ptrCast(@alignCast(context));
            self.calls += 1;
            const imported = request.source_loader.?.read(allocator, "source", "lib/Used.sol") catch return error.InternalFailure;
            defer imported.deinit(allocator);
            if (imported != .contents) return error.InternalFailure;
            return .{ .allocator = allocator, .bytes = try std.json.Stringify.valueAlloc(allocator, .{
                .imported = imported.contents,
                .call = self.calls,
            }, .{}) };
        }
    };
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    // Retain completed output across failed saves and validate every read before retrying.
    for (0..4) |edit| {
        var temporary = std.testing.tmpDir(.{});
        defer temporary.cleanup();
        try temporary.dir.createDir(io, "src", .default_dir);
        try temporary.dir.createDir(io, "lib", .default_dir);
        try temporary.dir.writeFile(io, .{ .sub_path = "src/Initial.sol", .data = "contract Initial {}" });
        try temporary.dir.writeFile(io, .{ .sub_path = "lib/Used.sol", .data = "library Used { /*1*/ }" });
        const root = try temporary.dir.realPathFileAlloc(io, ".", allocator);
        defer allocator.free(root);
        const source_root = try std.Io.Dir.path.join(allocator, &.{ root, "src" });
        defer allocator.free(source_root);
        var loader = try FileSourceLoader.init(allocator, io, .{ .base_path = root });
        defer loader.deinit();
        var store = try @import("browser/store.zig").Store.open(allocator, io, ":memory:");
        defer store.deinit();
        try store.db.execNoArgs("CREATE TRIGGER reject_publication BEFORE INSERT ON compilation BEGIN SELECT RAISE(ABORT,'test'); END;");
        var live: BrowserLive = .{ .io = io, .source_path = "src" };
        var fixture: Fixture = .{};
        var service: SourceService = .{
            .allocator = allocator,
            .io = io,
            .compiler_io = null,
            .compiler = .{ .context = &fixture, .compile_fn = Fixture.compile },
            .loader = &loader,
            .directory_path = source_root,
            .project_root = root,
            .prefix = "src",
            .poll_ms = 30,
            .store = &store,
            .live = &live,
        };
        defer service.deinit();
        try std.testing.expectError(error.ConstraintTrigger, service.update());
        const workspace_revision = live.get().workspace_revision;
        const initial_snapshot = try store.latest();
        for (0..3) |_| {
            try std.testing.expectError(error.ConstraintTrigger, service.update());
            try std.testing.expectEqual(@as(usize, 1), fixture.calls);
            try std.testing.expectEqual(.stale, live.get().state.phase);
            try std.testing.expectEqual(initial_snapshot, try store.latest());
            try std.testing.expectEqual(workspace_revision, live.get().workspace_revision);
        }
        switch (edit) {
            0 => try temporary.dir.writeFile(io, .{ .sub_path = "lib/Used.sol", .data = "library Used { /*2*/ }" }),
            1 => try temporary.dir.writeFile(io, .{ .sub_path = "src/Initial.sol", .data = "contract Changed {}" }),
            2 => try temporary.dir.writeFile(io, .{ .sub_path = "remappings.txt", .data = "pkg/=lib/\n" }),
            3 => try temporary.dir.writeFile(io, .{ .sub_path = "src/Added.sol", .data = "contract Added {}" }),
            else => unreachable,
        }
        try std.testing.expectError(error.ConstraintTrigger, service.update());
        try std.testing.expectEqual(@as(usize, 2), fixture.calls);
        try std.testing.expectEqual(workspace_revision + 1, live.get().workspace_revision);
        const saved = try allocator.dupe(u8, service.pending.?.output.bytes);
        defer allocator.free(saved);
        try store.db.execNoArgs("DROP TRIGGER reject_publication;");
        try service.update();
        try std.testing.expectEqual(@as(usize, 2), fixture.calls);
        try std.testing.expectEqual(.watching, live.get().state.phase);
        try std.testing.expect(service.pending == null);
        const id = live.get().current.?;
        const output = (try store.documentAlloc(allocator, id, .output)).?;
        defer allocator.free(output);
        try std.testing.expectEqualStrings(saved, output);
        try service.update();
        try std.testing.expectEqual(@as(usize, 2), fixture.calls);
        // Revert to a previously accepted revision after another failed
        // update. Its old read set must not bless the intervening page.
        try store.db.execNoArgs("CREATE TRIGGER reject_publication BEFORE INSERT ON compilation BEGIN SELECT RAISE(ABORT,'test'); END;");
        try temporary.dir.writeFile(io, .{ .sub_path = "lib/Used.sol", .data = "library Used { /*3*/ }" });
        try std.testing.expectError(error.ConstraintTrigger, service.update());
        const calls_before_revert = fixture.calls;
        const reverted = if (edit == 0) "library Used { /*2*/ }" else "library Used { /*1*/ }";
        try temporary.dir.writeFile(io, .{ .sub_path = "lib/Used.sol", .data = reverted });
        try store.db.execNoArgs("DROP TRIGGER reject_publication;");
        try service.update();
        try std.testing.expectEqual(calls_before_revert + 1, fixture.calls);
        const final = (try store.documentAlloc(allocator, live.get().current.?, .output)).?;
        defer allocator.free(final);
        try std.testing.expect(std.mem.find(u8, final, reverted) != null);
        try std.testing.expect(service.pending == null);
        try std.testing.expectEqual(.watching, live.get().state.phase);
    }
}

test {
    _ = CompileInput;
    _ = @import("install.zig");
    _ = ProjectSources;
    _ = @import("browser/capture.zig");
    _ = @import("browser/server.zig");
    _ = @import("browser/live.zig");
    _ = @import("browser/resume.zig");
}
