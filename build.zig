// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");
const builtin = @import("builtin");
const zlinter = @import("zlinter");

const required_zig_version: std.SemanticVersion = .{
    .major = 0,
    .minor = 16,
    .patch = 0,
};

comptime {
    if (builtin.zig_version.order(required_zig_version) != .eq) {
        @compileError(
            "solidity-zig requires Zig 0.16.0; found " ++
                builtin.zig_version_string,
        );
    }
}

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const strip_cli = b.option(
        bool,
        "strip",
        "Strip debug information from the oksolc executable",
    ) orelse false;
    const benchmark_runs = b.option(
        u32,
        "benchmark-runs",
        "Number of measured runs per benchmark workload",
    ) orelse 3;
    const benchmark_warmups = b.option(
        u32,
        "benchmark-warmups",
        "Number of untimed warmup runs per compiler and local workload",
    ) orelse 1;
    const adapter_fuzz_runs = b.option(
        u32,
        "adapter-fuzz-runs",
        "Number of ASan/UBSan yyjson adapter fuzz executions",
    ) orelse 1_000;
    const adapter_fuzz_seed = b.option(
        u64,
        "adapter-fuzz-seed",
        "Nonzero deterministic seed for ASan/UBSan yyjson adapter mutations",
    ) orelse 0x6a09e667f3bcc909;
    if (adapter_fuzz_seed == 0)
        @panic("-Dadapter-fuzz-seed must be greater than zero");
    const reference_solc = b.option(
        []const u8,
        "benchmark-reference-solc",
        "System-installed solc 0.8.36 executable used for parity comparisons",
    ) orelse "solc";
    const compiler_build_identity_override = b.option(
        []const u8,
        "compiler-build-identity",
        "Content-derived compiler build identity for persistent cache isolation",
    );
    const detected_compiler_build = detectCompilerBuildIdentity(b);
    const compiler_build_identity = compiler_build_identity_override orelse
        detected_compiler_build.identity;
    const compiler_build_identity_available = compiler_build_identity_override != null or
        detected_compiler_build.available;
    const compiler_build_validation_identity = if (compiler_build_identity_override == null)
        detected_compiler_build.validation_identity
    else
        null;
    if (compiler_build_identity_override) |identity|
        if (identity.len == 0) @panic("-Dcompiler-build-identity must not be empty");

    const build_options = b.addOptions();
    build_options.addOption([]const u8, "license_text", @embedFile("LICENSE.txt"));
    build_options.addOption(
        []const u8,
        "third_party_licenses",
        @embedFile("THIRD_PARTY_LICENSES.txt"),
    );
    build_options.addOption(
        []const u8,
        "compiler_build_identity",
        compiler_build_identity,
    );
    build_options.addOption(
        bool,
        "compiler_build_identity_available",
        compiler_build_identity_available,
    );
    const build_options_module = build_options.createModule();

    const common_module = b.createModule(.{
        .root_source_file = b.path("src/common/root.zig"),
        .target = target,
        .optimize = optimize,
    });

    const big_int_module = b.createModule(.{
        .root_source_file = b.path("src/libsolutil/big_int.zig"),
        .target = target,
        .optimize = optimize,
    });

    const cxx_compat_module = b.createModule(.{
        .root_source_file = b.path("src/cxx_compat/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "big_int", .module = big_int_module },
        },
    });

    const optimizer_workloads_module = b.createModule(.{
        .root_source_file = b.path("test/benchmarks/optimizer_workloads.zig"),
        .target = target,
        .optimize = optimize,
    });

    const yyjson_dependency = b.dependency("yyjson", .{});
    const translated_yyjson_adapter = b.addTranslateC(.{
        .root_source_file = b.path("include/yyjson_adapter.h"),
        .target = target,
        .optimize = optimize,
    });
    const translated_sqlite = b.addTranslateC(.{
        .root_source_file = b.path("vendor/sqlite/sqlite3.h"),
        .target = target,
        .optimize = optimize,
    });
    const sqlite_c_module = translated_sqlite.createModule();
    const zqlite_dependency = b.dependency("zqlite", .{});
    // One SQLite implementation per artifact. Use zqlite's Zig wrapper with
    // our pinned amalgamation, C translation, and existing compile flags.
    const zqlite_module = b.createModule(.{
        .root_source_file = zqlite_dependency.path("src/zqlite.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{.{ .name = "c", .module = sqlite_c_module }},
    });

    const compiler_module = b.createModule(.{
        .root_source_file = b.path("src/compiler.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
        .imports = &.{
            .{ .name = "build_options", .module = build_options_module },
            .{ .name = "big_int", .module = big_int_module },
            .{ .name = "common", .module = common_module },
            .{ .name = "cxx_compat", .module = cxx_compat_module },
            .{ .name = "zqlite", .module = zqlite_module },
            .{ .name = "yyjson_adapter_c", .module = translated_yyjson_adapter.createModule() },
        },
    });
    compiler_module.addIncludePath(b.path("include"));
    compiler_module.addIncludePath(yyjson_dependency.path("src"));
    compiler_module.addIncludePath(b.path("vendor/sqlite"));
    compiler_module.addCSourceFile(.{
        .file = b.path("src/libsolc/yyjson_adapter.c"),
        .flags = &.{ "-std=c99", "-fvisibility=hidden", "-Dyyjson_api=" },
    });
    compiler_module.addCSourceFile(.{
        .file = yyjson_dependency.path("src/yyjson.c"),
        .flags = &.{ "-std=c99", "-fvisibility=hidden", "-Dyyjson_api=" },
    });
    compiler_module.addCSourceFile(.{
        .file = b.path("vendor/sqlite/sqlite3.c"),
        .flags = &.{
            "-std=c99",
            "-fvisibility=hidden",
            "-DSQLITE_THREADSAFE=1",
            "-DSQLITE_DQS=0",
            "-DSQLITE_DEFAULT_MEMSTATUS=0",
            "-DSQLITE_DEFAULT_WAL_SYNCHRONOUS=1",
            "-DSQLITE_OMIT_DEPRECATED",
            "-DSQLITE_OMIT_LOAD_EXTENSION",
            "-DSQLITE_TEMP_STORE=3",
        },
    });

    const libsolc_library = b.addLibrary(.{
        .name = "solc",
        .linkage = .dynamic,
        .root_module = compiler_module,
    });
    libsolc_library.installHeader(b.path("include/libsolc.h"), "libsolc.h");
    const libsolc_identity_validation = addCompilerBuildIdentityValidation(
        b,
        libsolc_library,
        compiler_build_validation_identity,
    );
    const install_libsolc = b.addInstallArtifact(libsolc_library, .{});
    dependOnValidation(&install_libsolc.step, libsolc_identity_validation);
    b.getInstallStep().dependOn(&install_libsolc.step);

    const solidity_module = b.addModule("solidity", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "common", .module = common_module },
            .{ .name = "compiler", .module = compiler_module },
            .{ .name = "cxx_compat", .module = cxx_compat_module },
        },
    });

    const clap_dependency = b.dependency("clap", .{
        .target = target,
        .optimize = optimize,
    });
    const toml_dependency = b.dependency("toml", .{
        .target = target,
        .optimize = optimize,
    });
    const httpz_dependency = b.dependency("httpz", .{ .target = target, .optimize = optimize });
    const cli_module = b.createModule(.{
        .root_source_file = b.path("src/cli/main.zig"),
        .target = target,
        .optimize = optimize,
        .strip = strip_cli,
        .imports = &.{
            .{ .name = "clap", .module = clap_dependency.module("clap") },
            .{ .name = "solidity", .module = solidity_module },
            .{ .name = "toml", .module = toml_dependency.module("toml") },
            .{ .name = "zqlite", .module = zqlite_module },
            .{ .name = "httpz", .module = httpz_dependency.module("httpz") },
        },
    });
    @import("build_support/browser.zig").build(b, cli_module);
    const cli = b.addExecutable(.{
        .name = "oksolc",
        .root_module = cli_module,
    });
    const cli_identity_validation = addCompilerBuildIdentityValidation(
        b,
        cli,
        compiler_build_validation_identity,
    );
    const install_cli = b.addInstallArtifact(cli, .{});
    dependOnValidation(&install_cli.step, cli_identity_validation);
    b.getInstallStep().dependOn(&install_cli.step);
    b.step("build-cli", "Install the oksolc CLI").dependOn(&install_cli.step);
    const browser_smoke = b.addSystemCommand(&.{"python3"});
    browser_smoke.addFileArg(b.path("test/zig/cli/browser_smoke.py"));
    browser_smoke.addArtifactArg(cli);
    dependOnValidation(&browser_smoke.step, cli_identity_validation);
    b.step("browser-smoke", "Test the localhost compiler browser over HTTP").dependOn(&browser_smoke.step);
    const source_serve_smoke = b.addSystemCommand(&.{"python3"});
    source_serve_smoke.addFileArg(b.path("test/zig/cli/source_serve_smoke.py"));
    source_serve_smoke.addArtifactArg(cli);
    dependOnValidation(&source_serve_smoke.step, cli_identity_validation);
    b.step("source-serve-smoke", "Test source-root and imported dependency watching").dependOn(&source_serve_smoke.step);
    const live_browser_smoke = b.addSystemCommand(&.{"python3"});
    live_browser_smoke.addFileArg(b.path("test/zig/cli/live_browser_smoke.py"));
    live_browser_smoke.addArtifactArg(cli);
    dependOnValidation(&live_browser_smoke.step, cli_identity_validation);
    b.step("live-browser-smoke", "Test the combined source watcher and live SQL browser").dependOn(&live_browser_smoke.step);
    const diagnostic_limit_smoke = b.addSystemCommand(&.{"python3"});
    diagnostic_limit_smoke.addFileArg(b.path("test/zig/cli/diagnostic_limit_smoke.py"));
    diagnostic_limit_smoke.addArtifactArg(cli);
    dependOnValidation(&diagnostic_limit_smoke.step, cli_identity_validation);
    b.step("diagnostic-limit-smoke", "Test diagnostic-limit publication and session recovery").dependOn(&diagnostic_limit_smoke.step);
    const install_smoke = b.addSystemCommand(&.{"python3"});
    install_smoke.addFileArg(b.path("test/zig/cli/install_smoke.py"));
    install_smoke.addArtifactArg(cli);
    dependOnValidation(&install_smoke.step, cli_identity_validation);
    b.step("install-smoke", "Test remapped Git submodule installation with local repositories").dependOn(&install_smoke.step);
    const browser_startup_smoke = b.addSystemCommand(&.{"python3"});
    browser_startup_smoke.addFileArg(b.path("test/zig/cli/browser_startup_smoke.py"));
    browser_startup_smoke.addArtifactArg(cli);
    dependOnValidation(&browser_startup_smoke.step, cli_identity_validation);
    b.step("browser-startup-smoke", "Test immediate live HTTP and workspace availability").dependOn(&browser_startup_smoke.step);
    const browser_resume_smoke = b.addSystemCommand(&.{"python3"});
    browser_resume_smoke.addFileArg(b.path("test/zig/cli/browser_resume_smoke.py"));
    browser_resume_smoke.addArtifactArg(cli);
    dependOnValidation(&browser_resume_smoke.step, cli_identity_validation);
    b.step("browser-resume-smoke", "Test persistent live snapshot reuse and invalidation").dependOn(&browser_resume_smoke.step);
    const reference_corpus_module = b.createModule(.{
        .root_source_file = b.path("test/zig/reference_corpus.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{.{ .name = "solidity", .module = solidity_module }},
    });
    const standard_json_dispatch_module = b.createModule(.{
        .root_source_file = b.path("test/zig/standard_json_dispatch.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{.{ .name = "solidity", .module = solidity_module }},
    });
    const parser_fuzz_module = b.createModule(.{
        .root_source_file = b.path("src/fuzz_parser.zig"),
        .target = target,
        // Zig 0.16.0's Debug test runner cannot rebuild fuzz tests with
        // coverage instrumentation. ReleaseSafe retains safety checks and is
        // fast enough for sustained fuzzing.
        .optimize = .ReleaseSafe,
        .imports = &.{
            .{ .name = "big_int", .module = big_int_module },
            .{ .name = "cxx_compat", .module = cxx_compat_module },
        },
    });
    const json_fuzz_module = b.createModule(.{
        .root_source_file = b.path("src/fuzz_json.zig"),
        .target = target,
        .optimize = .ReleaseSafe,
    });
    // Zig 0.16's native fuzz runner cannot consume sanitizer-coverage tables
    // emitted by imported C objects. Keep those objects uninstrumented here;
    // the dedicated adapter target below mutation-fuzzes the same C sources
    // with ASan/UBSan.
    const no_native_fuzz_c_coverage =
        "-fno-sanitize-coverage=inline-8bit-counters,pc-table,trace-cmp";
    const standard_json_fuzz_compiler_module = b.createModule(.{
        .root_source_file = b.path("src/compiler.zig"),
        .target = target,
        .optimize = .ReleaseSafe,
        .link_libc = true,
        .imports = &.{
            .{ .name = "build_options", .module = build_options_module },
            .{ .name = "big_int", .module = big_int_module },
            .{ .name = "common", .module = common_module },
            .{ .name = "cxx_compat", .module = cxx_compat_module },
            .{ .name = "zqlite", .module = zqlite_module },
            .{ .name = "yyjson_adapter_c", .module = translated_yyjson_adapter.createModule() },
        },
    });
    standard_json_fuzz_compiler_module.addIncludePath(b.path("include"));
    standard_json_fuzz_compiler_module.addIncludePath(yyjson_dependency.path("src"));
    standard_json_fuzz_compiler_module.addIncludePath(b.path("vendor/sqlite"));
    standard_json_fuzz_compiler_module.addCSourceFile(.{
        .file = b.path("src/libsolc/yyjson_adapter.c"),
        .flags = &.{
            "-std=c99",
            "-fvisibility=hidden",
            "-Dyyjson_api=",
            no_native_fuzz_c_coverage,
        },
    });
    standard_json_fuzz_compiler_module.addCSourceFile(.{
        .file = yyjson_dependency.path("src/yyjson.c"),
        .flags = &.{
            "-std=c99",
            "-fvisibility=hidden",
            "-Dyyjson_api=",
            no_native_fuzz_c_coverage,
        },
    });
    standard_json_fuzz_compiler_module.addCSourceFile(.{
        .file = b.path("vendor/sqlite/sqlite3.c"),
        .flags = &.{
            "-std=c99",
            "-fvisibility=hidden",
            "-DSQLITE_THREADSAFE=1",
            "-DSQLITE_DQS=0",
            "-DSQLITE_DEFAULT_MEMSTATUS=0",
            "-DSQLITE_DEFAULT_WAL_SYNCHRONOUS=1",
            "-DSQLITE_OMIT_DEPRECATED",
            "-DSQLITE_OMIT_LOAD_EXTENSION",
            "-DSQLITE_TEMP_STORE=3",
            no_native_fuzz_c_coverage,
        },
    });
    const standard_json_fuzz_module = b.createModule(.{
        .root_source_file = b.path("src/fuzz_standard_json.zig"),
        .target = target,
        .optimize = .ReleaseSafe,
        .imports = &.{.{
            .name = "compiler",
            .module = standard_json_fuzz_compiler_module,
        }},
    });
    const incremental_edit_trace_module = b.createModule(.{
        .root_source_file = b.path("test/benchmarks/incremental_edit_trace.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{.{ .name = "solidity", .module = solidity_module }},
    });
    const cli_smoke_step = b.step("cli-smoke", "Exercise the oksolc CLI");
    const cache_lifecycle_smoke = b.addSystemCommand(&.{"python3"});
    cache_lifecycle_smoke.addFileArg(b.path("test/zig/cli/cache_lifecycle_smoke.py"));
    cache_lifecycle_smoke.addArtifactArg(cli);
    dependOnValidation(&cache_lifecycle_smoke.step, cli_identity_validation);
    b.step("cache-lifecycle-smoke", "Test persistent cache deletion, restart and recovery").dependOn(&cache_lifecycle_smoke.step);
    cli_smoke_step.dependOn(&cache_lifecycle_smoke.step);
    const cli_version_command = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_version_command);
    dependOnValidation(&cli_version_command.step, cli_identity_validation);
    cli_version_command.addArg("version");
    const cli_version_output = cli_version_command.captureStdOut(.{
        .basename = "oksolc-version.txt",
    });
    const cli_version_check = b.addCheckFile(cli_version_output, .{
        .expected_exact = "oksolc 0.8.36+zig\n",
    });
    cli_smoke_step.dependOn(&cli_version_check.step);

    const cli_help_command = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_help_command);
    dependOnValidation(&cli_help_command.step, cli_identity_validation);
    cli_help_command.addArg("help");
    const cli_help_output = cli_help_command.captureStdOut(.{
        .basename = "oksolc-help.txt",
    });
    const cli_help_check = b.addCheckFile(cli_help_output, .{
        .expected_matches = &.{
            "oksolc — A Solidity compiler",
            "  oksolc compile ",
            "  oksolc standard-json ",
            "  oksolc serve ",
            "  oksolc watch ",
            "  oksolc cache ",
            "  oksolc clean",
            "  oksolc version",
        },
    });
    cli_smoke_step.dependOn(&cli_help_check.step);

    const cli_standard_json_command = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_standard_json_command);
    dependOnValidation(&cli_standard_json_command.step, cli_identity_validation);
    cli_standard_json_command.addArgs(&.{
        "standard-json",
        "test/zig/standard-json/yul-basic.json",
    });
    const cli_standard_json_output = cli_standard_json_command.captureStdOut(.{
        .basename = "oksolc-standard-json.json",
    });
    const cli_standard_json_check = b.addCheckFile(cli_standard_json_output, .{
        .expected_exact = @embedFile("test/zig/standard-json/expected/yul-basic.json"),
    });
    cli_smoke_step.dependOn(&cli_standard_json_check.step);

    const source_url_settings =
        \\,"settings":{"viaIR":true,"optimizer":{"enabled":true},"outputSelection":{"*":{"*":["abi"]}}}}
    ;
    const source_base_request =
        \\{"language":"Solidity","sources":{"Inside.sol":{"urls":["./Inside.sol"]}}
    ++ source_url_settings;
    const source_include_request =
        \\{"language":"Solidity","sources":{"Library.sol":{"urls":["./Library.sol"]}}
    ++ source_url_settings;
    const source_outside_request =
        \\{"language":"Solidity","sources":{"Secret.sol":{"urls":["../outside/Secret.sol"]}}
    ++ source_url_settings;
    const source_callback_failed =
        \\{"errors":[{"component":"general","formattedMessage":"Source callback failed.","message":"Source callback failed.","severity":"error","type":"IOError"}]}
    ;
    const source_callback_unsupported =
        \\{"errors":[{"component":"general","formattedMessage":"Source callback is not available in this request.","message":"Source callback is not available in this request.","severity":"error","type":"IOError"}]}
    ;
    const source_loader_cwd = b.path("test/zig/cli/source-loader/base");

    const cli_source_base = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_source_base);
    dependOnValidation(&cli_source_base.step, cli_identity_validation);
    cli_source_base.addArgs(&.{
        "--standard-json",
        "--base-path",
        "test/zig/cli/source-loader/base",
    });
    cli_source_base.setStdIn(.{ .bytes = source_base_request });
    const cli_source_base_output = cli_source_base.captureStdOut(.{
        .basename = "oksolc-source-base.json",
    });
    const cli_source_base_check = b.addCheckFile(cli_source_base_output, .{
        .expected_matches = &.{ "\"Inside.sol\"", "\"Inside\"", "\"abi\":[]" },
    });
    cli_smoke_step.dependOn(&cli_source_base_check.step);

    const cli_source_include = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_source_include);
    dependOnValidation(&cli_source_include.step, cli_identity_validation);
    cli_source_include.setCwd(source_loader_cwd);
    cli_source_include.addArgs(&.{
        "--standard-json",
        "--base-path",
        ".",
        "--include-path",
        ".",
        "--include-path",
        "../include",
    });
    cli_source_include.setStdIn(.{ .bytes = source_include_request });
    const cli_source_include_output = cli_source_include.captureStdOut(.{
        .basename = "oksolc-source-include.json",
    });
    const cli_source_include_check = b.addCheckFile(cli_source_include_output, .{
        .expected_matches = &.{ "\"Library.sol\"", "\"Library\"", "\"abi\":[]" },
    });
    cli_smoke_step.dependOn(&cli_source_include_check.step);

    const cli_source_denied = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_source_denied);
    dependOnValidation(&cli_source_denied.step, cli_identity_validation);
    cli_source_denied.setCwd(source_loader_cwd);
    cli_source_denied.addArgs(&.{ "--standard-json", "--base-path", "." });
    cli_source_denied.setStdIn(.{ .bytes = source_outside_request });
    const cli_source_denied_output = cli_source_denied.captureStdOut(.{
        .basename = "oksolc-source-denied.json",
    });
    const cli_source_denied_check = b.addCheckFile(cli_source_denied_output, .{
        .expected_exact = source_callback_failed ++ "\n",
    });
    cli_smoke_step.dependOn(&cli_source_denied_check.step);

    const cli_source_allowed = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_source_allowed);
    dependOnValidation(&cli_source_allowed.step, cli_identity_validation);
    cli_source_allowed.setCwd(source_loader_cwd);
    cli_source_allowed.addArgs(&.{
        "--standard-json",
        "--base-path",
        ".",
        "--allow-paths",
        "../outside",
    });
    cli_source_allowed.setStdIn(.{ .bytes = source_outside_request });
    const cli_source_allowed_output = cli_source_allowed.captureStdOut(.{
        .basename = "oksolc-source-allowed.json",
    });
    const cli_source_allowed_check = b.addCheckFile(cli_source_allowed_output, .{
        .expected_matches = &.{ "\"Secret.sol\"", "\"Secret\"", "\"abi\":[]" },
    });
    cli_smoke_step.dependOn(&cli_source_allowed_check.step);

    const source_serve_frame = b.fmt(
        "Content-Length: {d}\r\n\r\n{s}",
        .{ source_base_request.len, source_base_request },
    );
    const source_serve_disabled = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, source_serve_disabled);
    dependOnValidation(&source_serve_disabled.step, cli_identity_validation);
    source_serve_disabled.setCwd(source_loader_cwd);
    source_serve_disabled.addArgs(&.{ "serve", "--stdio" });
    source_serve_disabled.setStdIn(.{ .bytes = source_serve_frame });
    const source_serve_disabled_output = source_serve_disabled.captureStdOut(.{
        .basename = "oksolc-source-serve-disabled.txt",
    });
    const source_serve_disabled_check = b.addCheckFile(
        source_serve_disabled_output,
        .{ .expected_exact = b.fmt(
            "Content-Length: {d}\r\n\r\n{s}\n",
            .{ source_callback_unsupported.len + 1, source_callback_unsupported },
        ) },
    );
    cli_smoke_step.dependOn(&source_serve_disabled_check.step);

    const source_serve_enabled = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, source_serve_enabled);
    dependOnValidation(&source_serve_enabled.step, cli_identity_validation);
    source_serve_enabled.setCwd(source_loader_cwd);
    source_serve_enabled.addArgs(&.{ "serve", "--stdio", "--base-path", "." });
    source_serve_enabled.setStdIn(.{
        .bytes = b.fmt("{s}{s}", .{ source_serve_frame, source_serve_frame }),
    });
    const source_serve_enabled_output = source_serve_enabled.captureStdOut(.{
        .basename = "oksolc-source-serve-enabled.txt",
    });
    const source_serve_enabled_check = b.addCheckFile(source_serve_enabled_output, .{
        .expected_matches = &.{
            "Content-Length:",
            "\"Inside.sol\"",
            "\"Inside\"",
            "Content-Length:",
        },
    });
    cli_smoke_step.dependOn(&source_serve_enabled_check.step);

    const cli_project_files = b.addWriteFiles();
    _ = cli_project_files.add(
        "oksolc.toml",
        "# Generated project root for CLI persistence tests.\n" ++
            "cache-max-entries = 102400\n",
    );
    const cli_project_root = cli_project_files.getDirectory();

    const cli_cache_seed_module = b.createModule(.{
        .root_source_file = b.path("test/zig/cli/cache_seed.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{.{ .name = "solidity", .module = solidity_module }},
    });
    const cli_cache_seed = b.addExecutable(.{
        .name = "oksolc-cli-cache-seed",
        .root_module = cli_cache_seed_module,
    });
    const run_cli_cache_config = b.addRunArtifact(cli_cache_seed);
    run_cli_cache_config.has_side_effects = true;
    isolateCliSmokeEnvironment(b, run_cli_cache_config);
    enableCliSmokeCache(b, run_cli_cache_config);
    run_cli_cache_config.addArg("configure");

    const cli_cache_first = b.addRunArtifact(cli);
    cli_cache_first.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_cache_first);
    enableCliSmokeCache(b, cli_cache_first);
    dependOnValidation(&cli_cache_first.step, cli_identity_validation);
    cli_cache_first.step.dependOn(&run_cli_cache_config.step);
    cli_cache_first.addArgs(&.{ "--standard-json", "--base-path" });
    cli_cache_first.addDirectoryArg(cli_project_root);
    cli_cache_first.setStdIn(.{
        .lazy_path = b.path("test/zig/standard-json/yul-basic.json"),
    });
    const cli_cache_first_output = cli_cache_first.captureStdOut(.{
        .basename = "oksolc-cache-first.json",
    });
    const cli_cache_first_check = b.addCheckFile(cli_cache_first_output, .{
        .expected_exact = @embedFile("test/zig/standard-json/expected/yul-basic.json"),
    });
    cli_smoke_step.dependOn(&cli_cache_first_check.step);

    const cli_cache_restart = b.addRunArtifact(cli);
    cli_cache_restart.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_cache_restart);
    enableCliSmokeCache(b, cli_cache_restart);
    dependOnValidation(&cli_cache_restart.step, cli_identity_validation);
    cli_cache_restart.step.dependOn(&cli_cache_first_check.step);
    cli_cache_restart.addArgs(&.{ "--standard-json", "--base-path" });
    cli_cache_restart.addDirectoryArg(cli_project_root);
    cli_cache_restart.setStdIn(.{
        .lazy_path = b.path("test/zig/standard-json/yul-basic.json"),
    });
    const cli_cache_restart_output = cli_cache_restart.captureStdOut(.{
        .basename = "oksolc-cache-restart.json",
    });
    const cli_cache_restart_check = b.addCheckFile(cli_cache_restart_output, .{
        .expected_exact = @embedFile("test/zig/standard-json/expected/yul-basic.json"),
    });
    cli_smoke_step.dependOn(&cli_cache_restart_check.step);

    const run_cli_cache_seed = b.addRunArtifact(cli_cache_seed);
    run_cli_cache_seed.has_side_effects = true;
    isolateCliSmokeEnvironment(b, run_cli_cache_seed);
    run_cli_cache_seed.step.dependOn(&cli_cache_restart_check.step);
    run_cli_cache_seed.addArg("seed");
    run_cli_cache_seed.addDirectoryArg(cli_project_root);

    const cli_cache_stats = b.addRunArtifact(cli);
    cli_cache_stats.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_cache_stats);
    cli_cache_stats.setCwd(cli_project_root);
    dependOnValidation(&cli_cache_stats.step, cli_identity_validation);
    cli_cache_stats.step.dependOn(&run_cli_cache_seed.step);
    cli_cache_stats.addArgs(&.{ "cache", "stats" });
    const cli_cache_stats_output = cli_cache_stats.captureStdOut(.{
        .basename = "oksolc-cache-stats.json",
    });
    const cli_cache_stats_check = b.addCheckFile(cli_cache_stats_output, .{
        .expected_matches = &.{
            "\"operation\":\"stats\"",
            "\"exists\":true",
            "\"entries\":",
            "\"logical_bytes\":",
        },
    });

    const cli_cache_prune = b.addRunArtifact(cli);
    cli_cache_prune.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_cache_prune);
    cli_cache_prune.setCwd(cli_project_root);
    dependOnValidation(&cli_cache_prune.step, cli_identity_validation);
    cli_cache_prune.step.dependOn(&cli_cache_stats_check.step);
    cli_cache_prune.addArgs(&.{
        "cache",
        "--max-bytes",
        "0",
        "--max-entries",
        "0",
        "prune",
    });
    const cli_cache_prune_output = cli_cache_prune.captureStdOut(.{
        .basename = "oksolc-cache-prune.json",
    });
    const cli_cache_prune_check = b.addCheckFile(cli_cache_prune_output, .{
        .expected_matches = &.{
            "\"operation\":\"prune\"",
            "\"exists\":true",
            "\"after_entries\":0",
            "\"after_logical_bytes\":0",
        },
    });
    cli_smoke_step.dependOn(&cli_cache_prune_check.step);

    const cli_clean = b.addRunArtifact(cli);
    cli_clean.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_clean);
    cli_clean.setCwd(cli_project_root);
    dependOnValidation(&cli_clean.step, cli_identity_validation);
    cli_clean.step.dependOn(&cli_cache_prune_check.step);
    cli_clean.addArg("clean");
    const cli_clean_output = cli_clean.captureStdOut(.{
        .basename = "oksolc-clean.json",
    });
    const cli_clean_check = b.addCheckFile(cli_clean_output, .{
        .expected_matches = &.{
            "\"operation\":\"clean\"",
            "\"removed\":true",
            "/projects-v2/",
        },
    });

    const cli_clean_again = b.addRunArtifact(cli);
    cli_clean_again.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_clean_again);
    cli_clean_again.setCwd(cli_project_root);
    dependOnValidation(&cli_clean_again.step, cli_identity_validation);
    cli_clean_again.step.dependOn(&cli_clean_check.step);
    cli_clean_again.addArg("clean");
    const cli_clean_again_output = cli_clean_again.captureStdOut(.{
        .basename = "oksolc-clean-again.json",
    });
    const cli_clean_again_check = b.addCheckFile(cli_clean_again_output, .{
        .expected_matches = &.{
            "\"operation\":\"clean\"",
            "\"removed\":false",
            "/projects-v2/",
        },
    });

    const cli_cache_after_clean = b.addRunArtifact(cli);
    cli_cache_after_clean.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_cache_after_clean);
    cli_cache_after_clean.setCwd(cli_project_root);
    dependOnValidation(&cli_cache_after_clean.step, cli_identity_validation);
    cli_cache_after_clean.step.dependOn(&cli_clean_again_check.step);
    cli_cache_after_clean.addArgs(&.{ "cache", "stats" });
    const cli_cache_after_clean_output = cli_cache_after_clean.captureStdOut(.{
        .basename = "oksolc-cache-after-clean.json",
    });
    const cli_cache_after_clean_check = b.addCheckFile(cli_cache_after_clean_output, .{
        .expected_matches = &.{
            "\"operation\":\"stats\"",
            "\"exists\":false",
            "/projects-v2/",
            "/artifacts.sqlite",
        },
    });
    cli_smoke_step.dependOn(&cli_cache_after_clean_check.step);

    const cli_no_cache = b.addRunArtifact(cli);
    cli_no_cache.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_no_cache);
    dependOnValidation(&cli_no_cache.step, cli_identity_validation);
    cli_no_cache.step.dependOn(&cli_cache_after_clean_check.step);
    cli_no_cache.addArgs(&.{ "--standard-json", "--no-cache", "--base-path" });
    cli_no_cache.addDirectoryArg(cli_project_root);
    cli_no_cache.setStdIn(.{
        .lazy_path = b.path("test/zig/standard-json/yul-basic.json"),
    });
    const cli_no_cache_output = cli_no_cache.captureStdOut(.{
        .basename = "oksolc-no-cache.json",
    });
    const cli_no_cache_check = b.addCheckFile(cli_no_cache_output, .{
        .expected_exact = @embedFile("test/zig/standard-json/expected/yul-basic.json"),
    });

    const cli_no_cache_stats = b.addRunArtifact(cli);
    cli_no_cache_stats.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_no_cache_stats);
    cli_no_cache_stats.setCwd(cli_project_root);
    dependOnValidation(&cli_no_cache_stats.step, cli_identity_validation);
    cli_no_cache_stats.step.dependOn(&cli_no_cache_check.step);
    cli_no_cache_stats.addArgs(&.{ "cache", "stats" });
    const cli_no_cache_stats_output = cli_no_cache_stats.captureStdOut(.{
        .basename = "oksolc-no-cache-stats.json",
    });
    const cli_no_cache_stats_check = b.addCheckFile(cli_no_cache_stats_output, .{
        .expected_matches = &.{
            "\"operation\":\"stats\"",
            "\"exists\":false",
            "/projects-v2/",
            "/artifacts.sqlite",
        },
    });
    cli_smoke_step.dependOn(&cli_no_cache_stats_check.step);

    const cli_config_no_cache_files = b.addWriteFiles();
    _ = cli_config_no_cache_files.add(
        "oksolc.toml",
        "# Repository configuration cannot opt into persistent caching.\n" ++
            "cache = true\n",
    );
    _ = cli_config_no_cache_files.add(
        ".oksolc/artifacts.sqlite",
        "attacker-controlled repository database that must never be opened",
    );
    const cli_config_no_cache_root = cli_config_no_cache_files.getDirectory();

    const cli_config_no_cache_clean = b.addRunArtifact(cli);
    cli_config_no_cache_clean.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_config_no_cache_clean);
    cli_config_no_cache_clean.setCwd(cli_config_no_cache_root);
    dependOnValidation(&cli_config_no_cache_clean.step, cli_identity_validation);
    cli_config_no_cache_clean.addArg("clean");
    const cli_config_no_cache_clean_output = cli_config_no_cache_clean.captureStdOut(.{
        .basename = "oksolc-config-no-cache-clean.json",
    });
    const cli_config_no_cache_clean_check = b.addCheckFile(
        cli_config_no_cache_clean_output,
        .{ .expected_matches = &.{"\"operation\":\"clean\""} },
    );

    const cli_config_no_cache = b.addRunArtifact(cli);
    cli_config_no_cache.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_config_no_cache);
    dependOnValidation(&cli_config_no_cache.step, cli_identity_validation);
    cli_config_no_cache.step.dependOn(&cli_config_no_cache_clean_check.step);
    cli_config_no_cache.addArgs(&.{ "--standard-json", "--base-path" });
    cli_config_no_cache.addDirectoryArg(cli_config_no_cache_root);
    cli_config_no_cache.setStdIn(.{
        .lazy_path = b.path("test/zig/standard-json/yul-basic.json"),
    });
    const cli_config_no_cache_output = cli_config_no_cache.captureStdOut(.{
        .basename = "oksolc-config-no-cache.json",
    });
    const cli_config_no_cache_check = b.addCheckFile(cli_config_no_cache_output, .{
        .expected_exact = @embedFile("test/zig/standard-json/expected/yul-basic.json"),
    });

    const cli_config_no_cache_stats = b.addRunArtifact(cli);
    cli_config_no_cache_stats.has_side_effects = true;
    isolateCliSmokeEnvironment(b, cli_config_no_cache_stats);
    cli_config_no_cache_stats.setCwd(cli_config_no_cache_root);
    dependOnValidation(&cli_config_no_cache_stats.step, cli_identity_validation);
    cli_config_no_cache_stats.step.dependOn(&cli_config_no_cache_check.step);
    cli_config_no_cache_stats.addArgs(&.{ "cache", "stats" });
    const cli_config_no_cache_stats_output = cli_config_no_cache_stats.captureStdOut(.{
        .basename = "oksolc-config-no-cache-stats.json",
    });
    const cli_config_no_cache_stats_check = b.addCheckFile(
        cli_config_no_cache_stats_output,
        .{ .expected_matches = &.{
            "\"operation\":\"stats\"",
            "\"exists\":false",
            "/projects-v2/",
            "/artifacts.sqlite",
        } },
    );
    cli_smoke_step.dependOn(&cli_config_no_cache_stats_check.step);

    const serve_request = @embedFile("test/zig/standard-json/yul-basic.json");
    const serve_response = @embedFile("test/zig/standard-json/expected/yul-basic.json");
    const serve_request_frame = b.fmt(
        "Content-Length: {d}\r\n\r\n{s}",
        .{ serve_request.len, serve_request },
    );
    const serve_response_frame = b.fmt(
        "Content-Length: {d}\r\n\r\n{s}",
        .{ serve_response.len, serve_response },
    );
    const cli_serve_command = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_serve_command);
    dependOnValidation(&cli_serve_command.step, cli_identity_validation);
    cli_serve_command.addArgs(&.{ "serve", "--stdio" });
    cli_serve_command.setStdIn(.{
        .bytes = b.fmt("{s}{s}", .{ serve_request_frame, serve_request_frame }),
    });
    const cli_serve_output = cli_serve_command.captureStdOut(.{
        .basename = "oksolc-serve.json",
    });
    const cli_serve_check = b.addCheckFile(cli_serve_output, .{
        .expected_exact = b.fmt(
            "{s}{s}",
            .{ serve_response_frame, serve_response_frame },
        ),
    });
    cli_smoke_step.dependOn(&cli_serve_check.step);

    const cli_watch_command = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_watch_command);
    dependOnValidation(&cli_watch_command.step, cli_identity_validation);
    cli_watch_command.addArgs(&.{
        "watch",
        "--once",
        "test/zig/standard-json/yul-basic.json",
    });
    const cli_watch_output = cli_watch_command.captureStdOut(.{
        .basename = "oksolc-watch.json",
    });
    const cli_watch_check = b.addCheckFile(cli_watch_output, .{
        .expected_exact = serve_response,
    });
    cli_smoke_step.dependOn(&cli_watch_check.step);

    const cli_progress_command = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_progress_command);
    dependOnValidation(&cli_progress_command.step, cli_identity_validation);
    cli_progress_command.addArgs(&.{
        "standard-json",
        "--progress",
        "test/zig/standard-json/yul-basic.json",
    });
    const cli_progress_output = cli_progress_command.captureStdOut(.{
        .basename = "oksolc-progress-standard-json.json",
    });
    const cli_progress_check = b.addCheckFile(cli_progress_output, .{
        .expected_exact = @embedFile("test/zig/standard-json/expected/yul-basic.json"),
    });
    cli_smoke_step.dependOn(&cli_progress_check.step);

    const compare_ir_output = b.addExecutable(.{
        .name = "compare-ir-output",
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/zig/compare_ir_output.zig"),
            .target = b.graph.host,
            .optimize = .ReleaseSafe,
            .imports = &.{.{ .name = "solidity", .module = solidity_module }},
        }),
    });

    for ([_][]const u8{ "1", "4" }) |jobs| {
        const cli_parallel_command = b.addRunArtifact(cli);
        isolateCliSmokeEnvironment(b, cli_parallel_command);
        dependOnValidation(&cli_parallel_command.step, cli_identity_validation);
        cli_parallel_command.addArgs(&.{
            "standard-json",
            "--parallel",
            "--jobs",
            jobs,
            "test/zig/standard-json/via-ir-smoke.json",
        });
        const cli_parallel_output = cli_parallel_command.captureStdOut(.{
            .basename = b.fmt("oksolc-parallel-{s}-standard-json.json", .{jobs}),
        });
        const cli_parallel_check = b.addRunArtifact(compare_ir_output);
        cli_parallel_check.addFileArg(b.path("test/zig/standard-json/expected/via-ir-smoke.json"));
        cli_parallel_check.addFileArg(cli_parallel_output);
        cli_smoke_step.dependOn(&cli_parallel_check.step);
    }

    const cli_compile_command = b.addRunArtifact(cli);
    isolateCliSmokeEnvironment(b, cli_compile_command);
    dependOnValidation(&cli_compile_command.step, cli_identity_validation);
    cli_compile_command.addArgs(&.{ "compile", "test/zig/cli/C.sol" });
    const cli_compile_output = cli_compile_command.captureStdOut(.{
        .basename = "oksolc-compile.json",
    });
    const cli_compile_check = b.addCheckFile(cli_compile_output, .{
        .expected_matches = &.{
            "\"test/zig/cli/C.sol\":{\"C\":{\"abi\":",
            "\"evm\":{\"bytecode\":{\"object\":",
            "\"deployedBytecode\":{\"object\":",
            "\\\"viaIR\\\":true",
        },
    });
    cli_smoke_step.dependOn(&cli_compile_check.step);

    for ([_][]const []const u8{
        &.{ "analyze", "test/zig/cli/C.sol" },
        &.{ "compile", "--abstract-interpretation", "test/zig/cli/C.sol" },
        &.{ "standard-json", "--abstract-interpretation" },
        &.{ "serve", "--analysis-config", "analysis.json" },
        &.{ "browse", "--forge", "test/zig/cli/C.sol" },
    }) |arguments| {
        const removed_analysis = b.addRunArtifact(cli);
        isolateCliSmokeEnvironment(b, removed_analysis);
        dependOnValidation(&removed_analysis.step, cli_identity_validation);
        removed_analysis.addArgs(arguments);
        removed_analysis.expectExitCode(1);
        _ = removed_analysis.captureStdErr(.{});
        cli_smoke_step.dependOn(&removed_analysis.step);
    }

    const libsolc_c_smoke_module = b.createModule(.{
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });
    libsolc_c_smoke_module.addIncludePath(b.path("include"));
    libsolc_c_smoke_module.addCSourceFile(.{
        .file = b.path("test/zig/libsolc_c_smoke.c"),
        .flags = &.{"-std=c99"},
    });
    const libsolc_c_smoke = b.addExecutable(.{
        .name = "libsolc-c-smoke",
        .root_module = libsolc_c_smoke_module,
    });
    libsolc_c_smoke_module.linkLibrary(libsolc_library);
    const run_libsolc_c_smoke = b.addRunArtifact(libsolc_c_smoke);
    dependOnValidation(&run_libsolc_c_smoke.step, libsolc_identity_validation);
    const libsolc_c_smoke_step = b.step(
        "libsolc-c-smoke",
        "Compile and exercise the libsolc C ABI",
    );
    libsolc_c_smoke_step.dependOn(&run_libsolc_c_smoke.step);

    const check_step = b.step("check", "Compile the compiler, CLI, and all tests");
    check_step.dependOn(&libsolc_library.step);
    check_step.dependOn(&cli.step);
    dependOnValidation(check_step, libsolc_identity_validation);
    dependOnValidation(check_step, cli_identity_validation);
    check_step.dependOn(cli_smoke_step);
    check_step.dependOn(libsolc_c_smoke_step);

    const test_step = b.step("test", "Run all Zig tests and smoke tests");
    test_step.dependOn(check_step);
    const terminal_probe = b.addExecutable(.{
        .name = "common-io-terminal-probe",
        .root_module = b.createModule(.{
            .root_source_file = b.path("test/zig/common_io_terminal_probe.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
            .imports = &.{.{ .name = "common_io", .module = b.createModule(.{
                .root_source_file = b.path("src/libsolutil/common_io.zig"),
                .target = target,
                .optimize = optimize,
            }) }},
        }),
    });
    const terminal_smoke = b.addSystemCommand(&.{"python3"});
    terminal_smoke.addFileArg(b.path("test/zig/common_io_terminal_smoke.py"));
    terminal_smoke.addArtifactArg(terminal_probe);
    b.step("common-io-terminal-smoke", "Test terminal input and mode restoration").dependOn(&terminal_smoke.step);
    test_step.dependOn(&terminal_smoke.step);
    const compatibility_step = b.step(
        "compatibility-check",
        "Compare clean compiler bytes with the frozen solc 0.8.36 corpus",
    );
    const fuzz_step = b.step(
        "fuzz",
        "Run compiler fuzz targets (use --fuzz=<iterations> for a longer run)",
    );
    const fuzz_parser_step = b.step(
        "fuzz-parser",
        "Run the Solidity parser fuzz target",
    );
    const fuzz_json_step = b.step(
        "fuzz-json",
        "Run the strict JSON parser fuzz target",
    );
    const fuzz_standard_json_step = b.step(
        "fuzz-standard-json",
        "Fuzz the public Standard JSON C ABI and dispatcher",
    );
    const fuzz_adapter_step = b.step(
        "fuzz-json-adapter",
        "Mutation-fuzz the yyjson C adapter with ASan and UBSan",
    );
    const test_modules = [_]*std.Build.Module{
        big_int_module,
        common_module,
        cxx_compat_module,
        compiler_module,
        solidity_module,
        cli_module,
        standard_json_dispatch_module,
        incremental_edit_trace_module,
    };
    for (test_modules) |module| {
        const tests = b.addTest(.{ .root_module = module });
        tests.stack_size = 32 * 1024 * 1024;
        check_step.dependOn(&tests.step);
        const identity_validation = addCompilerBuildIdentityValidation(
            b,
            tests,
            compiler_build_validation_identity,
        );
        dependOnValidation(check_step, identity_validation);
        const run_tests = b.addRunArtifact(tests);
        dependOnValidation(&run_tests.step, identity_validation);
        test_step.dependOn(&run_tests.step);
        if (module == cli_module)
            b.step("test-cli", "Run CLI unit tests").dependOn(&run_tests.step);
    }

    const evm_tests = b.addTest(.{ .root_module = b.createModule(.{
        .root_source_file = b.path("src/libevm.zig"),
        .target = target,
        .optimize = optimize,
    }) });
    b.step("test-evm", "Run shared EVM semantics tests").dependOn(&b.addRunArtifact(evm_tests).step);

    const ownership_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/ownership_tests.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
            .imports = &.{
                .{ .name = "build_options", .module = build_options_module },
                .{ .name = "big_int", .module = big_int_module },
                .{ .name = "common", .module = common_module },
                .{ .name = "cxx_compat", .module = cxx_compat_module },
            },
        }),
        .filters = &.{ "ownership test inventory", "assembly inliner", "label ID dispenser", "peephole", "assembly CSE", "assembly immutable", "assembly append", "backend scratch", "stack diagnostic", "function grouper", "source locations", "source snippets", "escaped string content", "function specializer", "function analysis cache", "optimizer scratch retention", "optimizer debug snapshots", "name simplifier", "IR variable", "IR source", "SSA transform", "SSA reverser", "Yul stack owned printing", "Yul AST generated object", "assembly printing", "contract artifact", "statement remover", "profiler ", "for-loop init rewriter", "structural simplifier", "expression joiner", "expression splitter", "loop-invariant", "block flattener", "full inliner", "inline declarations", "linker ", "append rebases", "expression classes", "nested logical", "printing ", "CFG lowering", "transient optimizer", "unused store", "unused assignment", "unused parameter", "variable name cleaner", "conditional simplifier" },
    });
    ownership_tests.stack_size = 32 * 1024 * 1024;
    check_step.dependOn(&ownership_tests.step);
    const run_ownership_tests = b.addRunArtifact(ownership_tests);
    test_step.dependOn(&run_ownership_tests.step);
    b.step("test-ownership", "Test compiler allocation failures and ownership transfers").dependOn(&run_ownership_tests.step);

    const structured_yul_step = b.step("test-structured-yul", "Test structured Yul ownership and solc artifact compatibility");
    structured_yul_step.dependOn(&run_ownership_tests.step);
    const yul_construction_tests = b.addTest(.{
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/yul_construction_tests.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
            .imports = &.{
                .{ .name = "build_options", .module = build_options_module },
                .{ .name = "big_int", .module = big_int_module },
                .{ .name = "common", .module = common_module },
                .{ .name = "cxx_compat", .module = cxx_compat_module },
            },
        }),
        .filters = &.{"Yul AST"},
    });
    // Corrupt-cache tests exercise the decoder's 1,200-level recursion guard.
    yul_construction_tests.stack_size = 32 * 1024 * 1024;
    const run_yul_construction = b.addRunArtifact(yul_construction_tests);
    b.step("test-yul-construction", "Test typed Yul construction independently of compiler integration").dependOn(&run_yul_construction.step);
    structured_yul_step.dependOn(&run_yul_construction.step);
    check_step.dependOn(&yul_construction_tests.step);
    test_step.dependOn(&run_yul_construction.step);
    const structured_yul_tests = b.addTest(.{
        .root_module = compiler_module,
        .filters = &.{ "compiler module inventory", "source locations", "source snippets", "escaped string content", "Yul AST builder", "Yul AST template", "printer renders", "Yul stack", "AST copier", "object code transfer", "stack compression", "stack limit eva", "disambiguator", "function specializer", "object optimizer", "compiler session propagates cache OOM", "backend cache", "code size warnings", "structured Yul", "compiler session reloads optimized Yul", "compiler session reuses backend layers", "Yul simplification", "expression simplifier", "constant EVM arithmetic", "expression classes" },
    });
    structured_yul_tests.stack_size = 32 * 1024 * 1024;
    structured_yul_step.dependOn(&b.addRunArtifact(structured_yul_tests).step);
    const structured_yul_artifact_tests = b.addTest(.{
        .root_module = standard_json_dispatch_module,
        .filters = &.{"parallel "},
    });
    const run_structured_yul_artifact_tests = b.addRunArtifact(structured_yul_artifact_tests);
    structured_yul_step.dependOn(&run_structured_yul_artifact_tests.step);
    b.step("test-parallel-artifacts", "Test artifact ownership, parallel output and retained-storage profiling").dependOn(&run_structured_yul_artifact_tests.step);

    const sqlite_tests = b.addTest(.{
        .name = "sqlite-store",
        .root_module = compiler_module,
        .filters = &.{ "compiler module inventory", "SQLite" },
    });
    const run_sqlite_tests = b.addRunArtifact(sqlite_tests);
    dependOnValidation(&run_sqlite_tests.step, addCompilerBuildIdentityValidation(b, sqlite_tests, compiler_build_validation_identity));
    b.step("test-sqlite", "Run SQLite storage and compiler-session tests").dependOn(&run_sqlite_tests.step);

    const browser_store_module = b.createModule(.{
        .root_source_file = b.path("src/cli/browser/store.zig"),
        .target = target,
        .optimize = optimize,
        .imports = &.{
            .{ .name = "zqlite", .module = zqlite_module },
            .{ .name = "solidity", .module = solidity_module },
        },
    });
    const browser_store_tests = b.addTest(.{ .root_module = browser_store_module });
    b.step("test-browser-store", "Run compiler-output SQL indexing tests").dependOn(&b.addRunArtifact(browser_store_tests).step);

    const reference_corpus_tests = b.addTest(.{
        .name = "frozen-solc-compatibility",
        .root_module = reference_corpus_module,
    });
    check_step.dependOn(&reference_corpus_tests.step);
    const reference_corpus_validation = addCompilerBuildIdentityValidation(
        b,
        reference_corpus_tests,
        compiler_build_validation_identity,
    );
    dependOnValidation(check_step, reference_corpus_validation);
    const run_reference_corpus_tests = b.addRunArtifact(reference_corpus_tests);
    dependOnValidation(
        &run_reference_corpus_tests.step,
        reference_corpus_validation,
    );
    test_step.dependOn(&run_reference_corpus_tests.step);
    compatibility_step.dependOn(&run_reference_corpus_tests.step);

    const parser_fuzz_tests = b.addTest(.{
        .name = "parser-fuzz",
        .root_module = parser_fuzz_module,
        .filters = &.{"fuzz bounded Solidity source parsing"},
    });
    check_step.dependOn(&parser_fuzz_tests.step);
    const parser_fuzz_validation = addCompilerBuildIdentityValidation(
        b,
        parser_fuzz_tests,
        compiler_build_validation_identity,
    );
    dependOnValidation(check_step, parser_fuzz_validation);
    const run_parser_fuzz_tests = b.addRunArtifact(parser_fuzz_tests);
    dependOnValidation(&run_parser_fuzz_tests.step, parser_fuzz_validation);
    test_step.dependOn(&run_parser_fuzz_tests.step);
    fuzz_step.dependOn(&run_parser_fuzz_tests.step);
    fuzz_parser_step.dependOn(&run_parser_fuzz_tests.step);

    const json_fuzz_tests = b.addTest(.{
        .name = "json-fuzz",
        .root_module = json_fuzz_module,
        .filters = &.{"fuzz bounded strict JSON parsing"},
    });
    check_step.dependOn(&json_fuzz_tests.step);
    const json_fuzz_validation = addCompilerBuildIdentityValidation(
        b,
        json_fuzz_tests,
        compiler_build_validation_identity,
    );
    dependOnValidation(check_step, json_fuzz_validation);
    const run_json_fuzz_tests = b.addRunArtifact(json_fuzz_tests);
    dependOnValidation(&run_json_fuzz_tests.step, json_fuzz_validation);
    test_step.dependOn(&run_json_fuzz_tests.step);
    fuzz_step.dependOn(&run_json_fuzz_tests.step);
    fuzz_json_step.dependOn(&run_json_fuzz_tests.step);

    const standard_json_fuzz_tests = b.addTest(.{
        .name = "standard-json-fuzz",
        .root_module = standard_json_fuzz_module,
        .filters = &.{"fuzz bounded public Standard JSON compilation"},
    });
    check_step.dependOn(&standard_json_fuzz_tests.step);
    const standard_json_fuzz_validation = addCompilerBuildIdentityValidation(
        b,
        standard_json_fuzz_tests,
        compiler_build_validation_identity,
    );
    dependOnValidation(check_step, standard_json_fuzz_validation);
    const run_standard_json_fuzz_tests = b.addRunArtifact(standard_json_fuzz_tests);
    dependOnValidation(
        &run_standard_json_fuzz_tests.step,
        standard_json_fuzz_validation,
    );
    test_step.dependOn(&run_standard_json_fuzz_tests.step);
    fuzz_step.dependOn(&run_standard_json_fuzz_tests.step);
    fuzz_standard_json_step.dependOn(&run_standard_json_fuzz_tests.step);

    const compile_adapter_fuzzer = b.addSystemCommand(&.{
        "clang",
        "-std=c99",
        "-g",
        "-O1",
        "-fno-omit-frame-pointer",
        "-fsanitize=address,undefined",
        "-fno-sanitize-recover=all",
        "-Dyyjson_api=",
    });
    compile_adapter_fuzzer.addPrefixedDirectoryArg("-I", b.path("include"));
    compile_adapter_fuzzer.addPrefixedDirectoryArg(
        "-I",
        yyjson_dependency.path("src"),
    );
    compile_adapter_fuzzer.addFileArg(b.path("src/fuzz_json_adapter.c"));
    compile_adapter_fuzzer.addFileArg(b.path("src/libsolc/yyjson_adapter.c"));
    compile_adapter_fuzzer.addFileArg(yyjson_dependency.path("src/yyjson.c"));
    compile_adapter_fuzzer.addArg("-o");
    const adapter_fuzzer_binary = compile_adapter_fuzzer.addOutputFileArg(
        "json-adapter-fuzzer",
    );
    const run_adapter_fuzzer = b.addSystemCommand(&.{"/usr/bin/env"});
    run_adapter_fuzzer.setEnvironmentVariable(
        "ASAN_OPTIONS",
        "halt_on_error=1",
    );
    run_adapter_fuzzer.setEnvironmentVariable(
        "UBSAN_OPTIONS",
        "halt_on_error=1:print_stacktrace=1",
    );
    run_adapter_fuzzer.addFileArg(adapter_fuzzer_binary);
    run_adapter_fuzzer.addArg(b.fmt("{d}", .{adapter_fuzz_runs}));
    run_adapter_fuzzer.addArg(b.fmt("{d}", .{adapter_fuzz_seed}));
    inline for (.{
        "content.json",
        "callback.json",
        "duplicates.json",
        "source-limit.seed",
        "source-limit-exceeded.seed",
    }) |seed_name| {
        run_adapter_fuzzer.addFileArg(b.path(b.fmt(
            "test/fuzz/json-adapter-corpus/{s}",
            .{seed_name},
        )));
    }
    fuzz_step.dependOn(&run_adapter_fuzzer.step);
    fuzz_adapter_step.dependOn(&run_adapter_fuzzer.step);

    const fmt_check = b.addSystemCommand(&.{
        "zig",
        "fmt",
        "--check",
        "build.zig",
        "src",
        "test/zig",
        "test/benchmarks",
    });
    const fmt_check_step = b.step("fmt-check", "Check Zig formatting");
    fmt_check_step.dependOn(&fmt_check.step);

    const lint_step = b.step("lint", "Lint Zig source");
    lint_step.dependOn(step: {
        var builder = zlinter.builder(b, .{ .optimize = .ReleaseFast });
        builder.addRule(.{ .builtin = .no_deprecated }, .{ .severity = .@"error" });
        builder.addRule(.{ .builtin = .no_hidden_allocations }, .{ .severity = .@"error" });
        builder.addRule(.{ .builtin = .no_orelse_unreachable }, .{ .severity = .@"error" });
        builder.addRule(.{ .builtin = .no_swallow_error }, .{
            .detect_catch_unreachable = .@"error",
            .detect_empty_catch = .@"error",
            .detect_empty_else = .@"error",
            .detect_else_unreachable = .@"error",
        });
        builder.addRule(.{ .builtin = .no_unused }, .{ .container_declaration = .@"error" });
        builder.addRule(.{ .builtin = .require_errdefer_dealloc }, .{ .severity = .@"error" });
        builder.addPaths(.{
            .include = &.{
                b.path("build.zig"),
                b.path("src"),
                b.path("test/zig"),
                b.path("test/benchmarks"),
            },
        });
        break :step builder.build();
    });

    addReferenceCheck(b, reference_solc);
    addBenchmarks(
        b,
        target,
        optimize,
        benchmark_runs,
        benchmark_warmups,
        reference_solc,
        cli,
        cli_identity_validation,
        cxx_compat_module,
        optimizer_workloads_module,
        solidity_module,
        incremental_edit_trace_module,
        compiler_build_validation_identity,
    );
}

const DetectedCompilerBuild = struct {
    identity: []const u8 = "unidentified",
    available: bool = false,
    validation_identity: ?[]const u8 = null,
};

/// Hash actual compiler inputs, including uncommitted and source-archive
/// contents. Product assets, documentation and Git metadata are not inputs.
fn detectCompilerBuildIdentity(b: *std.Build) DetectedCompilerBuild {
    const identity = @import("build_support/compiler_identity.zig").digest(b.allocator, b.graph.io, b.build_root.handle) catch return .{};
    const owned = b.dupe(&identity);
    return .{ .identity = owned, .available = true, .validation_identity = owned };
}

fn addCompilerBuildIdentityValidation(
    b: *std.Build,
    artifact: *std.Build.Step.Compile,
    expected_identity: ?[]const u8,
) ?*std.Build.Step {
    const identity = expected_identity orelse return null;
    const validator = b.addExecutable(.{
        .name = "oksolc-compiler-identity",
        .root_module = b.createModule(.{
            .root_source_file = b.path("build_support/compiler_identity.zig"),
            .target = b.graph.host,
            .optimize = .ReleaseSafe,
        }),
    });
    const validation = b.addRunArtifact(validator);
    validation.has_side_effects = true;
    validation.addArg(b.pathFromRoot("."));
    validation.addArg(identity);
    validation.setName(b.fmt("validate {s} compiler content identity", .{artifact.name}));
    validation.step.dependOn(&artifact.step);
    return &validation.step;
}

fn dependOnValidation(step: *std.Build.Step, validation: ?*std.Build.Step) void {
    if (validation) |dependency| step.dependOn(dependency);
}

fn isolateCliSmokeEnvironment(b: *std.Build, run: *std.Build.Step.Run) void {
    run.setEnvironmentVariable(
        "XDG_CONFIG_HOME",
        b.pathFromRoot("test/zig/cli/config-home"),
    );
    run.setEnvironmentVariable(
        "OKSOLC_CACHE_AUTH_KEY",
        "5a" ** 32,
    );
    run.setEnvironmentVariable(
        "XDG_CACHE_HOME",
        b.pathFromRoot(b.graph.global_cache_root.join(
            b.allocator,
            &.{"oksolc-cli-smoke-cache-v2"},
        ) catch @panic("out of memory")),
    );
}

fn enableCliSmokeCache(b: *std.Build, run: *std.Build.Step.Run) void {
    run.setEnvironmentVariable(
        "XDG_CONFIG_HOME",
        b.pathFromRoot(b.graph.global_cache_root.join(
            b.allocator,
            &.{"oksolc-cli-smoke-config-v2"},
        ) catch @panic("out of memory")),
    );
}

fn addReferenceCheck(b: *std.Build, reference_solc: []const u8) void {
    const reference_check_step = b.step(
        "reference-check",
        "Audit frozen outputs against a local solc 0.8.36 executable",
    );
    const version_command = b.addSystemCommand(&.{ reference_solc, "--version" });
    const version_output = version_command.captureStdOut(.{
        .basename = "solc-version.txt",
    });
    const version_check = b.addCheckFile(version_output, .{
        .expected_matches = &.{"Version: 0.8.36"},
    });
    version_check.setName("verify system solc version");
    reference_check_step.dependOn(&version_check.step);

    const cases = .{
        .{
            .id = "empty-sources",
            .input = "test/zig/standard-json/empty-sources.json",
            .expected = @embedFile("test/zig/standard-json/expected/empty-sources.json"),
        },
        .{
            .id = "solidity-abi",
            .input = "test/zig/standard-json/solidity-abi.json",
            .expected = @embedFile("test/zig/standard-json/expected/solidity-abi.json"),
        },
        .{
            .id = "via-ir-smoke",
            .input = "test/zig/standard-json/via-ir-smoke.json",
            .expected = @embedFile("test/zig/standard-json/expected/via-ir-smoke.json"),
        },
        .{
            .id = "parser-error",
            .input = "test/zig/standard-json/parser-error.json",
            .expected = @embedFile("test/zig/standard-json/expected/parser-error.json"),
        },
        .{
            .id = "type-error",
            .input = "test/zig/standard-json/type-error.json",
            .expected = @embedFile("test/zig/standard-json/expected/type-error.json"),
        },
    };
    inline for (cases) |case| {
        const command = b.addSystemCommand(&.{ reference_solc, "--standard-json" });
        command.step.dependOn(&version_check.step);
        command.setStdIn(.{ .lazy_path = b.path(case.input) });
        const output = command.captureStdOut(.{
            .basename = b.fmt("{s}.json", .{case.id}),
        });
        const output_check = b.addCheckFile(output, .{
            .expected_exact = case.expected,
        });
        output_check.setName(b.fmt("compare {s} reference output", .{case.id}));
        reference_check_step.dependOn(&output_check.step);
    }
}

fn addBenchmarks(
    b: *std.Build,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    benchmark_runs: u32,
    benchmark_warmups: u32,
    reference_solc: []const u8,
    cli: *std.Build.Step.Compile,
    cli_identity_validation: ?*std.Build.Step,
    cxx_compat_module: *std.Build.Module,
    optimizer_workloads_module: *std.Build.Module,
    solidity_module: *std.Build.Module,
    incremental_edit_trace_module: *std.Build.Module,
    compiler_build_validation_identity: ?[]const u8,
) void {
    const benchmark_local_step = b.step(
        "benchmark-local",
        "Compare ReleaseFast oksolc with system solc on three local fixtures",
    );
    if (benchmarkGuard(b, benchmark_local_step, target, optimize, benchmark_runs)) {
        const benchmark_local = b.addSystemCommand(&.{
            "python3",
            "test/benchmarks/compare.py",
            "--reference-solc",
            reference_solc,
            "--zig-solc",
        });
        benchmark_local.addArtifactArg(cli);
        dependOnValidation(&benchmark_local.step, cli_identity_validation);
        benchmark_local.addArgs(&.{
            "--runs",
            b.fmt("{d}", .{benchmark_runs}),
            "--warmups",
            b.fmt("{d}", .{benchmark_warmups}),
            "--require-exact-output",
            "--output",
            "build/benchmarks/local.json",
            "--summary-output",
            "build/benchmarks/local-summary.json",
        });
        benchmark_local_step.dependOn(&benchmark_local.step);
    }

    const benchmark_zbench_step = b.step(
        "benchmark-zbench",
        "Run zBench after the three-case system-solc parity gate",
    );
    const benchmark_zbench_only_step = b.step(
        "benchmark-zbench-only",
        "Run zBench without the system-solc parity gate",
    );
    const zbench_enabled = benchmarkGuard(
        b,
        benchmark_zbench_step,
        target,
        optimize,
        1,
    );
    const zbench_only_enabled = benchmarkGuard(
        b,
        benchmark_zbench_only_step,
        target,
        optimize,
        1,
    );
    if (zbench_enabled and zbench_only_enabled) {
        const zbench_dependency = b.dependency("zbench", .{
            .target = target,
            .optimize = optimize,
        });
        const zbench_library = zbench_dependency.artifact("zbench");
        const zbench_module = b.createModule(.{
            .root_source_file = b.path("test/benchmarks/zbench.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "cxx_compat", .module = cxx_compat_module },
                .{ .name = "optimizer_workloads", .module = optimizer_workloads_module },
                .{ .name = "solidity", .module = solidity_module },
                .{ .name = "zbench", .module = zbench_library.root_module },
            },
        });
        const zbench_executable = b.addExecutable(.{
            .name = "oksolc-zbench",
            .root_module = zbench_module,
        });
        const zbench_identity_validation = addCompilerBuildIdentityValidation(
            b,
            zbench_executable,
            compiler_build_validation_identity,
        );
        const run_zbench = b.addRunArtifact(zbench_executable);
        dependOnValidation(&run_zbench.step, zbench_identity_validation);
        run_zbench.addArgs(&.{ "--json", "build/benchmarks/zbench.json", "--counters" });
        run_zbench.step.dependOn(benchmark_local_step);
        benchmark_zbench_step.dependOn(&run_zbench.step);

        const run_zbench_only = b.addRunArtifact(zbench_executable);
        dependOnValidation(&run_zbench_only.step, zbench_identity_validation);
        run_zbench_only.addArgs(&.{ "--json", "build/benchmarks/zbench.json", "--counters" });
        benchmark_zbench_only_step.dependOn(&run_zbench_only.step);
    }

    const benchmark_incremental_step = b.step(
        "benchmark-incremental",
        "Run byte-exact incremental edit traces and record cache metrics",
    );
    if (benchmarkGuard(b, benchmark_incremental_step, target, optimize, 1)) {
        const benchmark_incremental_executable = b.addExecutable(.{
            .name = "oksolc-incremental-benchmark",
            .root_module = incremental_edit_trace_module,
        });
        const identity_validation = addCompilerBuildIdentityValidation(
            b,
            benchmark_incremental_executable,
            compiler_build_validation_identity,
        );
        const benchmark_incremental = b.addRunArtifact(benchmark_incremental_executable);
        dependOnValidation(&benchmark_incremental.step, identity_validation);
        benchmark_incremental.addArgs(&.{
            "--output",
            "build/benchmarks/incremental-edit-trace.json",
        });
        benchmark_incremental_step.dependOn(&benchmark_incremental.step);
    }
}

fn benchmarkGuard(
    b: *std.Build,
    step: *std.Build.Step,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    runs: u32,
) bool {
    if (optimize != .ReleaseFast) {
        step.dependOn(&b.addFail("benchmark requires -Doptimize=ReleaseFast").step);
        return false;
    }
    if (!target.query.isNative()) {
        step.dependOn(&b.addFail("benchmark requires a native target").step);
        return false;
    }
    if (runs == 0) {
        step.dependOn(&b.addFail("benchmark runs must be greater than zero").step);
        return false;
    }
    return true;
}
