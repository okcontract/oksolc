// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");
const builtin = @import("builtin");
const zlinter = @import("zlinter");
const CompilerHeader = @import("build_support/compiler_header.zig");
const CompilerIdentity = @import("build_support/compiler_identity.zig");
const package = @import("build.zig.zon");

const required_zig_version: std.SemanticVersion = .{
    .major = 0,
    .minor = 17,
    .patch = 0,
};

comptime {
    if (builtin.zig_version.order(required_zig_version) != .eq) {
        @compileError(
            "solidity-zig requires Zig 0.17.0; found " ++
                builtin.zig_version_string,
        );
    }
}

pub fn build(b: *std.Build) !void {
    const lint_worker = b.option(
        bool,
        "lint-worker",
        "Internal: configure zlinter in a separate build process",
    ) orelse false;
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const browser_enabled = b.option(
        bool,
        "browser",
        "Include the web browser (requires Bun and TypeScript)",
    ) orelse false;
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
        "Number of untimed warmup runs per compiler and benchmark workload",
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
    const compiler_build_validation_identity = CompilerIdentity.create(b, compiler_build_identity_override);

    const build_options = b.addOptions();
    build_options.addOption([]const u8, "oksolc_version", package.version);
    build_options.addOption([]const u8, "license_text", @embedFile("LICENSE.txt"));
    build_options.addOption(
        []const u8,
        "third_party_licenses",
        @embedFile("THIRD_PARTY_LICENSES.txt"),
    );
    const build_options_module = b.createModule(.{
        .root_source_file = b.path("build_support/build_options.zig"),
        .imports = &.{.{ .name = "package_options", .module = build_options.createModule() }},
    });
    build_options_module.addAnonymousImport("compiler_identity", .{
        .root_source_file = compiler_build_validation_identity.file,
    });

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
    const translate_c = b.dependency("translate_c", .{
        .target = b.graph.host,
        .optimize = .fast,
    });
    const translated_yyjson_adapter = CompilerHeader.translate(translate_c, compiler_build_validation_identity.file, .{
        .c_source_file = b.path("include/yyjson_adapter.h"),
        .target = target,
        .optimize = optimize,
    });
    const translated_sqlite = CompilerHeader.translate(translate_c, compiler_build_validation_identity.file, .{
        .c_source_file = b.path("vendor/sqlite/sqlite3.h"),
        .target = target,
        .optimize = optimize,
    });
    const sqlite_c_module = translated_sqlite.mod;
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
            .{ .name = "yyjson_adapter_c", .module = translated_yyjson_adapter.mod },
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
    const cli_options = b.addOptions();
    cli_options.addOption(bool, "browser_enabled", browser_enabled);
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
        },
    });
    cli_module.addOptions("cli_options", cli_options);
    if (browser_enabled) {
        const httpz_dependency = try b.dependencyLazy("httpz", .{ .target = target, .optimize = optimize });
        cli_module.addImport("httpz", httpz_dependency.module("httpz"));
    }
    @import("build_support/browser.zig").build(b, if (browser_enabled) cli_module else null);
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
    if (browser_enabled) {
        const browser_smoke = b.addSystemCommand(&.{"python3"});
        browser_smoke.addFileArg2(b.path("test/zig/cli/browser_smoke.py"), .{});
        browser_smoke.addArtifactArg2(cli, .{});
        dependOnValidation(&browser_smoke.step, cli_identity_validation);
        b.step("browser-smoke", "Test the localhost compiler browser over HTTP").dependOn(&browser_smoke.step);
        const live_browser_smoke = b.addSystemCommand(&.{"python3"});
        live_browser_smoke.addFileArg2(b.path("test/zig/cli/live_browser_smoke.py"), .{});
        live_browser_smoke.addArtifactArg2(cli, .{});
        dependOnValidation(&live_browser_smoke.step, cli_identity_validation);
        b.step("live-browser-smoke", "Test the combined source watcher and live SQL browser").dependOn(&live_browser_smoke.step);
        const diagnostic_limit_smoke = b.addSystemCommand(&.{"python3"});
        diagnostic_limit_smoke.addFileArg2(b.path("test/zig/cli/diagnostic_limit_smoke.py"), .{});
        diagnostic_limit_smoke.addArtifactArg2(cli, .{});
        dependOnValidation(&diagnostic_limit_smoke.step, cli_identity_validation);
        b.step("diagnostic-limit-smoke", "Test diagnostic-limit publication and session recovery").dependOn(&diagnostic_limit_smoke.step);
        const browser_startup_smoke = b.addSystemCommand(&.{"python3"});
        browser_startup_smoke.addFileArg2(b.path("test/zig/cli/browser_startup_smoke.py"), .{});
        browser_startup_smoke.addArtifactArg2(cli, .{});
        dependOnValidation(&browser_startup_smoke.step, cli_identity_validation);
        b.step("browser-startup-smoke", "Test immediate live HTTP and workspace availability").dependOn(&browser_startup_smoke.step);
        const browser_resume_smoke = b.addSystemCommand(&.{"python3"});
        browser_resume_smoke.addFileArg2(b.path("test/zig/cli/browser_resume_smoke.py"), .{});
        browser_resume_smoke.addArtifactArg2(cli, .{});
        dependOnValidation(&browser_resume_smoke.step, cli_identity_validation);
        b.step("browser-resume-smoke", "Test persistent live snapshot reuse and invalidation").dependOn(&browser_resume_smoke.step);
    }
    const source_serve_smoke = b.addSystemCommand(&.{"python3"});
    source_serve_smoke.addFileArg2(b.path("test/zig/cli/source_serve_smoke.py"), .{});
    source_serve_smoke.addArtifactArg2(cli, .{});
    dependOnValidation(&source_serve_smoke.step, cli_identity_validation);
    b.step("source-serve-smoke", "Test source-root and imported dependency watching").dependOn(&source_serve_smoke.step);
    const install_smoke = b.addSystemCommand(&.{"python3"});
    install_smoke.addFileArg2(b.path("test/zig/cli/install_smoke.py"), .{});
    install_smoke.addArtifactArg2(cli, .{});
    dependOnValidation(&install_smoke.step, cli_identity_validation);
    b.step("install-smoke", "Test remapped Git submodule installation with local repositories").dependOn(&install_smoke.step);
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
        .optimize = .safe,
        .imports = &.{
            .{ .name = "build_options", .module = build_options_module },
            .{ .name = "big_int", .module = big_int_module },
            .{ .name = "cxx_compat", .module = cxx_compat_module },
        },
    });
    const json_fuzz_module = b.createModule(.{
        .root_source_file = b.path("src/fuzz_json.zig"),
        .target = target,
        .optimize = .safe,
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
        .optimize = .safe,
        .link_libc = true,
        .imports = &.{
            .{ .name = "build_options", .module = build_options_module },
            .{ .name = "big_int", .module = big_int_module },
            .{ .name = "common", .module = common_module },
            .{ .name = "cxx_compat", .module = cxx_compat_module },
            .{ .name = "zqlite", .module = zqlite_module },
            .{ .name = "yyjson_adapter_c", .module = translated_yyjson_adapter.mod },
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
        .optimize = .safe,
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
    if (!browser_enabled) {
        const browser_disabled_smoke = b.addSystemCommand(&.{"python3"});
        browser_disabled_smoke.addFileArg2(b.path("test/zig/cli/browser_disabled_smoke.py"), .{});
        browser_disabled_smoke.addArtifactArg2(cli, .{});
        dependOnValidation(&browser_disabled_smoke.step, cli_identity_validation);
        cli_smoke_step.dependOn(&browser_disabled_smoke.step);
    }
    const cache_lifecycle_smoke = b.addSystemCommand(&.{"python3"});
    cache_lifecycle_smoke.addFileArg2(b.path("test/zig/cli/cache_lifecycle_smoke.py"), .{});
    cache_lifecycle_smoke.addArtifactArg2(cli, .{});
    dependOnValidation(&cache_lifecycle_smoke.step, cli_identity_validation);
    b.step("cache-lifecycle-smoke", "Test persistent cache deletion, restart and recovery").dependOn(&cache_lifecycle_smoke.step);
    cli_smoke_step.dependOn(&cache_lifecycle_smoke.step);
    const cli_version_smoke = b.addSystemCommand(&.{"python3"});
    cli_version_smoke.addFileArg2(b.path("test/zig/cli/version_smoke.py"), .{});
    cli_version_smoke.addArtifactArg2(cli, .{});
    cli_version_smoke.addArg(package.version);
    cli_version_smoke.addFileContentArg2(compiler_build_validation_identity.file, .{});
    dependOnValidation(&cli_version_smoke.step, cli_identity_validation);
    b.step("version-smoke", "Check product and solc-compatible version reporting").dependOn(&cli_version_smoke.step);
    cli_smoke_step.dependOn(&cli_version_smoke.step);

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
    cli_cache_first.addDirectoryArg2(cli_project_root, .{});
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
    cli_cache_restart.addDirectoryArg2(cli_project_root, .{});
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
    run_cli_cache_seed.addDirectoryArg2(cli_project_root, .{});

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
    cli_no_cache.addDirectoryArg2(cli_project_root, .{});
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
    cli_config_no_cache.addDirectoryArg2(cli_config_no_cache_root, .{});
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
            .optimize = .safe,
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
        cli_parallel_check.addFileArg2(b.path("test/zig/standard-json/expected/via-ir-smoke.json"), .{});
        cli_parallel_check.addFileArg2(cli_parallel_output, .{});
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
    run_libsolc_c_smoke.addArg(b.fmt("0.8.36+oksolc.{s}", .{package.version}));
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
    // CI runs these in Debug and the compiler interfaces in ReleaseFast, so
    // the broad suite does not optimize another copy of every test binary.
    const unit_test_step = b.step("test-unit", "Run unit, ownership, and terminal tests without compiler smoke tests or fuzzers");
    test_step.dependOn(unit_test_step);
    const compiler_cache_check = b.addSystemCommand(&.{"python3"});
    compiler_cache_check.addFileArg2(b.path("test/zig/compiler_identity_cache.py"), .{});
    compiler_cache_check.addFileArg2(.zig_exe, .{ .make_absolute = true });
    compiler_cache_check.addDirectoryArg2(translate_c.path("."), .{ .make_absolute = true });
    compiler_cache_check.addDirectoryArg2(yyjson_dependency.path(".."), .{ .make_absolute = true });
    compiler_cache_check.addArg(package.dependencies.translate_c.hash);
    b.step("test-build-cache", "Test compiler identity and Zig configure cache invalidation").dependOn(&compiler_cache_check.step);
    unit_test_step.dependOn(&compiler_cache_check.step);
    const lint_worker_check = b.addSystemCommand(&.{"python3"});
    lint_worker_check.addFileArg2(b.path("test/zig/lint_worker.py"), .{});
    lint_worker_check.addFileArg2(.zig_exe, .{ .make_absolute = true });
    b.step("test-lint-worker", "Test offline lint workers and passthrough arguments").dependOn(&lint_worker_check.step);
    unit_test_step.dependOn(&lint_worker_check.step);
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
    terminal_smoke.addFileArg2(b.path("test/zig/common_io_terminal_smoke.py"), .{});
    terminal_smoke.addArtifactArg2(terminal_probe, .{});
    b.step("common-io-terminal-smoke", "Test terminal input and mode restoration").dependOn(&terminal_smoke.step);
    unit_test_step.dependOn(&terminal_smoke.step);
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
        b.createModule(.{
            .root_source_file = b.path("build_support/compiler_identity.zig"),
            .target = target,
            .optimize = optimize,
        }),
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
        unit_test_step.dependOn(&run_tests.step);
        if (module == cli_module)
            b.step("test-cli", "Run CLI unit tests").dependOn(&run_tests.step);
    }

    const evm_tests = b.addTest(.{ .root_module = b.createModule(.{
        .root_source_file = b.path("src/libevm.zig"),
        .target = target,
        .optimize = optimize,
    }) });
    b.step("test-evm", "Run shared EVM semantics tests").dependOn(&b.addRunArtifact(evm_tests).step);

    const frontend_index_tests = b.addTest(.{
        .name = "frontend-indexes",
        .root_module = compiler_module,
        .filters = &.{ "compiler module inventory", "CFG function-flow index", "dependency mask", "semantic fingerprints skip importers", "source graph", "semantic revision", "semantic child", "semantic overlay", "selective", "invalidation" },
    });
    frontend_index_tests.stack_size = 32 * 1024 * 1024;
    const run_frontend_index_tests = b.addRunArtifact(frontend_index_tests);
    dependOnValidation(&run_frontend_index_tests.step, addCompilerBuildIdentityValidation(
        b,
        frontend_index_tests,
        compiler_build_validation_identity,
    ));
    b.step("test-frontend-indexes", "Test frontend indexes and semantic dependency invalidation").dependOn(&run_frontend_index_tests.step);

    const public_api_tests = b.addTest(.{
        .name = "public-api",
        .root_module = solidity_module,
        .filters = &.{"public "},
    });
    public_api_tests.stack_size = 32 * 1024 * 1024;
    const run_public_api_tests = b.addRunArtifact(public_api_tests);
    dependOnValidation(&run_public_api_tests.step, addCompilerBuildIdentityValidation(b, public_api_tests, compiler_build_validation_identity));
    b.step("test-public-api", "Test public Zig API ownership and compiler sessions").dependOn(&run_public_api_tests.step);

    const yul_interner_tests = b.addTest(.{
        .name = "yul-interner",
        .root_module = compiler_module,
        .filters = &.{ "compiler module inventory", "libyul.yul_string", "cached dialect factories" },
    });
    yul_interner_tests.stack_size = 32 * 1024 * 1024;
    const run_yul_interner_tests = b.addRunArtifact(yul_interner_tests);
    dependOnValidation(&run_yul_interner_tests.step, addCompilerBuildIdentityValidation(b, yul_interner_tests, compiler_build_validation_identity));
    b.step("test-yul-interner", "Test sharded Yul canonicality, ownership, startup failures and reset lifetimes").dependOn(&run_yul_interner_tests.step);

    const optimizer_cache_tests = b.addTest(.{
        .name = "optimizer-cache-integration",
        .root_module = standard_json_dispatch_module,
        .filters = &.{"optimizer cache semantic edits"},
    });
    optimizer_cache_tests.stack_size = 32 * 1024 * 1024;
    const run_optimizer_cache_tests = b.addRunArtifact(optimizer_cache_tests);
    dependOnValidation(&run_optimizer_cache_tests.step, addCompilerBuildIdentityValidation(b, optimizer_cache_tests, compiler_build_validation_identity));
    b.step("test-optimizer-caches", "Test optimizer caches through incremental edits and full solc outputs").dependOn(&run_optimizer_cache_tests.step);

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
        .filters = &.{ "ownership test inventory", "assembly inliner", "label ID dispenser", "peephole", "assembly CSE", "assembly immutable", "assembly append", "backend scratch", "stack diagnostic", "stack multiplicity", "function grouper", "source locations", "source snippets", "escaped string content", "function specializer", "function analysis cache", "call graph", "optimizer scratch retention", "optimizer debug snapshots", "name simplifier", "IR variable", "IR source", "SSA transform", "SSA value tracker", "SSA reverser", "Yul stack owned printing", "Yul AST generated object", "assembly printing", "contract artifact", "statement remover", "profiler ", "for-loop init rewriter", "structural simplifier", "expression joiner", "expression splitter", "loop-invariant", "block flattener", "full inliner", "inline declarations", "linker ", "append rebases", "expression classes", "nested logical", "printing ", "CFG lowering", "transient optimizer", "unused store", "unused assignment", "unused pruner", "unused parameter", "variable name cleaner", "conditional simplifier" },
    });
    ownership_tests.stack_size = 32 * 1024 * 1024;
    check_step.dependOn(&ownership_tests.step);
    const run_ownership_tests = b.addRunArtifact(ownership_tests);
    unit_test_step.dependOn(&run_ownership_tests.step);
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
    unit_test_step.dependOn(&run_yul_construction.step);
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
    const parallel_group_tests = b.addTest(.{
        .root_module = compiler_module,
        .filters = &.{ "compiler module inventory", "parallel group cancellation", "parallel prepared jobs" },
    });
    const run_parallel_group_tests = b.addRunArtifact(parallel_group_tests);
    structured_yul_step.dependOn(&run_parallel_group_tests.step);
    const parallel_artifacts_step = b.step("test-parallel-artifacts", "Test artifact ownership, parallel output and retained-storage profiling");
    parallel_artifacts_step.dependOn(&run_structured_yul_artifact_tests.step);
    parallel_artifacts_step.dependOn(&run_parallel_group_tests.step);

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
    compile_adapter_fuzzer.addDirectoryArg2(b.path("include"), .{ .prefix = "-I" });
    compile_adapter_fuzzer.addDirectoryArg2(yyjson_dependency.path("src"), .{ .prefix = "-I" });
    compile_adapter_fuzzer.addFileArg2(b.path("src/fuzz_json_adapter.c"), .{});
    compile_adapter_fuzzer.addFileArg2(b.path("src/libsolc/yyjson_adapter.c"), .{});
    compile_adapter_fuzzer.addFileArg2(yyjson_dependency.path("src/yyjson.c"), .{});
    compile_adapter_fuzzer.addArg("-o");
    const adapter_fuzzer_binary = compile_adapter_fuzzer.addOutputFileArg2("json-adapter-fuzzer", .{});
    const run_adapter_fuzzer = b.addSystemCommand(&.{"/usr/bin/env"});
    run_adapter_fuzzer.setEnvironmentVariable(
        "ASAN_OPTIONS",
        "halt_on_error=1",
    );
    run_adapter_fuzzer.setEnvironmentVariable(
        "UBSAN_OPTIONS",
        "halt_on_error=1:print_stacktrace=1",
    );
    run_adapter_fuzzer.addFileArg2(adapter_fuzzer_binary, .{});
    run_adapter_fuzzer.addArg(b.fmt("{d}", .{adapter_fuzz_runs}));
    run_adapter_fuzzer.addArg(b.fmt("{d}", .{adapter_fuzz_seed}));
    inline for (.{
        "content.json",
        "callback.json",
        "duplicates.json",
        "source-limit.seed",
        "source-limit-exceeded.seed",
    }) |seed_name| {
        run_adapter_fuzzer.addFileArg2(b.path(b.fmt(
            "test/fuzz/json-adapter-corpus/{s}",
            .{seed_name},
        )), .{});
    }
    fuzz_step.dependOn(&run_adapter_fuzzer.step);
    fuzz_adapter_step.dependOn(&run_adapter_fuzzer.step);

    const fmt_check = b.addFmt(.{
        .paths = b.pathList(&.{
            "build.zig",
            "build.zig.zon",
            "build_support",
            "src",
            "test/zig",
            "test/benchmarks",
        }),
        .check = true,
    });
    const fmt_check_step = b.step("fmt-check", "Check Zig formatting");
    fmt_check_step.dependOn(&fmt_check.step);

    const lint_step = b.step("lint", "Lint Zig source");
    if (lint_worker) {
        var builder = zlinter.builder(b, .{ .optimize = .fast });
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
        builder.addSource(.{ .file_path = b.path("build.zig") });
        for ([_][]const u8{ "build_support", "src", "test/zig", "test/benchmarks" }) |path|
            builder.addSource(.{ .dir_path = b.path(path) });
        lint_step.dependOn(builder.build());
    } else {
        // zlinter probes for kcov during configuration even without coverage.
        // Keep that untracked lookup out of the normal configure cache.
        const lint = @import("build_support/lint.zig").worker(b, yyjson_dependency);
        lint_step.dependOn(&lint.step);
    }

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

fn addCompilerBuildIdentityValidation(
    b: *std.Build,
    artifact: *std.Build.Step.Compile,
    identity: CompilerIdentity.BuildIdentity,
) ?*std.Build.Step {
    return identity.validate(b, artifact);
}

fn dependOnValidation(step: *std.Build.Step, validation: ?*std.Build.Step) void {
    if (validation) |dependency| step.dependOn(dependency);
}

fn isolateCliSmokeEnvironment(b: *std.Build, run: *std.Build.Step.Run) void {
    const authentication_key = std.fmt.bytesToHex(@as([32]u8, @splat(0x5a)), .lower);
    run.setEnvironmentVariable(
        "XDG_CONFIG_HOME",
        b.root.joinString(b.allocator, "test/zig/cli/config-home") catch @panic("out of memory"),
    );
    run.setEnvironmentVariable(
        "OKSOLC_CACHE_AUTH_KEY",
        &authentication_key,
    );
    setCliSmokeDirectory(
        b,
        run,
        "XDG_CACHE_HOME",
        "oksolc-cli-smoke-cache-v2",
    );
}

fn enableCliSmokeCache(b: *std.Build, run: *std.Build.Step.Run) void {
    setCliSmokeDirectory(
        b,
        run,
        "XDG_CONFIG_HOME",
        "oksolc-cli-smoke-config-v2",
    );
}

fn setCliSmokeDirectory(b: *std.Build, run: *std.Build.Step.Run, name: []const u8, sub_path: []const u8) void {
    const command = run.argv.toOwnedSlice(b.allocator) catch @panic("out of memory");
    run.addArg("/usr/bin/env");
    run.addDirectoryArg2(b.graph.path(.global_cache, sub_path), .{
        .prefix = b.fmt("{s}=", .{name}),
        .make_absolute = true,
    });
    run.argv.appendSlice(b.allocator, command) catch @panic("out of memory");
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
    optimize: std.lang.Optimize,
    benchmark_runs: u32,
    benchmark_warmups: u32,
    reference_solc: []const u8,
    cli: *std.Build.Step.Compile,
    cli_identity_validation: ?*std.Build.Step,
    cxx_compat_module: *std.Build.Module,
    optimizer_workloads_module: *std.Build.Module,
    solidity_module: *std.Build.Module,
    incremental_edit_trace_module: *std.Build.Module,
    compiler_build_validation_identity: CompilerIdentity.BuildIdentity,
) void {
    const build_benchmarks_step = b.step(
        "build-benchmarks",
        "Build ReleaseFast benchmark executables in parallel without running them",
    );
    if (benchmarkGuard(b, build_benchmarks_step, target, optimize, 1)) {
        build_benchmarks_step.dependOn(&cli.step);
        dependOnValidation(build_benchmarks_step, cli_identity_validation);
    }
    const cache_probe_step = b.step("benchmark-optimizer-caches", "Compare single-sample cached and uncached CSE and nearly finished stack layouts");
    if (benchmarkGuard(b, cache_probe_step, target, optimize, 1)) {
        const cache_probe = b.addExecutable(.{
            .name = "optimizer-cache-probe",
            .root_module = b.createModule(.{
                .root_source_file = b.path("test/benchmarks/optimizer_caches.zig"),
                .target = target,
                .optimize = optimize,
                .link_libc = true,
                .imports = &.{.{ .name = "solidity", .module = solidity_module }},
            }),
        });
        const validation = addCompilerBuildIdentityValidation(b, cache_probe, compiler_build_validation_identity);
        build_benchmarks_step.dependOn(&cache_probe.step);
        dependOnValidation(build_benchmarks_step, validation);
        const run = b.addRunArtifact(cache_probe);
        run.has_side_effects = true;
        dependOnValidation(&run.step, validation);
        cache_probe_step.dependOn(&run.step);
    }
    const interner_probe_step = b.step("build-interner-benchmarks", "Build single-sample Yul interner probes for 1, 8, 16, 32 and 64 shards in parallel");
    if (benchmarkGuard(b, interner_probe_step, target, optimize, 1)) {
        const interner_module = b.createModule(.{
            .root_source_file = b.path("src/libyul/yul_string.zig"),
            .target = target,
            .optimize = optimize,
        });
        for ([_]usize{ 1, 8, 16, 32, 64 }) |count| {
            const options = b.addOptions();
            options.addOption(usize, "shards", count);
            const probe = b.addExecutable(.{
                .name = b.fmt("yul-interner-{d}", .{count}),
                .root_module = b.createModule(.{
                    .root_source_file = b.path("test/benchmarks/yul_interner.zig"),
                    .target = target,
                    .optimize = optimize,
                    .link_libc = true,
                    .imports = &.{
                        .{ .name = "yul_string", .module = interner_module },
                        .{ .name = "benchmark_options", .module = options.createModule() },
                    },
                }),
            });
            interner_probe_step.dependOn(&b.addInstallArtifact(probe, .{}).step);
            build_benchmarks_step.dependOn(&probe.step);
        }
    }
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
        benchmark_local.addArtifactArg2(cli, .{});
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
        build_benchmarks_step.dependOn(&zbench_executable.step);
        dependOnValidation(build_benchmarks_step, zbench_identity_validation);
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

    const benchmark_external_step = b.step(
        "benchmark-external",
        "Compare ReleaseFast oksolc output and performance with solc on 14 external projects",
    );
    if (benchmarkGuard(b, benchmark_external_step, target, optimize, benchmark_runs)) {
        const benchmark_external = b.addSystemCommand(&.{
            "bash",
            "test/benchmarks/external-compare.sh",
        });
        benchmark_external.addPassthruArgs();
        benchmark_external.addArg(reference_solc);
        benchmark_external.addArtifactArg2(cli, .{});
        dependOnValidation(&benchmark_external.step, cli_identity_validation);
        benchmark_external.addArg(b.fmt("{d}", .{benchmark_runs}));
        benchmark_external.setEnvironmentVariable(
            "BENCHMARK_WARMUPS",
            b.fmt("{d}", .{benchmark_warmups}),
        );
        benchmark_external.has_side_effects = true;
        benchmark_external_step.dependOn(&benchmark_external.step);
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
        build_benchmarks_step.dependOn(&benchmark_incremental_executable.step);
        dependOnValidation(build_benchmarks_step, identity_validation);
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
    optimize: std.lang.Optimize,
    runs: u32,
) bool {
    if (optimize != .fast) {
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
