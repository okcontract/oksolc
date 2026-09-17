// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Byte-exact edit traces for measuring incremental compiler behavior.
//!
//! Every warm compilation is compared with a fresh dispatcher for the same
//! revision. The report records compilation timings and cache counters for
//! no-op revisions, source edits, and compiler-setting changes.

const std = @import("std");
const builtin = @import("builtin");
const solidity = @import("solidity");

const modules = solidity.compiler;
const JSON = modules.libsolutil.json;
const Json = JSON.Json;
const Profiler = modules.libsolutil.profiler.Profiler;
const CompilerSession = solidity.incremental.CompilerSession;
const SessionStatistics = solidity.incremental.compiler_session.SessionStatistics;

const baseline_main_source =
    "pragma solidity ^0.8.0; import \"./Lib.sol\"; " ++
    "contract Main { " ++
    "function value(uint256 x) external pure returns (uint256) { return x + 1; } " ++
    "function linked(uint256 x) external view returns (uint256) { return Lib.bump(x); } " ++
    "}";
const body_edit_main_source =
    "pragma solidity ^0.8.0; import \"./Lib.sol\"; " ++
    "contract Main { " ++
    "function value(uint256 x) external pure returns (uint256) { return x + 2; } " ++
    "function linked(uint256 x) external view returns (uint256) { return Lib.bump(x); } " ++
    "}";
const interface_edit_main_source =
    "pragma solidity ^0.8.0; import \"./Lib.sol\"; " ++
    "contract Main { " ++
    "function value(bytes32 x) external pure returns (bytes32) { return x; } " ++
    "function linked(uint256 x) external view returns (uint256) { return Lib.bump(x); } " ++
    "}";
const renamed_main_source =
    "pragma solidity ^0.8.0; import \"./Math.sol\"; " ++
    "contract Main { " ++
    "function value(uint256 x) external pure returns (uint256) { return x + 1; } " ++
    "function linked(uint256 x) external view returns (uint256) { return Lib.bump(x); } " ++
    "}";
const baseline_library_source =
    "pragma solidity ^0.8.0; library Lib { " ++
    "function bump(uint256 x) external pure returns (uint256) { return x + 1; } " ++
    "}";
const import_edit_library_source =
    "pragma solidity ^0.8.0; library Lib { " ++
    "function bump(uint256 x) external pure returns (uint256) { return x + 3; } " ++
    "}";
const import_cycle_library_source =
    "pragma solidity ^0.8.0; import \"./Main.sol\"; library Lib { " ++
    "function bump(uint256 x) external pure returns (uint256) { return x + 1; } " ++
    "}";
const additional_source =
    "pragma solidity ^0.8.0; contract Extra { " ++
    "function value() external pure returns (uint256) { return 7; } " ++
    "}";

const OutputSelection = enum {
    creation_and_runtime,
    runtime_only,
};

const RequestConfig = struct {
    main_source: []const u8 = baseline_main_source,
    library_name: []const u8 = "Lib.sol",
    library_source: []const u8 = baseline_library_source,
    library_address: []const u8 = "0x1111111111111111111111111111111111111111",
    optimizer_runs: u64 = 200,
    metadata_hash: []const u8 = "ipfs",
    output_selection: OutputSelection = .creation_and_runtime,
    additional_source_name: ?[]const u8 = null,
};

const Trace = struct {
    name: []const u8,
    before: RequestConfig = .{},
    after: RequestConfig,
};

const traces = [_]Trace{
    .{ .name = "no-op", .after = .{} },
    .{ .name = "function-body", .after = .{ .main_source = body_edit_main_source } },
    .{ .name = "public-interface", .after = .{ .main_source = interface_edit_main_source } },
    .{ .name = "import", .after = .{ .library_source = import_edit_library_source } },
    .{
        .name = "rename",
        .after = .{
            .main_source = renamed_main_source,
            .library_name = "Math.sol",
        },
    },
    .{
        .name = "source-add",
        .after = .{ .additional_source_name = "Extra.sol" },
    },
    .{
        .name = "source-remove",
        .before = .{ .additional_source_name = "Extra.sol" },
        .after = .{},
    },
    .{
        .name = "import-cycle",
        .after = .{ .library_source = import_cycle_library_source },
    },
    .{ .name = "metadata", .after = .{ .metadata_hash = "none" } },
    .{
        .name = "library-address",
        .after = .{ .library_address = "0x2222222222222222222222222222222222222222" },
    },
    .{ .name = "optimizer-setting", .after = .{ .optimizer_runs = 500 } },
    .{ .name = "output-selection", .after = .{ .output_selection = .runtime_only } },
};

pub fn main(init: std.process.Init) !void {
    const arguments = try init.minimal.args.toSlice(init.arena.allocator());
    var output_path: ?[]const u8 = null;
    var argument_index: usize = 1;
    while (argument_index < arguments.len) : (argument_index += 1) {
        if (!std.mem.eql(u8, arguments[argument_index], "--output"))
            return error.InvalidArgument;
        argument_index += 1;
        if (argument_index == arguments.len) return error.MissingOutputPath;
        output_path = arguments[argument_index];
    }

    const report = try runAlloc(init.gpa, init.io);
    defer init.gpa.free(report);
    if (output_path) |path| {
        if (std.Io.Dir.path.dirname(path)) |directory|
            try std.Io.Dir.cwd().createDirPath(init.io, directory);
        var file = try std.Io.Dir.cwd().createFile(init.io, path, .{});
        defer file.close(init.io);
        try file.writeStreamingAll(init.io, report);
        try file.writeStreamingAll(init.io, "\n");
    } else {
        try std.Io.File.stdout().writeStreamingAll(init.io, report);
        try std.Io.File.stdout().writeStreamingAll(init.io, "\n");
    }
}

fn runAlloc(allocator: std.mem.Allocator, io: std.Io) ![]u8 {
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var trace_reports = std.json.Array.init(arena);
    for (traces) |trace| {
        const before_request = try requestAlloc(allocator, trace.before);
        defer allocator.free(before_request);
        const after_request = try requestAlloc(allocator, trace.after);
        defer allocator.free(after_request);

        var session = CompilerSession.init(allocator);
        defer session.deinit();
        try compileAndCompare(allocator, before_request, &session, null);
        const before_statistics = session.statistics();

        var oracle_dispatcher: solidity.StandardJsonDispatcher = .{};
        var expected = try oracle_dispatcher.compiler().compile(
            allocator,
            .{ .input = after_request },
        );
        defer expected.deinit();
        var profiler = Profiler.init(allocator, io);
        defer profiler.deinit();
        session.setOptimizerProfiler(&profiler);
        const start = std.Io.Clock.awake.now(io).nanoseconds;
        var actual = try session.compiler().compile(allocator, .{ .input = after_request });
        const elapsed = std.Io.Clock.awake.now(io).nanoseconds - start;
        defer actual.deinit();
        session.setOptimizerProfiler(null);
        try compareSuccessful(expected.bytes, actual.bytes);
        const after_statistics = session.statistics();

        var report: Json = .{ .object = .empty };
        try report.object.put(arena, "edit", .{ .string = trace.name });
        try report.object.put(arena, "wall_time_nanoseconds", jsonInteger(elapsed));
        try report.object.put(
            arena,
            "response_cache",
            try responseCacheStatisticsJson(arena, before_statistics, after_statistics),
        );
        try report.object.put(
            arena,
            "optimizer_cache",
            try optimizerCacheStatisticsJson(arena, before_statistics, after_statistics),
        );
        try report.object.put(
            arena,
            "backend_cache",
            try backendCacheStatisticsJson(arena, before_statistics, after_statistics),
        );
        try report.object.put(
            arena,
            "cache_resident_bytes",
            jsonInteger(cacheResidentBytes(after_statistics)),
        );
        try report.object.put(
            arena,
            "store_failures",
            jsonInteger(after_statistics.store_failures - before_statistics.store_failures),
        );
        try report.object.put(
            arena,
            "invalidations",
            try frontendStatisticsJson(arena, before_statistics, after_statistics),
        );
        try report.object.put(arena, "database_wait_nanoseconds", .null);
        try report.object.put(
            arena,
            "phase_times",
            try phaseTimesJson(arena, &profiler),
        );
        try trace_reports.append(report);
    }

    var root: Json = .{ .object = .empty };
    try root.object.put(arena, "schema_version", .{ .integer = 4 });
    try root.object.put(arena, "compiler", .{ .string = "oksolc" });
    try root.object.put(arena, "mode", .{ .string = "memory-session" });
    try root.object.put(arena, "oracle", .{ .string = "fresh-byte-exact" });
    try root.object.put(
        arena,
        "rss_scope",
        .{ .string = "process-lifetime high-water; includes warmups and clean oracles" },
    );
    try root.object.put(arena, "process_peak_rss_bytes", jsonInteger(peakRssBytes()));
    try root.object.put(arena, "traces", .{ .array = trace_reports });
    return JSON.jsonCompactPrintAlloc(allocator, &root);
}

fn compileAndCompare(
    allocator: std.mem.Allocator,
    request: []const u8,
    session: *CompilerSession,
    profiler: ?*Profiler,
) !void {
    var oracle_dispatcher: solidity.StandardJsonDispatcher = .{};
    var expected = try oracle_dispatcher.compiler().compile(allocator, .{ .input = request });
    defer expected.deinit();

    session.setOptimizerProfiler(profiler);
    var actual = try session.compiler().compile(allocator, .{ .input = request });
    defer actual.deinit();
    session.setOptimizerProfiler(null);
    try compareSuccessful(expected.bytes, actual.bytes);
}

fn compareSuccessful(expected: []const u8, actual: []const u8) !void {
    try solidity.standard_json.compareExact(expected, actual);
    if (std.mem.find(u8, actual, "\"severity\":\"error\"") != null)
        return error.TraceCompilationFailed;
}

fn responseCacheStatisticsJson(
    allocator: std.mem.Allocator,
    before: SessionStatistics,
    after: SessionStatistics,
) !Json {
    var result: Json = .{ .object = .empty };
    try putDelta(
        allocator,
        &result,
        "hits",
        before.memory_response_hits,
        after.memory_response_hits,
    );
    try putDelta(
        allocator,
        &result,
        "misses",
        before.response_misses,
        after.response_misses,
    );
    try putDelta(
        allocator,
        &result,
        "lookup_hits",
        before.memory.hits,
        after.memory.hits,
    );
    try putDelta(
        allocator,
        &result,
        "lookup_misses",
        before.memory.misses,
        after.memory.misses,
    );
    try putDelta(
        allocator,
        &result,
        "coherence_rejections",
        before.coherence_rejections,
        after.coherence_rejections,
    );
    try putDelta(allocator, &result, "puts", before.memory.puts, after.memory.puts);
    try putDelta(
        allocator,
        &result,
        "replacements",
        before.memory.replacements,
        after.memory.replacements,
    );
    try putDelta(
        allocator,
        &result,
        "bytes_read",
        before.memory.bytes_read,
        after.memory.bytes_read,
    );
    try putDelta(
        allocator,
        &result,
        "bytes_written",
        before.memory.bytes_written,
        after.memory.bytes_written,
    );
    try result.object.put(allocator, "entries", jsonInteger(after.memory.entries));
    try result.object.put(
        allocator,
        "resident_bytes",
        jsonInteger(after.memory.resident_bytes),
    );
    return result;
}

fn optimizerCacheStatisticsJson(
    allocator: std.mem.Allocator,
    before: SessionStatistics,
    after: SessionStatistics,
) !Json {
    var result: Json = .{ .object = .empty };
    inline for (.{
        .{ "memory_hits", "memory_hits" },
        .{ "memory_misses", "memory_misses" },
        .{ "persistent_hits", "persistent_hits" },
        .{ "persistent_misses", "persistent_misses" },
        .{ "persistent_failures", "persistent_failures" },
        .{ "optimization_runs", "optimization_runs" },
        .{ "single_flight_waits", "single_flight_waits" },
    }) |field| try putDelta(
        allocator,
        &result,
        field[0],
        @field(before.optimizer, field[1]),
        @field(after.optimizer, field[1]),
    );
    try result.object.put(allocator, "entries", jsonInteger(after.optimizer.entries));
    try result.object.put(
        allocator,
        "resident_bytes",
        jsonInteger(after.optimizer.resident_bytes),
    );
    return result;
}

fn backendCacheStatisticsJson(
    allocator: std.mem.Allocator,
    before: SessionStatistics,
    after: SessionStatistics,
) !Json {
    var result: Json = .{ .object = .empty };
    inline for (.{
        .{ "blueprint_hits", "blueprint_hits" },
        .{ "blueprint_misses", "blueprint_misses" },
        .{ "machine_hits", "machine_hits" },
        .{ "machine_misses", "machine_misses" },
        .{ "link_hits", "link_hits" },
        .{ "link_misses", "link_misses" },
        .{ "lowering_runs", "lowering_runs" },
        .{ "bytecode_assembly_runs", "bytecode_assembly_runs" },
        .{ "memory_hits", "memory_hits" },
        .{ "memory_misses", "memory_misses" },
        .{ "persistent_hits", "persistent_hits" },
        .{ "persistent_misses", "persistent_misses" },
        .{ "cache_failures", "cache_failures" },
    }) |field| try putDelta(
        allocator,
        &result,
        field[0],
        @field(before.backend, field[1]),
        @field(after.backend, field[1]),
    );
    try result.object.put(
        allocator,
        "flight_entries",
        jsonInteger(after.backend.flight_entries),
    );
    try result.object.put(
        allocator,
        "resident_bytes",
        jsonInteger(after.backend.memory.resident_bytes),
    );
    return result;
}

fn frontendStatisticsJson(
    allocator: std.mem.Allocator,
    before: SessionStatistics,
    after: SessionStatistics,
) !Json {
    const advanced = before.frontend.revision != after.frontend.revision;
    var result: Json = .{ .object = .empty };
    try result.object.put(
        allocator,
        "revision_before",
        jsonInteger(before.frontend.revision),
    );
    try result.object.put(
        allocator,
        "revision_after",
        jsonInteger(after.frontend.revision),
    );
    try result.object.put(allocator, "revision_advanced", .{ .bool = advanced });
    try result.object.put(
        allocator,
        "active_sources",
        jsonInteger(after.frontend.active_sources),
    );
    inline for (.{
        .{ "dirty_sources", "dirty_sources" },
        .{ "parsed_syntax_sources", "parsed_syntax_sources" },
        .{ "reused_syntax_sources", "reused_syntax_sources" },
        .{ "analyzed_semantic_sources", "analyzed_semantic_sources" },
        .{ "reused_semantic_sources", "reused_semantic_sources" },
        .{ "fingerprinted_sources", "fingerprinted_sources" },
        .{ "semantic_dependency_edges", "semantic_dependency_edges" },
    }) |field| try result.object.put(
        allocator,
        field[0],
        jsonInteger(if (advanced) @field(after.frontend, field[1]) else 0),
    );
    try result.object.put(
        allocator,
        "semantic_analyzed",
        .{ .bool = advanced and after.frontend.semantic_analyzed },
    );
    return result;
}

fn putDelta(
    allocator: std.mem.Allocator,
    result: *Json,
    name: []const u8,
    before: u64,
    after: u64,
) !void {
    std.debug.assert(after >= before);
    try result.object.put(allocator, name, jsonInteger(after - before));
}

fn cacheResidentBytes(statistics: SessionStatistics) u64 {
    return statistics.memory.resident_bytes +|
        statistics.optimizer.resident_bytes +|
        statistics.backend.memory.resident_bytes;
}

fn phaseTimesJson(allocator: std.mem.Allocator, profiler: *Profiler) !Json {
    const indices = try allocator.alloc(usize, profiler.metrics.count());
    for (indices, 0..) |*slot, index| slot.* = index;
    std.sort.insertion(usize, indices, profiler, struct {
        fn lessThan(context: *Profiler, left: usize, right: usize) bool {
            return std.mem.order(
                u8,
                context.metrics.keys()[left],
                context.metrics.keys()[right],
            ) == .lt;
        }
    }.lessThan);

    var result: Json = .{ .object = .empty };
    for (indices) |index| {
        const metrics = profiler.metrics.values()[index];
        var value: Json = .{ .object = .empty };
        try value.object.put(
            allocator,
            "duration_microseconds",
            jsonInteger(metrics.duration_microseconds),
        );
        try value.object.put(
            allocator,
            "maximum_duration_microseconds",
            jsonInteger(metrics.maximum_duration_microseconds),
        );
        try value.object.put(
            allocator,
            "cpu_duration_microseconds",
            jsonInteger(metrics.cpu_duration_microseconds),
        );
        try value.object.put(
            allocator,
            "maximum_cpu_duration_microseconds",
            jsonInteger(metrics.maximum_cpu_duration_microseconds),
        );
        try value.object.put(allocator, "call_count", jsonInteger(metrics.call_count));
        try result.object.put(
            allocator,
            try allocator.dupe(u8, profiler.metrics.keys()[index]),
            value,
        );
    }
    return result;
}

fn requestAlloc(allocator: std.mem.Allocator, config: RequestConfig) ![]u8 {
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var sources: Json = .{ .object = .empty };
    try sources.object.put(arena, "Main.sol", try sourceJson(arena, config.main_source));
    try sources.object.put(
        arena,
        config.library_name,
        try sourceJson(arena, config.library_source),
    );
    if (config.additional_source_name) |name|
        try sources.object.put(arena, name, try sourceJson(arena, additional_source));

    var optimizer: Json = .{ .object = .empty };
    try optimizer.object.put(arena, "enabled", .{ .bool = true });
    try optimizer.object.put(arena, "runs", jsonInteger(config.optimizer_runs));

    var metadata: Json = .{ .object = .empty };
    try metadata.object.put(arena, "bytecodeHash", .{ .string = config.metadata_hash });
    try metadata.object.put(arena, "appendCBOR", .{ .bool = true });

    var library_file: Json = .{ .object = .empty };
    try library_file.object.put(arena, "Lib", .{ .string = config.library_address });
    var libraries: Json = .{ .object = .empty };
    try libraries.object.put(arena, config.library_name, library_file);

    var artifacts = std.json.Array.init(arena);
    if (config.output_selection == .creation_and_runtime)
        try artifacts.append(.{ .string = "evm.bytecode.object" });
    try artifacts.append(.{ .string = "evm.deployedBytecode.object" });
    var contracts: Json = .{ .object = .empty };
    try contracts.object.put(arena, "*", .{ .array = artifacts });
    var output_selection: Json = .{ .object = .empty };
    try output_selection.object.put(arena, "*", contracts);

    var settings: Json = .{ .object = .empty };
    try settings.object.put(arena, "optimizer", optimizer);
    try settings.object.put(arena, "viaIR", .{ .bool = true });
    try settings.object.put(arena, "metadata", metadata);
    try settings.object.put(arena, "libraries", libraries);
    try settings.object.put(arena, "outputSelection", output_selection);

    var root: Json = .{ .object = .empty };
    try root.object.put(arena, "language", .{ .string = "Solidity" });
    try root.object.put(arena, "sources", sources);
    try root.object.put(arena, "settings", settings);
    return JSON.jsonCompactPrintAlloc(allocator, &root);
}

fn sourceJson(allocator: std.mem.Allocator, source: []const u8) !Json {
    var result: Json = .{ .object = .empty };
    try result.object.put(allocator, "content", .{ .string = source });
    return result;
}

fn jsonInteger(value: anytype) Json {
    const Value = @TypeOf(value);
    const converted: i64 = switch (@typeInfo(Value)) {
        .int, .comptime_int => if (value <= 0)
            0
        else
            std.math.cast(i64, value) orelse std.math.maxInt(i64),
        else => @compileError("jsonInteger requires an integer"),
    };
    return .{ .integer = converted };
}

fn peakRssBytes() usize {
    return switch (builtin.os.tag) {
        .dragonfly, .freebsd, .netbsd, .openbsd, .illumos, .linux, .serenity => blk: {
            const usage = std.posix.getrusage(0);
            break :blk @as(usize, @intCast(usage.maxrss)) * 1024;
        },
        .driverkit, .ios, .maccatalyst, .macos, .tvos, .visionos, .watchos => blk: {
            const usage = std.posix.getrusage(0);
            break :blk @intCast(usage.maxrss);
        },
        else => 0,
    };
}

test "edit trace covers every initial invalidation dimension" {
    const expected = [_][]const u8{
        "no-op",
        "function-body",
        "public-interface",
        "import",
        "rename",
        "source-add",
        "source-remove",
        "import-cycle",
        "metadata",
        "library-address",
        "optimizer-setting",
        "output-selection",
    };
    try std.testing.expectEqual(expected.len, traces.len);
    for (expected, traces) |name, trace|
        try std.testing.expectEqualStrings(name, trace.name);
}

test "every edit trace revision is byte-exact with a clean compilation" {
    for (traces) |trace| {
        const before = try requestAlloc(std.testing.allocator, trace.before);
        defer std.testing.allocator.free(before);
        const after = try requestAlloc(std.testing.allocator, trace.after);
        defer std.testing.allocator.free(after);

        var session = CompilerSession.init(std.testing.allocator);
        defer session.deinit();
        try compileAndCompare(std.testing.allocator, before, &session, null);
        try compileAndCompare(std.testing.allocator, after, &session, null);
    }
}

test "deterministic randomized edit sequence stays byte-exact" {
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var prng = std.Random.DefaultPrng.init(0x492a_41a7_5b23_910d);
    const random = prng.random();
    for (0..32) |_| {
        const trace = traces[random.uintLessThan(usize, traces.len)];
        const request = try requestAlloc(std.testing.allocator, trace.after);
        defer std.testing.allocator.free(request);
        try compileAndCompare(std.testing.allocator, request, &session, null);
    }
}

test "edit trace requests are strict JSON and only no-op is byte-identical" {
    for (traces, 0..) |trace, index| {
        const before = try requestAlloc(std.testing.allocator, trace.before);
        defer std.testing.allocator.free(before);
        const after = try requestAlloc(std.testing.allocator, trace.after);
        defer std.testing.allocator.free(after);

        var before_json = try JSON.jsonParseStrict(std.testing.allocator, before);
        defer before_json.deinit();
        var after_json = try JSON.jsonParseStrict(std.testing.allocator, after);
        defer after_json.deinit();
        try std.testing.expect(before_json == .document);
        try std.testing.expect(after_json == .document);
        try std.testing.expectEqual(index == 0, std.mem.eql(u8, before, after));
    }
}
