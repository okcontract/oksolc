// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Internal performance probes for measured Zig compiler hot paths.
//!
//! The default build step runs the byte-exact system-solc comparison first.
//! These measurements can therefore guide representation changes without
//! turning a faster but semantically different compiler into a success.

const std = @import("std");
const builtin = @import("builtin");
const cxx = @import("cxx_compat");
const optimizer_workloads = @import("optimizer_workloads");
const solidity = @import("solidity");
const zbench = @import("zbench");

const modules = solidity.compiler;
const AST = modules.libyul.ast;
const ASTCopier = modules.libyul.@"optimiser/ast_copier".ASTCopier;
const AsmParser = modules.libyul.asm_parser;
const BigInt = modules.libsolutil.big_int.BigInt;
const JsonUtil = modules.libsolutil.json;
const CommonSubexpressionEliminator =
    modules.libyul.@"optimiser/common_subexpression_eliminator".CommonSubexpressionEliminator;
const DataFlow = modules.libyul.@"optimiser/data_flow_analyzer";
const Diagnostics = modules.liblangutil.diagnostics;
const EVMDialect = modules.libyul.@"backends/evm/evm_dialect".EVMDialect;
const EVMVersion = modules.liblangutil.evm_version.EVMVersion;
const NameCollector = modules.libyul.@"optimiser/name_collector";
const NameDispenser = modules.libyul.@"optimiser/name_dispenser".NameDispenser;
const OptimiserStepContext =
    modules.libyul.@"optimiser/optimiser_step".OptimiserStepContext;
const SyntacticallyEqual =
    modules.libyul.@"optimiser/syntactical_equality".SyntacticallyEqual;

const map_entry_count = 4_096;
const OrderedMap = cxx.OrderedMap(u32, u32, lessU32);
const HashMap = std.AutoHashMapUnmanaged(u32, u32);

const OptimizerWorkloadKind = enum {
    data_flow_ignore,
    data_flow_analyze,
    data_flow_observed,
    common_subexpression_elimination,
    assigned_block_facts,
    syntactic_equality,
};

const PreparedYul = struct {
    ast: AST.AST,

    fn init(
        allocator: std.mem.Allocator,
        dialect: AST.Dialect,
        source: []const u8,
    ) !PreparedYul {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        const ast = (try AsmParser.Parser.parseSource(
            allocator,
            source,
            "optimizer-workload.yul",
            &reporter,
            dialect,
            .{},
        )) orelse return error.InvalidOptimizerWorkload;
        return .{ .ast = ast };
    }

    fn deinit(self: *PreparedYul) void {
        self.ast.deinit();
        self.* = undefined;
    }
};

const OptimizerWorkload = struct {
    name: []const u8,
    kind: OptimizerWorkloadKind,
    block: *const AST.Block,
    dialect: AST.Dialect,
    source_bytes: usize,

    pub fn run(self: *const OptimizerWorkload, allocator: std.mem.Allocator) void {
        self.runFallible(allocator) catch @panic("optimizer benchmark failed");
    }

    fn runFallible(
        self: *const OptimizerWorkload,
        allocator: std.mem.Allocator,
    ) !void {
        var copier = ASTCopier.init(allocator);
        var block = try copier.translateBlock(self.block);
        defer block.deinit(allocator);

        switch (self.kind) {
            .data_flow_ignore => {
                var observer: DataFlow.NoObserver = .{};
                const Analyzer = DataFlow.DataFlowAnalyzer(DataFlow.NoObserver, .ignore);
                var analyzer = Analyzer.init(allocator, self.dialect, null);
                defer analyzer.deinit();
                try analyzer.run(&observer, &block);
            },
            .data_flow_analyze => {
                var observer: DataFlow.NoObserver = .{};
                const Analyzer = DataFlow.DataFlowAnalyzer(DataFlow.NoObserver, .analyze);
                var analyzer = Analyzer.init(allocator, self.dialect, null);
                defer analyzer.deinit();
                try analyzer.run(&observer, &block);
            },
            .data_flow_observed => {
                var counters: WorkloadCounters = .{};
                const Analyzer = DataFlow.DataFlowAnalyzer(WorkloadCounters, .ignore);
                var analyzer = Analyzer.init(allocator, self.dialect, null);
                defer analyzer.deinit();
                try analyzer.run(&counters, &block);
                std.mem.doNotOptimizeAway(&counters);
            },
            .common_subexpression_elimination => {
                var reserved: NameCollector.NameSet = .{};
                defer reserved.deinit(allocator);
                var dispenser = try NameDispenser.initFromAst(
                    allocator,
                    self.dialect,
                    &block,
                    &reserved,
                );
                defer dispenser.deinit();
                var context: OptimiserStepContext = .{
                    .dialect = self.dialect,
                    .dispenser = &dispenser,
                    .reserved_identifiers = &reserved,
                };
                try CommonSubexpressionEliminator.run(&context, &block);
            },
            .assigned_block_facts => {
                var assigned = try NameCollector.assignedVariableNames(allocator, &block);
                defer assigned.deinit(allocator);
                std.mem.doNotOptimizeAway(assigned.len());
            },
            .syntactic_equality => {
                var rhs = try copier.translateBlock(self.block);
                defer rhs.deinit(allocator);
                var equality = SyntacticallyEqual.init(allocator);
                defer equality.deinit();
                std.debug.assert(try equality.block(&block, &rhs));
            },
        }
        std.mem.doNotOptimizeAway(&block);
    }
};

const WorkloadCounters = struct {
    expression_visits: usize = 0,
    statement_visits: usize = 0,
    assignments: usize = 0,
    forward_reference_slots: usize = 0,
    reverse_edges: usize = 0,
    live_dependency_edges: usize = 0,
    dependency_compactions: usize = 0,

    pub fn visitExpression(
        self: *WorkloadCounters,
        _: anytype,
        _: *AST.Expression,
    ) anyerror!DataFlow.ExpressionVisit {
        self.expression_visits += 1;
        return .descend;
    }

    pub fn beforeStatement(
        self: *WorkloadCounters,
        _: anytype,
        _: *const AST.Statement,
    ) anyerror!void {
        self.statement_visits += 1;
    }

    pub fn assignValue(
        self: *WorkloadCounters,
        analyzer: anytype,
        variable: modules.libyul.yul_name.YulName,
        value: ?*const AST.Expression,
    ) anyerror!bool {
        self.assignments += 1;
        try analyzer.baseAssignValue(variable, value);
        return true;
    }
};

/// zBench 0.11.2 forwards allocator remaps without updating its live-byte
/// counters. Refusing remap here makes reallocations take the tracked
/// allocate/copy/free fallback and keeps benchmark memory results meaningful.
const TrackingCompatibleAllocator = struct {
    child: std.mem.Allocator,

    fn allocator(self: *TrackingCompatibleAllocator) std.mem.Allocator {
        return .{ .ptr = self, .vtable = &.{
            .alloc = alloc,
            .resize = resize,
            .remap = remap,
            .free = free,
        } };
    }

    fn alloc(
        context: *anyopaque,
        length: usize,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) ?[*]u8 {
        const self: *TrackingCompatibleAllocator = @ptrCast(@alignCast(context));
        return self.child.rawAlloc(length, alignment, return_address);
    }

    fn resize(
        context: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_length: usize,
        return_address: usize,
    ) bool {
        const self: *TrackingCompatibleAllocator = @ptrCast(@alignCast(context));
        return self.child.rawResize(memory, alignment, new_length, return_address);
    }

    fn remap(
        _: *anyopaque,
        _: []u8,
        _: std.mem.Alignment,
        _: usize,
        _: usize,
    ) ?[*]u8 {
        return null;
    }

    fn free(
        context: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) void {
        const self: *TrackingCompatibleAllocator = @ptrCast(@alignCast(context));
        self.child.rawFree(memory, alignment, return_address);
    }
};

fn lessU32(left: u32, right: u32) bool {
    return left < right;
}

fn permutedKey(index: usize) u32 {
    const value: u32 = @intCast(index);
    return value *% 2_654_435_761;
}

fn orderedMapInsert(allocator: std.mem.Allocator) void {
    var compatible: TrackingCompatibleAllocator = .{ .child = allocator };
    const tracked_allocator = compatible.allocator();
    var map: OrderedMap = .{};
    defer map.deinit(tracked_allocator);
    for (0..map_entry_count) |index| {
        const key = permutedKey(index);
        const inserted = map.insert(tracked_allocator, key, key) catch
            @panic("ordered-map benchmark allocation failed");
        std.debug.assert(inserted);
    }
    std.mem.doNotOptimizeAway(&map);
}

fn hashMapInsert(allocator: std.mem.Allocator) void {
    var compatible: TrackingCompatibleAllocator = .{ .child = allocator };
    const tracked_allocator = compatible.allocator();
    var map: HashMap = .empty;
    defer map.deinit(tracked_allocator);
    for (0..map_entry_count) |index| {
        const key = permutedKey(index);
        map.putNoClobber(tracked_allocator, key, key) catch
            @panic("hash-map benchmark allocation failed");
    }
    std.mem.doNotOptimizeAway(&map);
}

// BigInt intentionally uses the process-wide SMP allocator for derived values.
// These cases measure execution time only: zBench's allocator counters cannot
// observe BigInt's allocations.
fn bigIntSmallArithmetic(_: std.mem.Allocator) void {
    var checksum: u256 = 0;
    for (0..2_048) |index| {
        var lhs = BigInt.initUnsigned(@intCast(index + 1));
        var rhs = BigInt.initUnsigned(@intCast(index * 3 + 17));
        var sum = BigInt.add(&lhs, &rhs);
        var product = BigInt.mul(&lhs, &rhs);
        var divisor = BigInt.gcd(&sum, &product);
        checksum +%= sum.toU256Wrapping();
        checksum +%= product.toU256Wrapping();
        checksum +%= divisor.toU256Wrapping();
        divisor.deinit();
        product.deinit();
        sum.deinit();
        rhs.deinit();
        lhs.deinit();
    }
    std.mem.doNotOptimizeAway(&checksum);
}

fn bigIntU256Arithmetic(_: std.mem.Allocator) void {
    var lhs = BigInt.fromU256((@as(u256, 1) << 255) + 0x1234_5678_9abc_def0);
    defer lhs.deinit();
    var rhs = BigInt.fromU256((@as(u256, 1) << 192) + 0xfedc_ba98_7654_3211);
    defer rhs.deinit();
    var checksum: u256 = 0;
    for (0..512) |_| {
        var difference = BigInt.sub(&lhs, &rhs);
        var combined = BigInt.bitXor(&lhs, &rhs);
        var divisor = BigInt.gcd(&lhs, &rhs);
        checksum +%= difference.toU256Wrapping();
        checksum +%= combined.toU256Wrapping();
        checksum +%= divisor.toU256Wrapping();
        divisor.deinit();
        combined.deinit();
        difference.deinit();
    }
    std.mem.doNotOptimizeAway(&checksum);
}

fn bigIntPromotionMultiply(_: std.mem.Allocator) void {
    var lhs = BigInt.fromU256(std.math.maxInt(u256) - 16);
    defer lhs.deinit();
    var rhs = BigInt.fromU256(std.math.maxInt(u256) - 32);
    defer rhs.deinit();
    var checksum: u256 = 0;
    for (0..512) |_| {
        var product = BigInt.mul(&lhs, &rhs);
        checksum +%= product.toU256Wrapping();
        product.deinit();
    }
    std.mem.doNotOptimizeAway(&checksum);
}

fn bigIntSmallParsing(allocator: std.mem.Allocator) void {
    const inputs = [_]struct { text: []const u8, base: u8 }{
        .{ .text = "123456789012345678901234567890", .base = 10 },
        .{ .text = "  -0x1234 5678 9abc def0  ", .base = 0 },
        .{ .text = "ZzZzZzZz", .base = 62 },
        .{
            .text = "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            .base = 10,
        },
    };
    var checksum: u256 = 0;
    for (0..2_048) |index| {
        const input = inputs[index % inputs.len];
        var value = BigInt.parse(allocator, input.text, input.base) catch
            @panic("BigInt parsing benchmark failed");
        checksum +%= value.toU256Wrapping();
        value.deinit();
    }
    std.mem.doNotOptimizeAway(&checksum);
}

const CompilerCase = struct {
    request: []const u8,
    io: ?std.Io = null,
    use_smp_allocator: bool = false,

    pub fn run(self: *const CompilerCase, allocator: std.mem.Allocator) void {
        var compatible: TrackingCompatibleAllocator = .{ .child = allocator };
        const tracked_allocator = compatible.allocator();
        const compile_allocator = if (self.use_smp_allocator)
            std.heap.smp_allocator
        else
            tracked_allocator;
        var dispatcher: solidity.StandardJsonDispatcher = .{};
        var output = dispatcher.compiler().compile(compile_allocator, .{
            .input = self.request,
            .io = self.io,
        }) catch @panic("compiler benchmark failed");
        defer output.deinit();
        std.mem.doNotOptimizeAway(output.bytes.ptr);
        std.mem.doNotOptimizeAway(output.bytes.len);
    }
};

const JsonParseCase = struct {
    input: []const u8,

    pub fn run(self: *const JsonParseCase, allocator: std.mem.Allocator) void {
        var parsed = JsonUtil.jsonParseStrict(allocator, self.input) catch
            @panic("JSON parsing benchmark failed");
        defer parsed.deinit();
        switch (parsed) {
            .document => |*document| std.mem.doNotOptimizeAway(document.rootConst()),
            .failure => @panic("JSON parsing benchmark rejected valid JSON"),
        }
    }
};

const JsonPrintCase = struct {
    root: *const JsonUtil.Json,

    pub fn run(self: *const JsonPrintCase, _: std.mem.Allocator) void {
        const output = JsonUtil.jsonCompactPrintAlloc(std.heap.smp_allocator, self.root) catch
            @panic("JSON serialization benchmark failed");
        defer std.heap.smp_allocator.free(output);
        std.mem.doNotOptimizeAway(output.ptr);
        std.mem.doNotOptimizeAway(output.len);
    }
};

const SyntacticEqualityCase = struct {
    block: *const AST.Block,

    pub fn run(self: *const SyntacticEqualityCase, allocator: std.mem.Allocator) void {
        var equality = SyntacticallyEqual.init(allocator);
        defer equality.deinit();
        std.debug.assert(equality.block(self.block, self.block) catch
            @panic("syntactic-equality benchmark failed"));
    }
};

fn measureWorkloadCounters(
    allocator: std.mem.Allocator,
    workload: *const OptimizerWorkload,
) !WorkloadCounters {
    var copier = ASTCopier.init(allocator);
    var block = try copier.translateBlock(workload.block);
    defer block.deinit(allocator);
    var counters: WorkloadCounters = .{};
    const Analyzer = DataFlow.DataFlowAnalyzer(WorkloadCounters, .analyze);
    var analyzer = Analyzer.init(allocator, workload.dialect, null);
    defer analyzer.deinit();
    try analyzer.run(&counters, &block);
    const dependency_stats = analyzer.dependencyPoolStats();
    counters.forward_reference_slots = dependency_stats.forward_slots;
    counters.reverse_edges = dependency_stats.reverse_edges;
    counters.live_dependency_edges = dependency_stats.live_edges;
    counters.dependency_compactions = dependency_stats.compactions;
    return counters;
}

fn writeUnsignedArray(
    writer: *std.Io.Writer,
    values: anytype,
) !void {
    try writer.writeByte('[');
    for (values, 0..) |value, index| {
        if (index != 0) try writer.writeByte(',');
        try writer.print("{d}", .{value});
    }
    try writer.writeByte(']');
}

fn medianUnsigned(
    comptime T: type,
    allocator: std.mem.Allocator,
    values: []const T,
) !T {
    if (values.len == 0) return 0;
    const sorted = try allocator.dupe(T, values);
    defer allocator.free(sorted);
    std.mem.sort(T, sorted, {}, std.sort.asc(T));
    const middle = sorted.len / 2;
    if (sorted.len % 2 != 0) return sorted[middle];
    return sorted[middle - 1] + (sorted[middle] - sorted[middle - 1]) / 2;
}

fn writeResultJSON(
    allocator: std.mem.Allocator,
    writer: *std.Io.Writer,
    result: zbench.Result,
) !void {
    try writer.print(
        "{{\"name\":\"{s}\",\"iterations\":{d},\"timing_ns_median\":{d},\"timings_ns\":",
        .{
            result.name,
            result.readings.iterations,
            try medianUnsigned(u64, allocator, result.readings.timings_ns),
        },
    );
    try writeUnsignedArray(writer, result.readings.timings_ns);
    if (result.readings.allocations) |allocations| {
        try writer.print(
            ",\"max_allocation_bytes_median\":{d},\"allocation_count_median\":{d},\"max_allocation_bytes\":",
            .{
                try medianUnsigned(usize, allocator, allocations.maxes),
                try medianUnsigned(usize, allocator, allocations.counts),
            },
        );
        try writeUnsignedArray(writer, allocations.maxes);
        try writer.writeAll(",\"allocation_counts\":");
        try writeUnsignedArray(writer, allocations.counts);
    }
    try writer.writeByte('}');
}

fn runBenchmarks(
    allocator: std.mem.Allocator,
    io: std.Io,
    benchmark: *const zbench.Benchmark,
    json_writer: ?*std.Io.Writer,
    workloads: []const OptimizerWorkload,
    emit_counters: bool,
) !void {
    try zbench.prettyPrintHeader(io, .stdout(), benchmark.max_name_len);
    if (json_writer) |writer| {
        try writer.print(
            "{{\"schema_version\":1,\"zig_version\":\"{s}\",\"target\":\"{s}-{s}\",\"optimize\":\"{s}\",\"workload_counters\":",
            .{
                builtin.zig_version_string,
                @tagName(builtin.cpu.arch),
                @tagName(builtin.os.tag),
                @tagName(builtin.mode),
            },
        );
        if (emit_counters) {
            try writer.writeByte('[');
            for (workloads, 0..) |*workload, index| {
                if (index != 0) try writer.writeByte(',');
                const counters = try measureWorkloadCounters(allocator, workload);
                try writer.print(
                    "{{\"name\":\"{s}\",\"source_bytes\":{d},\"expression_visits\":{d},\"statement_visits\":{d},\"assignments\":{d},\"forward_reference_slots\":{d},\"reverse_edges\":{d},\"live_dependency_edges\":{d},\"dependency_compactions\":{d}}}",
                    .{
                        workload.name,
                        workload.source_bytes,
                        counters.expression_visits,
                        counters.statement_visits,
                        counters.assignments,
                        counters.forward_reference_slots,
                        counters.reverse_edges,
                        counters.live_dependency_edges,
                        counters.dependency_compactions,
                    },
                );
            }
            try writer.writeByte(']');
        } else {
            try writer.writeAll("null");
        }
        try writer.writeAll(",\"benchmarks\":[");
    }

    var iterator = try benchmark.iterator();
    var result_index: usize = 0;
    while (try iterator.next(io)) |step| switch (step) {
        .progress => {},
        .result => |result| {
            defer result.deinit();
            try result.prettyPrint(io, .stdout(), benchmark.max_name_len);
            if (json_writer) |writer| {
                if (result_index != 0) try writer.writeByte(',');
                try writeResultJSON(allocator, writer, result);
            }
            result_index += 1;
        },
    };
    if (json_writer) |writer| try writer.writeAll("]}\n");
}

fn runStandardJsonSurvey(
    init: std.process.Init,
    request_path: []const u8,
    jobs: usize,
    json_path: ?[]const u8,
) !void {
    if (jobs == 0) return error.InvalidJobCount;

    const request = try std.Io.Dir.cwd().readFileAlloc(
        init.io,
        request_path,
        init.gpa,
        .limited(std.math.maxInt(usize)),
    );
    defer init.gpa.free(request);

    var parallel_backend: std.Io.Threaded = .init(std.heap.smp_allocator, .{
        .async_limit = .limited(jobs - 1),
    });
    defer parallel_backend.deinit();
    const parallel_io = parallel_backend.io();

    var dispatcher: solidity.StandardJsonDispatcher = .{};
    var response = try dispatcher.compiler().compile(std.heap.smp_allocator, .{
        .input = request,
        .io = parallel_io,
    });
    defer response.deinit();

    var parsed_response = try JsonUtil.jsonParseStrict(init.gpa, response.bytes);
    defer parsed_response.deinit();
    const response_root = switch (parsed_response) {
        .document => |*document| document.rootConst(),
        .failure => return error.InvalidCompilerResponseJson,
    };

    const request_parse_case: JsonParseCase = .{ .input = request };
    const response_parse_case: JsonParseCase = .{ .input = response.bytes };
    const response_print_case: JsonPrintCase = .{ .root = response_root };
    const compiler_case: CompilerCase = .{
        .request = request,
        .io = parallel_io,
        .use_smp_allocator = true,
    };

    var benchmark = zbench.Benchmark.init(init.gpa, .{
        .track_allocations = true,
    });
    defer benchmark.deinit();
    try benchmark.addParam(
        "JSON: parse Standard JSON request",
        &request_parse_case,
        .{ .iterations = 10 },
    );
    try benchmark.addParam(
        "JSON: parse compiler response",
        &response_parse_case,
        .{ .iterations = 3 },
    );
    try benchmark.addParam(
        "JSON: serialize compiler response (timing only)",
        &response_print_case,
        .{ .iterations = 3 },
    );
    const compiler_name = try std.fmt.allocPrint(
        init.gpa,
        "compiler: Standard JSON end-to-end ({d} jobs, timing only)",
        .{jobs},
    );
    defer init.gpa.free(compiler_name);
    try benchmark.addParam(compiler_name, &compiler_case, .{ .iterations = 1 });

    if (json_path) |path| {
        if (std.Io.Dir.path.dirname(path)) |directory|
            try std.Io.Dir.cwd().createDirPath(init.io, directory);
        var json_file = try std.Io.Dir.cwd().createFile(init.io, path, .{});
        defer json_file.close(init.io);
        var json_buffer: [4096]u8 = undefined;
        var json_file_writer: std.Io.File.Writer = .init(
            json_file,
            init.io,
            &json_buffer,
        );
        try runBenchmarks(
            init.gpa,
            init.io,
            &benchmark,
            &json_file_writer.interface,
            &.{},
            false,
        );
        try json_file_writer.interface.flush();
    } else {
        try runBenchmarks(init.gpa, init.io, &benchmark, null, &.{}, false);
    }
}

pub fn main(init: std.process.Init) !void {
    const arguments = try init.minimal.args.toSlice(init.arena.allocator());
    var json_path: ?[]const u8 = null;
    var standard_json_path: ?[]const u8 = null;
    var jobs: usize = 4;
    var emit_counters = false;
    var argument_index: usize = 1;
    while (argument_index < arguments.len) : (argument_index += 1) {
        if (std.mem.eql(u8, arguments[argument_index], "--counters")) {
            emit_counters = true;
        } else if (std.mem.eql(u8, arguments[argument_index], "--json")) {
            argument_index += 1;
            if (argument_index == arguments.len) return error.MissingJsonPath;
            json_path = arguments[argument_index];
        } else if (std.mem.eql(u8, arguments[argument_index], "--standard-json")) {
            argument_index += 1;
            if (argument_index == arguments.len) return error.MissingStandardJsonPath;
            standard_json_path = arguments[argument_index];
        } else if (std.mem.eql(u8, arguments[argument_index], "--jobs")) {
            argument_index += 1;
            if (argument_index == arguments.len) return error.MissingJobCount;
            jobs = try std.fmt.parseInt(usize, arguments[argument_index], 10);
        } else {
            return error.InvalidArgument;
        }
    }

    if (standard_json_path) |path| {
        try runStandardJsonSurvey(init, path, jobs, json_path);
        return;
    }

    const request = try chainsRequestAlloc(init.gpa);
    defer init.gpa.free(request);
    const compiler_case: CompilerCase = .{ .request = request };

    var dialect = try EVMDialect.init(init.gpa, EVMVersion.current(), false);
    defer dialect.deinit();
    const dialect_view = dialect.dialect();

    const fanout_source = try optimizer_workloads.dataFlowFanoutAlloc(init.gpa, 256);
    defer init.gpa.free(fanout_source);
    var fanout_ast = try PreparedYul.init(init.gpa, dialect_view, fanout_source);
    defer fanout_ast.deinit();

    const churn_source = try optimizer_workloads.dependencyChurnAlloc(init.gpa, 256, 16);
    defer init.gpa.free(churn_source);
    var churn_ast = try PreparedYul.init(init.gpa, dialect_view, churn_source);
    defer churn_ast.deinit();

    const branches_source = try optimizer_workloads.branchHeavyAlloc(init.gpa, 64, 32);
    defer init.gpa.free(branches_source);
    var branches_ast = try PreparedYul.init(init.gpa, dialect_view, branches_source);
    defer branches_ast.deinit();

    const environment_source = try optimizer_workloads.environmentInvalidationAlloc(init.gpa, 128);
    defer init.gpa.free(environment_source);
    var environment_ast = try PreparedYul.init(init.gpa, dialect_view, environment_source);
    defer environment_ast.deinit();

    const scopes_source = try optimizer_workloads.deepScopesAlloc(init.gpa, 128);
    defer init.gpa.free(scopes_source);
    var scopes_ast = try PreparedYul.init(init.gpa, dialect_view, scopes_source);
    defer scopes_ast.deinit();

    const cse_source = try optimizer_workloads.cseBucketsAlloc(init.gpa, 96, 96);
    defer init.gpa.free(cse_source);
    var cse_ast = try PreparedYul.init(init.gpa, dialect_view, cse_source);
    defer cse_ast.deinit();

    const switches_source = try optimizer_workloads.smallSwitchesAlloc(init.gpa, 128, 4);
    defer init.gpa.free(switches_source);
    var switches_ast = try PreparedYul.init(init.gpa, dialect_view, switches_source);
    defer switches_ast.deinit();
    const equality_case: SyntacticEqualityCase = .{
        .block = switches_ast.ast.root(),
    };

    const workloads = [_]OptimizerWorkload{
        .{
            .name = "data flow: 256 dependency fanout",
            .kind = .data_flow_ignore,
            .block = fanout_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = fanout_source.len,
        },
        .{
            .name = "data flow: 256 dependencies reassigned 16 times",
            .kind = .data_flow_ignore,
            .block = churn_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = churn_source.len,
        },
        .{
            .name = "data flow: 64-way joins with 32 facts",
            .kind = .data_flow_analyze,
            .block = branches_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = branches_source.len,
        },
        .{
            .name = "CSE: 96 repeated expressions at depth 96",
            .kind = .common_subexpression_elimination,
            .block = cse_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = cse_source.len,
        },
        .{
            .name = "data flow: invalidate 128 environment facts",
            .kind = .data_flow_analyze,
            .block = environment_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = environment_source.len,
        },
        .{
            .name = "block facts: 64-way joins with 32 facts",
            .kind = .assigned_block_facts,
            .block = branches_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = branches_source.len,
        },
        .{
            .name = "data flow: 128 nested scopes",
            .kind = .data_flow_ignore,
            .block = scopes_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = scopes_source.len,
        },
        .{
            .name = "data flow: 256 fanout with observer",
            .kind = .data_flow_observed,
            .block = fanout_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = fanout_source.len,
        },
        .{
            .name = "syntactic equality: 128 nested scopes",
            .kind = .syntactic_equality,
            .block = scopes_ast.ast.root(),
            .dialect = dialect_view,
            .source_bytes = scopes_source.len,
        },
    };

    var benchmark = zbench.Benchmark.init(init.gpa, .{
        .track_allocations = true,
    });
    defer benchmark.deinit();
    try benchmark.add(
        "ordered vector: 4096 permuted inserts",
        orderedMapInsert,
        .{ .iterations = 20 },
    );
    try benchmark.add(
        "hash map: 4096 permuted inserts",
        hashMapInsert,
        .{ .iterations = 20 },
    );
    try benchmark.add(
        "BigInt: 2048 small arithmetic groups (timing only)",
        bigIntSmallArithmetic,
        .{ .iterations = 20 },
    );
    try benchmark.add(
        "BigInt: 512 u256 arithmetic groups (timing only)",
        bigIntU256Arithmetic,
        .{ .iterations = 20 },
    );
    try benchmark.add(
        "BigInt: 512 promoted multiplications (timing only)",
        bigIntPromotionMultiply,
        .{ .iterations = 20 },
    );
    try benchmark.add(
        "BigInt: 2048 small parses",
        bigIntSmallParsing,
        .{ .iterations = 20 },
    );
    try benchmark.addParam(
        "compiler: chains.sol via IR",
        &compiler_case,
        .{ .iterations = 1 },
    );
    try benchmark.addParam(workloads[0].name, &workloads[0], .{ .iterations = 10 });
    try benchmark.addParam(workloads[1].name, &workloads[1], .{ .iterations = 10 });
    try benchmark.addParam(workloads[2].name, &workloads[2], .{ .iterations = 10 });
    try benchmark.addParam(workloads[3].name, &workloads[3], .{ .iterations = 5 });
    try benchmark.addParam(workloads[4].name, &workloads[4], .{ .iterations = 10 });
    try benchmark.addParam(workloads[5].name, &workloads[5], .{ .iterations = 10 });
    try benchmark.addParam(workloads[6].name, &workloads[6], .{ .iterations = 10 });
    try benchmark.addParam(workloads[7].name, &workloads[7], .{ .iterations = 10 });
    try benchmark.addParam(workloads[8].name, &workloads[8], .{ .iterations = 10 });
    try benchmark.addParam(
        "syntactic equality: 128 four-case switches",
        &equality_case,
        .{ .iterations = 10 },
    );

    if (json_path) |path| {
        if (std.Io.Dir.path.dirname(path)) |directory|
            try std.Io.Dir.cwd().createDirPath(init.io, directory);
        var json_file = try std.Io.Dir.cwd().createFile(init.io, path, .{});
        defer json_file.close(init.io);
        var json_buffer: [4096]u8 = undefined;
        var json_file_writer: std.Io.File.Writer = .init(
            json_file,
            init.io,
            &json_buffer,
        );
        try runBenchmarks(
            init.gpa,
            init.io,
            &benchmark,
            &json_file_writer.interface,
            &workloads,
            emit_counters,
        );
        try json_file_writer.interface.flush();
    } else {
        try runBenchmarks(
            init.gpa,
            init.io,
            &benchmark,
            null,
            &workloads,
            emit_counters,
        );
    }
}

fn chainsRequestAlloc(allocator: std.mem.Allocator) ![]u8 {
    const JSON = solidity.libsolutil.json;
    var arena_state = std.heap.ArenaAllocator.init(allocator);
    defer arena_state.deinit();
    const arena = arena_state.allocator();

    var source_entry: std.json.Value = .{ .object = .empty };
    try source_entry.object.put(arena, "content", .{
        .string = @embedFile("chains.sol"),
    });
    var sources: std.json.Value = .{ .object = .empty };
    try sources.object.put(arena, "test/benchmarks/chains.sol", source_entry);

    var optimizer: std.json.Value = .{ .object = .empty };
    try optimizer.object.put(arena, "enabled", .{ .bool = true });
    try optimizer.object.put(arena, "runs", .{ .integer = 200 });

    var artifacts = std.json.Array.init(arena);
    try artifacts.append(.{ .string = "evm.bytecode.object" });
    var contract_selection: std.json.Value = .{ .object = .empty };
    try contract_selection.object.put(arena, "*", .{ .array = artifacts });
    var output_selection: std.json.Value = .{ .object = .empty };
    try output_selection.object.put(arena, "*", contract_selection);

    var settings: std.json.Value = .{ .object = .empty };
    try settings.object.put(arena, "optimizer", optimizer);
    try settings.object.put(arena, "outputSelection", output_selection);
    try settings.object.put(arena, "viaIR", .{ .bool = true });

    var root: std.json.Value = .{ .object = .empty };
    try root.object.put(arena, "language", .{ .string = "Solidity" });
    try root.object.put(arena, "settings", settings);
    try root.object.put(arena, "sources", sources);
    return JSON.jsonCompactPrintAlloc(allocator, &root);
}
