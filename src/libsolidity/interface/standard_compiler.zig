// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Standard JSON orchestration translated from `StandardCompiler.cpp`.
//!
//! Compiles Solidity through via-IR and Yul through the EVM backend.
//! Experimental SSA-CFG code generation and ethdebug output are unsupported.

const std = @import("std");
const ArtifactOutput = @import("artifact_output.zig");
const StandardJson = @import("common").standard_json;
const SolidityAST = @import("../ast/ast.zig");
const SolidityASTBehavior = @import("../ast/ast.zig");
const SolidityAnnotations = @import("../ast/ast_annotations.zig");
const CompatibilityIdResolver = @import("../ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const SolidityTypeBehavior = @import("../ast/types.zig");
const SolidityCallGraph = @import("../ast/call_graph.zig");
const ASTJsonExporterModule = @import("../ast/ast_json_exporter.zig");
const SolidityABI = @import("abi.zig");
const SolidityFunctionCallGraph = @import("../analysis/function_call_graph.zig");
const SolidityGlobalContext = @import("../analysis/global_context.zig");
const SolidityImmutableValidator = @import("../analysis/immutable_validator.zig");
const SolidityNameResolver = @import("../analysis/name_and_type_resolver.zig");
const SolidityPostTypeChecker = @import("../analysis/post_type_checker.zig");
const SolidityPostTypeContractLevelChecker = @import("../analysis/post_type_contract_level_checker.zig");
const SolidityReferencesResolver = @import("../analysis/references_resolver.zig");
const SolidityDeclarationTypeChecker = @import("../analysis/declaration_type_checker.zig");
const SolidityContractLevelChecker = @import("../analysis/contract_level_checker.zig");
const SolidityControlFlowAnalyzer = @import("../analysis/control_flow_analyzer.zig");
const SolidityControlFlowGraph = @import("../analysis/control_flow_graph.zig");
const SolidityControlFlowGraphImplementation = @import("../analysis/control_flow_graph.zig");
const SolidityControlFlowRevertPruner = @import("../analysis/control_flow_revert_pruner.zig");
const SolidityDocStringAnalyser = @import("../analysis/doc_string_analyser.zig");
const SolidityDocStringTagParser = @import("../analysis/doc_string_tag_parser.zig");
const SolidityScoper = @import("../analysis/scoper.zig");
const SoliditySyntaxChecker = @import("../analysis/syntax_checker.zig");
const SolidityTypeChecker = @import("../analysis/type_checker.zig");
const SolidityStaticAnalyzer = @import("../analysis/static_analyzer.zig");
const SolidityViewPureChecker = @import("../analysis/view_pure_checker.zig");
const SolidityTypeProvider = @import("../ast/type_provider.zig");
const SolidityIRCommon = @import("../codegen/ir/common.zig");
const SolidityIRGenerator = @import("../codegen/ir/ir_generator.zig");
const SolidityParser = @import("../parsing/parser.zig");
const SolidityCompilerStack = @import("compiler_stack.zig");
const CodeSizeDiagnostics = @import("code_size_diagnostics.zig");
const SolidityGasEstimator = @import("gas_estimator.zig");
const SolidityImportRemapper = @import("import_remapper.zig");
const SolidityReadFile = @import("read_file.zig");
const SolidityNatspec = @import("natspec.zig");
const SolidityStorageLayout = @import("storage_layout.zig");
const CharStream = @import("../../liblangutil/char_stream.zig").CharStream;
const DebugInfoSelection = @import("../../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const Diagnostics = @import("../../liblangutil/diagnostics.zig");
const Disassemble = @import("../../libevmasm/disassemble.zig");
const EVMAssembly = @import("../../libevmasm/assembly.zig");
const EVMMeter = @import("../../libevmasm/gas_meter.zig");
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const FixedHash = @import("../../libsolutil/fixed_hash.zig");
const JSON = @import("../../libsolutil/json.zig");
const Keccak256 = @import("../../libsolutil/keccak256.zig");
const ProfilerModule = @import("../../libsolutil/profiler.zig");
const Profiler = ProfilerModule.Profiler;
const CommonIO = @import("../../libsolutil/common_io.zig");
const LinkerObjectModule = @import("../../libevmasm/linker_object.zig");
const LinkerObject = LinkerObjectModule.LinkerObject;
const CompilationOptionsModule = @import("compilation_options.zig");
const CompilationOptions = CompilationOptionsModule.CompilationOptions;
const OutputSelection = CompilationOptionsModule.OutputSelection;
const DebugSettings = @import("debug_settings.zig");
const OptimiserSettingsModule = @import("optimiser_settings.zig");
const OptimiserSettings = OptimiserSettingsModule.OptimiserSettings;
const OptimiserSuite = @import("../../libyul/optimiser/suite.zig").OptimiserSuite;
const ObjectOptimizer = @import("../../libyul/object_optimizer.zig").ObjectOptimizer;
const BackendArtifactCache = @import("../../incremental/backend_artifact_cache.zig").BackendArtifactCache;
const CompatibilityIds = @import("../../incremental/compatibility_ids.zig");
const FrontendRevisionState = @import("../../incremental/frontend_revision_state.zig").FrontendRevisionState;
const PhaseKey = @import("../../incremental/phase_key.zig");
const SourceRegistryModule = @import("../../incremental/source_registry.zig");
const SourceId = SourceRegistryModule.SourceId;
const SourceRegistry = SourceRegistryModule.SourceRegistry;
const SourceGraphModule = @import("../../incremental/source_graph.zig");
const SourceEdge = SourceGraphModule.SourceEdge;
const SourceGraph = SourceGraphModule.SourceGraph;
const SyntaxRevisionModule = @import("../../incremental/syntax_revision.zig");
const SyntaxRevision = SyntaxRevisionModule.SyntaxRevision;
const SyntaxSource = SyntaxRevisionModule.SyntaxSource;
const SemanticRevisionModule = @import("../../incremental/semantic_revision.zig");
const SemanticRevision = SemanticRevisionModule.SemanticRevision;
const SemanticDiagnosticPhase = SemanticRevisionModule.DiagnosticPhase;
const SemanticFingerprint = @import("../../incremental/semantic_fingerprint.zig");
const AsmPrinter = @import("../../libyul/asm_printer.zig");
const SourceReferenceFormatter = @import("../../liblangutil/source_reference_formatter.zig");
const StreamProvider = @import("../../liblangutil/char_stream_provider.zig");
const SynchronizedAllocator = @import("../../libsolutil/synchronized_allocator.zig").SynchronizedAllocator;
const YulStackModule = @import("../../libyul/yul_stack.zig");
const YulStack = YulStackModule.YulStack;

pub const SourceContent = struct {
    name: []const u8,
    content: []const u8,
};

const ParsedSourceIndex = struct {
    registry: *const SourceRegistry,
    graph: *const SourceGraph,
    source_ids: []SourceId,
    indices_by_active_index: []usize,
    source_ids_by_root: std.AutoHashMapUnmanaged(*const SolidityAST.Node, SourceId) = .empty,

    fn init(
        allocator: std.mem.Allocator,
        registry: *const SourceRegistry,
        graph: *const SourceGraph,
        parsed_sources: []const SolidityParser.ParseResult,
    ) !ParsedSourceIndex {
        const source_ids = try allocator.alloc(SourceId, parsed_sources.len);
        errdefer allocator.free(source_ids);
        const indices_by_active_index = try allocator.alloc(usize, graph.activeSourceCount());
        errdefer allocator.free(indices_by_active_index);
        @memset(indices_by_active_index, std.math.maxInt(usize));

        var result: ParsedSourceIndex = .{
            .registry = registry,
            .graph = graph,
            .source_ids = source_ids,
            .indices_by_active_index = indices_by_active_index,
        };
        errdefer result.source_ids_by_root.deinit(allocator);
        for (parsed_sources, 0..) |*parsed, index| {
            const source_id = registry.idForName(parsed.tree.source_name) orelse
                return error.InvalidSolidityParserState;
            const active_index = graph.activeIndex(source_id) orelse
                return error.InvalidSolidityParserState;
            if (active_index >= indices_by_active_index.len or
                indices_by_active_index[active_index] != std.math.maxInt(usize))
                return error.InvalidSolidityParserState;
            source_ids[index] = source_id;
            indices_by_active_index[active_index] = index;
            if (parsed.tree.root) |root|
                try result.source_ids_by_root.put(allocator, root, source_id);
        }
        return result;
    }

    fn deinit(self: *ParsedSourceIndex, allocator: std.mem.Allocator) void {
        self.source_ids_by_root.deinit(allocator);
        allocator.free(self.indices_by_active_index);
        allocator.free(self.source_ids);
        self.* = undefined;
    }

    fn sourceId(self: *const ParsedSourceIndex, parsed_index: usize) ?SourceId {
        if (parsed_index >= self.source_ids.len) return null;
        return self.source_ids[parsed_index];
    }

    fn parsedIndexForId(self: *const ParsedSourceIndex, source_id: SourceId) ?usize {
        const active_index = self.graph.activeIndex(source_id) orelse return null;
        if (active_index >= self.indices_by_active_index.len) return null;
        const index = self.indices_by_active_index[active_index];
        return if (index == std.math.maxInt(usize)) null else index;
    }

    fn parsedIndexForName(
        self: *const ParsedSourceIndex,
        source_name: []const u8,
    ) ?usize {
        const source_id = self.registry.idForName(source_name) orelse return null;
        return self.parsedIndexForId(source_id);
    }

    fn parsedIndexForRoot(
        self: *const ParsedSourceIndex,
        root: *const SolidityAST.Node,
    ) ?usize {
        const source_id = self.source_ids_by_root.get(root) orelse return null;
        return self.parsedIndexForId(source_id);
    }

    fn metadataSources(
        self: *const ParsedSourceIndex,
        items: []const SolidityCompilerStack.MetadataSource,
        graph: *const SourceGraph,
    ) SolidityCompilerStack.MetadataSources {
        return .{
            .items = items,
            .indices_by_active_index = self.indices_by_active_index,
            .graph = graph,
        };
    }
};

const Json = JSON.Json;
const ErrorType = Diagnostics.ErrorType;

const Fatal = struct {
    error_type: ErrorType = .JSONError,
    message: []const u8,
};

const CompilationOptionsResult = union(enum) {
    options: CompilationOptions,
    fatal: Fatal,
};

inline fn reportProgress(
    progress: ?StandardJson.ProgressReporter,
    update: StandardJson.ProgressUpdate,
) void {
    if (progress) |reporter| reporter.report(update);
}

/// Uses the layered backend cache only when a long-lived owner supplies one.
/// One-shot compilations retain the direct lowering path and avoid encoding
/// artifacts that cannot be reused after the request returns.
fn assembleAndLinkBackend(
    allocator: std.mem.Allocator,
    stack: *YulStack,
    deploy_name: ?[]const u8,
    via_ssa_cfg: bool,
    source_indices: []const EVMAssembly.SourceIndex,
    libraries: []const LinkerObjectModule.LibraryAddress,
    backend_cache: ?*BackendArtifactCache,
) !YulStackModule.MachineAssemblyPair {
    const previous_indices = stack.assembly_source_indices;
    stack.assembly_source_indices = source_indices;
    defer stack.assembly_source_indices = previous_indices;
    if (backend_cache) |cache| {
        var artifact = try cache.assemble(
            stack,
            deploy_name,
            via_ssa_cfg,
            source_indices,
        );
        errdefer artifact.deinit();
        try cache.link(&artifact, libraries);
        const result = artifact.pair;
        artifact.pair = .{};
        artifact.deinit();
        return result;
    }

    var result = try stack.assembleWithDeployed(deploy_name, via_ssa_cfg);
    errdefer result.deinit();
    if (result.creation.bytecode) |*bytecode| try bytecode.link(allocator, libraries);
    if (result.deployed.bytecode) |*bytecode| try bytecode.link(allocator, libraries);
    return result;
}

/// Compiles one validated Solidity Standard JSON request against an active
/// frontend revision. Solidity EVM output requires `settings.viaIR: true`.
pub fn compileSolidityStandardJsonAlloc(
    allocator: std.mem.Allocator,
    input: *const Json,
    loaded_sources: []const SourceContent,
    read_callback: ?SolidityReadFile.ReadCallback,
    profiler: ?*Profiler,
    progress: ?StandardJson.ProgressReporter,
    io: ?std.Io,
    shared_object_optimizer: ?*ObjectOptimizer,
    shared_backend_cache: ?*BackendArtifactCache,
    revision: *FrontendRevisionState.Revision,
) ![]u8 {
    var synchronized_allocator = SynchronizedAllocator.init(allocator);
    const compilation_allocator = if (io != null)
        synchronized_allocator.allocator()
    else
        allocator;
    var local_object_optimizer: ObjectOptimizer = undefined;
    const object_optimizer = shared_object_optimizer orelse optimizer: {
        local_object_optimizer = ObjectOptimizer.init(compilation_allocator);
        break :optimizer &local_object_optimizer;
    };
    defer if (shared_object_optimizer == null) local_object_optimizer.deinit();
    const backend_cache = shared_backend_cache;
    var output_arena = std.heap.ArenaAllocator.init(compilation_allocator);
    defer output_arena.deinit();
    const arena = output_arena.allocator();
    var parallel_artifact_arenas: std.ArrayList(*std.heap.ArenaAllocator) = .empty;
    defer {
        for (parallel_artifact_arenas.items) |artifact_arena|
            artifact_arena.deinit();
        parallel_artifact_arenas.deinit(compilation_allocator);
    }

    var output: Json = .{ .object = .empty };
    try output.object.put(arena, "errors", .{ .array = std.json.Array.init(arena) });
    const errors_value = output.object.getPtr("errors").?;

    const parsed_options = try parseSettings(
        arena,
        input,
    );
    var settings = switch (parsed_options) {
        .options => |value| value,
        .fatal => |fatal| {
            try appendError(
                arena,
                errors_value,
                fatal.error_type,
                fatal.message,
                fatal.message,
                null,
                null,
            );
            return finishOutput(allocator, &output);
        },
    };
    defer settings.deinit();
    const frontend_fingerprint = PhaseKey.frontendFingerprint(&settings);

    if (settings.frontend.evm_version_deprecation_warning) {
        const message = "Support for EVM versions older than constantinople is deprecated and will be removed in the future.";
        try appendError(arena, errors_value, .Warning, message, message, null, null);
    }

    if (requestsSolidityEvmOutput(&settings.projection.output_selection) and !settings.ir.via_ir) {
        const message = "Zig port: Solidity EVM output requires \"settings.viaIR\": true; the legacy direct-codegen pipeline is unsupported.";
        try appendError(
            arena,
            errors_value,
            .UnimplementedFeatureError,
            message,
            message,
            null,
            null,
        );
        return finishOutput(allocator, &output);
    }

    if (settings.ir.via_ssa_cfg) {
        const message = "Zig port: experimental Solidity SSA-CFG code generation is not implemented.";
        try appendError(arena, errors_value, .UnimplementedFeatureError, message, message, null, null);
        return finishOutput(allocator, &output);
    }
    if (settings.ir.debug_info.ethdebug or hasAnyEthdebugRequest(&settings.projection.output_selection)) {
        const message = "Zig port: ethdebug output is not implemented.";
        try appendError(arena, errors_value, .UnimplementedFeatureError, message, message, null, null);
        return finishOutput(allocator, &output);
    }
    if (hasExactArtifactRequest(&settings.projection.output_selection, "irAst") or
        hasExactArtifactRequest(&settings.projection.output_selection, "irOptimizedAst"))
    {
        const message = "Zig port: experimental Solidity IR AST output is not implemented.";
        try appendError(arena, errors_value, .UnimplementedFeatureError, message, message, null, null);
        return finishOutput(allocator, &output);
    }
    if (hasExactArtifactRequest(&settings.projection.output_selection, "yulCFGJson")) {
        const message = "Zig port: experimental Solidity Yul CFG JSON output is not implemented.";
        try appendError(arena, errors_value, .UnimplementedFeatureError, message, message, null, null);
        return finishOutput(allocator, &output);
    }

    const sources_value = objectMember(input, "sources") orelse {
        try appendError(arena, errors_value, .JSONError, "No input sources specified.", "No input sources specified.", null, null);
        return finishOutput(allocator, &output);
    };
    const sources = jsonObject(sources_value) orelse {
        try appendError(arena, errors_value, .JSONError, "\"sources\" is not a JSON object.", "\"sources\" is not a JSON object.", null, null);
        return finishOutput(allocator, &output);
    };

    var loaded_sources_by_name: std.StringHashMapUnmanaged([]const u8) = .empty;
    defer loaded_sources_by_name.deinit(arena);
    try loaded_sources_by_name.ensureTotalCapacity(
        arena,
        std.math.cast(u32, loaded_sources.len) orelse return error.TooManySources,
    );
    for (loaded_sources) |loaded| {
        const result = try loaded_sources_by_name.getOrPut(arena, loaded.name);
        // Preserve the existing first-match behavior for duplicate callback
        // entries while making every source-content lookup constant-time.
        if (!result.found_existing) result.value_ptr.* = loaded.content;
    }

    const source_registry = revision.registry();

    const initial_source_order = try sortedObjectIndices(arena, sources);
    for (initial_source_order) |object_index| {
        const source_name = sources.keys()[object_index];
        const source_entry = &sources.values()[object_index];
        const source_contents = resolveIndexedSource(
            source_name,
            source_entry,
            &loaded_sources_by_name,
        ) orelse {
            try appendError(arena, errors_value, .IOError, "Source callback failed.", "Source callback failed.", null, null);
            return finishOutput(allocator, &output);
        };
        if (objectMember(source_entry, "keccak256")) |hash_value| {
            if (jsonString(hash_value)) |hash| {
                if (!hashMatchesContent(hash, source_contents)) {
                    const message = try std.fmt.allocPrint(
                        arena,
                        "Mismatch between content and supplied hash for \"{s}\"",
                        .{source_name},
                    );
                    try appendError(arena, errors_value, .IOError, message, message, null, null);
                    return finishOutput(allocator, &output);
                }
            }
        }
        const registered = try source_registry.upsert(source_name, source_contents);
        try source_registry.appendParseOrder(registered.id);
    }

    var parsed_sources: std.ArrayList(SolidityParser.ParseResult) = .empty;
    defer parsed_sources.deinit(allocator);
    var candidate_syntax = try SyntaxRevision.init(
        allocator,
        source_registry.knownCount(),
    );
    var syntax_adopted = false;
    defer if (!syntax_adopted) candidate_syntax.deinit();
    var source_edges: std.ArrayList(SourceEdge) = .empty;
    defer source_edges.deinit(allocator);
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();

    var parsing_probe: ?ProfilerModule.OptionalProbe =
        ProfilerModule.OptionalProbe.init(profiler, "Solidity parsing");
    defer if (parsing_probe) |*probe| probe.deinit();
    var next_ast_id: i64 = 0;
    var source_to_parse: usize = 0;
    reportProgress(progress, .{
        .stage = .parsing_sources,
        .estimated_total_items = source_registry.parseOrder().len,
    });
    while (source_to_parse < source_registry.parseOrder().len) : (source_to_parse += 1) {
        const source_id = source_registry.parseOrder()[source_to_parse];
        const source = source_registry.record(source_id) orelse
            return error.InvalidSolidityParserState;
        reportProgress(progress, .{
            .stage = .parsing_sources,
            .completed_items = source_to_parse,
            .estimated_total_items = source_registry.parseOrder().len,
            .item_name = source.name,
        });
        try candidate_syntax.ensureSourceCapacity(source_registry.knownCount());
        const syntax_source = syntax: {
            if (revision.previousSyntax(source_id)) |previous|
                if (previous.reusableFor(
                    &source.content_digest,
                    settings.frontend.evm_version,
                )) {
                    try candidate_syntax.retainReused(source_id, previous);
                    previous.replayParseDiagnostics(&reporter) catch |err| switch (err) {
                        error.FatalDiagnostic => return finishParsingDiagnostics(allocator, arena, &output, &reporter, source_registry),
                        else => return err,
                    };
                    break :syntax previous;
                };

            const diagnostic_start = reporter.diagnostics().len;
            var parsed = try SolidityParser.parseSourceWithIdentity(
                allocator,
                source.content,
                source.name,
                &reporter,
                settings.frontend.evm_version,
                source_id,
                next_ast_id,
            );
            if (reporter.error_count > Diagnostics.ErrorReporter.max_errors_allowed) {
                // Diagnostic source names borrow the parser tree until export.
                defer parsed.deinit();
                return finishParsingDiagnostics(allocator, arena, &output, &reporter, source_registry);
            }
            const created = SyntaxSource.create(
                allocator,
                &parsed,
                source.content_digest,
                settings.frontend.evm_version,
                reporter.diagnostics()[diagnostic_start..],
            ) catch |err| {
                parsed.deinit();
                return err;
            };
            errdefer created.release();
            try candidate_syntax.adoptParsed(source_id, created);
            break :syntax created;
        };
        const node_count = std.math.cast(
            i64,
            syntax_source.parsed.tree.nodesInCreationOrder().len,
        ) orelse return error.InvalidSolidityParserState;
        next_ast_id = std.math.add(i64, next_ast_id, node_count) catch
            return error.InvalidSolidityParserState;
        try parsed_sources.append(allocator, .{ .tree = syntax_source.parsed.tree });

        const current = &parsed_sources.items[parsed_sources.items.len - 1];
        const root = current.tree.root orelse continue;
        for (root.payload.source_unit.nodes) |node| {
            if (node.nodeKind() != .import_directive) continue;
            const import = node.payload.import_directive;
            const absolute_path = try CommonIO.absolutePathAlloc(
                arena,
                import.path,
                current.tree.source_name,
            );
            const import_path = try SolidityImportRemapper.applyNormalizedRemappingsAlloc(
                arena,
                settings.frontend.remappings.items,
                absolute_path,
                current.tree.source_name,
            );
            if (source_registry.idForName(import_path)) |imported_id| {
                try source_edges.append(allocator, .{
                    .importer = source_id,
                    .imported = imported_id,
                });
                continue;
            }
            if (settings.frontend.stop_after_parsing) continue;

            var callback_result = if (read_callback) |callback|
                try callback.read(arena, .read_file, import_path)
            else
                try SolidityReadFile.ReadCallback.Result.init(
                    arena,
                    false,
                    "File not supplied initially.",
                );
            defer callback_result.deinit();
            if (!callback_result.success) {
                const message = try std.fmt.allocPrint(
                    arena,
                    "Source \"{s}\" not found: {s}",
                    .{ import_path, callback_result.response_or_error_message },
                );
                reporter.parserError(.{ .value = 6275 }, node.location, message) catch |err| switch (err) {
                    error.FatalDiagnostic => return finishParsingDiagnostics(allocator, arena, &output, &reporter, source_registry),
                    else => return err,
                };
                continue;
            }
            const imported_content = try arena.dupe(
                u8,
                callback_result.response_or_error_message,
            );
            const registered = try source_registry.upsert(import_path, imported_content);
            try source_registry.appendParseOrder(registered.id);
            try source_edges.append(allocator, .{
                .importer = source_id,
                .imported = registered.id,
            });
        }
        reportProgress(progress, .{
            .stage = .parsing_sources,
            .completed_items = source_to_parse + 1,
            .estimated_total_items = source_registry.parseOrder().len,
        });
    }
    try candidate_syntax.ensureSourceCapacity(source_registry.knownCount());
    const source_fingerprints = try arena.alloc(
        SemanticFingerprint.SourceFingerprintEntry,
        source_registry.parseOrder().len,
    );
    for (source_registry.parseOrder(), source_fingerprints) |source_id, *entry| {
        const syntax_source = candidate_syntax.get(source_id) orelse
            return error.InvalidSolidityParserState;
        entry.* = .{
            .source = source_id,
            .fingerprints = syntax_source.semantic_fingerprints,
        };
    }
    const source_graph = try revision.finish(
        source_edges.items,
        frontend_fingerprint,
        source_fingerprints,
    );
    const source_node_counts = try arena.alloc(
        CompatibilityIds.SourceNodeCount,
        source_registry.parseOrder().len,
    );
    for (source_registry.parseOrder(), source_node_counts) |source_id, *source_node_count| {
        const syntax_source = candidate_syntax.get(source_id) orelse
            return error.InvalidSolidityParserState;
        const node_count = std.math.cast(
            u32,
            syntax_source.parsed.tree.nodesInCreationOrder().len,
        ) orelse return error.InvalidSolidityParserState;
        source_node_count.* = .{ .source = source_id, .node_count = node_count };
    }
    const semantic = try revision.createSemantic(source_node_counts);
    for (source_registry.parseOrder()) |source_id| {
        const syntax_source = candidate_syntax.get(source_id) orelse
            return error.InvalidSolidityParserState;
        try semantic.retainSyntaxSource(syntax_source);
        try semantic.bindTree(&syntax_source.parsed.tree);
    }
    try revision.adoptSyntax(&candidate_syntax);
    syntax_adopted = true;
    try sortParsedSourcesByRegistry(allocator, source_registry, &parsed_sources);
    parsing_probe.?.deinit();
    parsing_probe = null;

    var parsed_source_index = try ParsedSourceIndex.init(
        allocator,
        source_registry,
        source_graph,
        parsed_sources.items,
    );
    defer parsed_source_index.deinit(allocator);
    const analyze_sources = try allocator.alloc(bool, parsed_sources.items.len);
    defer allocator.free(analyze_sources);
    var analyzed_source_count: usize = 0;
    for (parsed_sources.items, analyze_sources) |*parsed, *should_analyze| {
        should_analyze.* = !semantic.reusesPriorState() or
            revision.sourceIsDirty(parsed.tree.source_id);
        analyzed_source_count += @intFromBool(should_analyze.*);
    }

    const source_indices = try arena.alloc(
        ASTJsonExporterModule.SourceIndex,
        parsed_sources.items.len,
    );
    for (parsed_sources.items, source_indices, 0..) |*parsed, *source, index|
        source.* = .{ .name = parsed.tree.source_name, .index = index };

    const streams = try arena.alloc(CharStream, parsed_sources.items.len);
    for (parsed_sources.items, 0..) |*parsed, index|
        streams[index] = CharStream.initBorrowed(parsed.tree.source, parsed.tree.source_name);
    var provider_state: SoliditySourceProvider = .{
        .streams = streams,
        .source_index = .{ .parsed = &parsed_source_index },
    };
    const provider = provider_state.provider();

    if (reporter.hasErrors()) {
        semantic.markFailed();
        for (reporter.diagnostics()) |*diagnostic|
            try appendDiagnosticWithProvider(arena, errors_value, provider, diagnostic, true);
        try output.object.put(arena, "sources", .{ .object = .empty });
        return finishOutput(allocator, &output);
    }

    const compatibility_id_resolver = try semantic.buildCompatibilityIds(source_node_counts);

    if (!settings.frontend.stop_after_parsing) {
        const frontend_only = requestsOnlyImplementedSolidityFrontendArtifacts(
            &settings.projection.output_selection,
        );
        // Annotations retain pointers into both semantic owners. Keep them
        // alive through artifact generation and analyzed-AST serialization.
        try semantic.beginAnalysis(settings.frontend.evm_version);
        reportProgress(progress, .{ .stage = .analyzing_sources });
        semantic.setSourceCounts(
            analyzed_source_count,
            parsed_sources.items.len - analyzed_source_count,
        );
        const type_provider = try semantic.typeProvider();
        const global_context = try semantic.globalContext();
        var artifact_contracts: Json = .{ .object = .empty };
        var stack_exception = false;
        const frontend_ok = frontend: {
            var probe = ProfilerModule.OptionalProbe.init(profiler, "Solidity frontend and artifacts");
            defer probe.deinit();
            break :frontend analyzeSolidityFrontend(
                compilation_allocator,
                semantic,
                type_provider,
                global_context,
                compatibility_id_resolver,
                parsed_sources.items,
                analyze_sources,
                &parsed_source_index,
                source_graph,
                &settings,
                &reporter,
                arena,
                &artifact_contracts,
                !frontend_only,
                source_indices,
                provider,
                errors_value,
                profiler,
                progress,
                io,
                &parallel_artifact_arenas,
                compilation_allocator,
                object_optimizer,
                backend_cache,
            ) catch |err| switch (err) {
                error.FatalDiagnostic => false,
                error.StackTooDeep => recovered: {
                    // This exception occurs after successful Solidity analysis.
                    // Upstream bypasses its accumulated warnings when publishing
                    // the exception, but retains all analyzed artifacts.
                    stack_exception = true;
                    break :recovered true;
                },
                else => return err,
            };
        };
        if (stack_exception) {
            reporter.clear();
            discardSolidityCodegenArtifacts(&artifact_contracts);
        }
        if (!frontend_ok or reporter.hasErrors()) {
            semantic.markFailed();
            for (reporter.diagnostics()) |*diagnostic|
                try appendDiagnosticWithProvider(arena, errors_value, provider, diagnostic, true);
            try output.object.put(arena, "sources", .{ .object = .empty });
            return finishOutput(allocator, &output);
        }
        semantic.markAnalyzed();

        const final_errors = output.object.getPtr("errors").?;
        for (reporter.diagnostics()) |*diagnostic|
            try appendDiagnosticWithProvider(arena, final_errors, provider, diagnostic, true);

        var output_sources: Json = .{ .object = .empty };
        for (parsed_sources.items, 0..) |*parsed, source_index| {
            const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
            const source_name = parsed.tree.source_name;
            var source_result: Json = .{ .object = .empty };
            try source_result.object.put(
                arena,
                "id",
                .{ .integer = @intCast(source_index) },
            );
            if (isArtifactRequested(
                &settings.projection.output_selection,
                source_name,
                "",
                "ast",
                false,
            )) {
                var exporter = ASTJsonExporterModule.ASTJsonExporter.initAnalyzed(
                    arena,
                    source_indices,
                    source_name,
                    compatibility_id_resolver,
                    type_provider,
                );
                try source_result.object.put(arena, "ast", try exporter.toJson(root));
            }
            try output_sources.object.put(arena, source_name, source_result);
        }
        try output.object.put(arena, "sources", output_sources);
        if (artifact_contracts.object.count() != 0)
            try output.object.put(arena, "contracts", artifact_contracts);
        if (final_errors.array.items.len == 0) _ = output.object.orderedRemove("errors");
        return finishOutput(allocator, &output);
    }

    var output_sources: Json = .{ .object = .empty };
    for (parsed_sources.items, 0..) |*parsed, source_index| {
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        const source_name = parsed.tree.source_name;
        var source_result: Json = .{ .object = .empty };
        try source_result.object.put(arena, "id", .{ .integer = @intCast(source_index) });
        if (isArtifactRequested(&settings.projection.output_selection, source_name, "", "ast", true)) {
            var exporter = ASTJsonExporterModule.ASTJsonExporter.init(
                arena,
                source_indices,
                source_name,
                compatibility_id_resolver,
            );
            try source_result.object.put(arena, "ast", try exporter.toJson(root));
        }
        try output_sources.object.put(arena, source_name, source_result);
    }
    try output.object.put(arena, "sources", output_sources);

    const final_errors = output.object.getPtr("errors").?;
    for (reporter.diagnostics()) |*diagnostic|
        try appendDiagnosticWithProvider(arena, final_errors, provider, diagnostic, true);
    if (final_errors.array.items.len == 0) _ = output.object.orderedRemove("errors");
    return finishOutput(allocator, &output);
}

const SourceDfsFrame = struct {
    index: usize,
    leave: bool,
};

const ContractSource = struct {
    tree: *SolidityAST.Tree,
    source_id: SourceId,
};

const ContractSourceMap = std.AutoHashMapUnmanaged(
    *const SolidityAST.Node,
    ContractSource,
);

fn recordSemanticDiagnosticDelta(
    semantic: *SemanticRevision,
    phase: SemanticDiagnosticPhase,
    source: SourceId,
    reporter: *const Diagnostics.ErrorReporter,
    diagnostic_start: usize,
) std.mem.Allocator.Error!void {
    try semantic.recordDiagnostics(
        phase,
        source,
        reporter.diagnostics()[diagnostic_start..],
    );
}

fn reuseSemanticDiagnostics(
    semantic: *SemanticRevision,
    phase: SemanticDiagnosticPhase,
    source: SourceId,
    reporter: *Diagnostics.ErrorReporter,
) (Diagnostics.ReportError || std.mem.Allocator.Error)!void {
    const diagnostic_start = reporter.diagnostics().len;
    try semantic.replayDiagnostics(phase, source, reporter);
    try recordSemanticDiagnosticDelta(
        semantic,
        phase,
        source,
        reporter,
        diagnostic_start,
    );
}

fn analyzeSolidityFrontend(
    allocator: std.mem.Allocator,
    semantic: *SemanticRevision,
    type_provider: *SolidityTypeProvider.TypeProvider,
    global_context: *SolidityGlobalContext.GlobalContext,
    compatibility_ids: CompatibilityIdResolver,
    parsed_sources: []SolidityParser.ParseResult,
    analyze_sources: []const bool,
    parsed_source_index: *const ParsedSourceIndex,
    source_graph: *const SourceGraph,
    settings: *const CompilationOptions,
    reporter: *Diagnostics.ErrorReporter,
    artifact_allocator: std.mem.Allocator,
    artifact_contracts: *Json,
    generate_code: bool,
    source_indices: []const ASTJsonExporterModule.SourceIndex,
    source_provider: StreamProvider.CharStreamProvider,
    errors_value: *Json,
    profiler: ?*Profiler,
    progress: ?StandardJson.ProgressReporter,
    io: ?std.Io,
    parallel_artifact_arenas: *std.ArrayList(*std.heap.ArenaAllocator),
    parallel_allocator: std.mem.Allocator,
    object_optimizer: *ObjectOptimizer,
    backend_cache: ?*BackendArtifactCache,
) !bool {
    if (analyze_sources.len != parsed_sources.len)
        return error.InvalidSolidityParserState;
    const source_entries = try allocator.alloc(
        SolidityNameResolver.SourceUnitEntry,
        parsed_sources.len,
    );
    defer allocator.free(source_entries);

    for (parsed_sources, 0..) |*parsed, index| {
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        const source_annotation = try soliditySourceUnitAnnotation(&parsed.tree, root);
        if (analyze_sources[index]) {
            try source_annotation.path.assign(parsed.tree.source_name);
        } else if (!source_annotation.path.isSet() or
            !std.mem.eql(
                u8,
                (try source_annotation.path.get()).*,
                parsed.tree.source_name,
            )) return error.InvalidSolidityParserState;
        source_entries[index] = .{
            .path = parsed.tree.source_name,
            .source_unit = root,
        };
    }

    for (parsed_sources, 0..) |*parsed, source_index| {
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |node| {
            if (node.nodeKind() != .import_directive) continue;
            const annotation = try solidityImportAnnotation(&parsed.tree, node);
            if (analyze_sources[source_index]) {
                const lexical_path = try CommonIO.absolutePathAlloc(
                    allocator,
                    node.payload.import_directive.path,
                    parsed.tree.source_name,
                );
                defer allocator.free(lexical_path);
                const import_path = try SolidityImportRemapper.applyNormalizedRemappingsAlloc(
                    allocator,
                    settings.frontend.remappings.items,
                    lexical_path,
                    parsed.tree.source_name,
                );
                defer allocator.free(import_path);
                try annotation.absolute_path.assign(try parsed.tree.ownString(import_path));
            } else if (!annotation.absolute_path.isSet()) {
                return error.InvalidSolidityParserState;
            }
            const annotated_path = (try annotation.absolute_path.get()).*;
            const imported_index = parsed_source_index.parsedIndexForName(annotated_path) orelse {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "Source \"{s}\" not found: File not supplied initially.",
                    .{annotated_path},
                );
                defer allocator.free(message);
                try reporter.parserError(.{ .value = 6275 }, node.location, message);
                continue;
            };
            const imported_root = parsed_sources[imported_index].tree.root.?;
            if (analyze_sources[source_index]) {
                annotation.source_unit = imported_root;
            } else if (annotation.source_unit != imported_root) {
                try SolidityAnnotations.rebindImportSource(
                    &parsed.tree,
                    node,
                    imported_root,
                );
            }
        }
    }
    if (reporter.hasErrors()) return false;

    const source_order = try soliditySourceOrderAlloc(
        allocator,
        parsed_sources,
        parsed_source_index,
    );
    defer allocator.free(source_order);
    const analyzed_source_order_storage = try allocator.alloc(usize, source_order.len);
    defer allocator.free(analyzed_source_order_storage);
    var analyzed_source_order_len: usize = 0;
    for (source_order) |source_index| {
        if (!analyze_sources[source_index]) continue;
        analyzed_source_order_storage[analyzed_source_order_len] = source_index;
        analyzed_source_order_len += 1;
    }
    const analyzed_source_order = analyzed_source_order_storage[0..analyzed_source_order_len];
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        if (!analyze_sources[source_index]) {
            try reuseSemanticDiagnostics(
                semantic,
                .syntax,
                parsed.tree.source_id,
                reporter,
            );
            continue;
        }
        const diagnostic_start = reporter.diagnostics().len;
        try SolidityScoper.assignScopes(&parsed.tree, root);
        _ = try SoliditySyntaxChecker.checkSyntax(
            &parsed.tree,
            root,
            reporter,
            .{
                .use_yul_optimizer = settings.optimizer.settings.run_yul_optimiser,
                .experimental = settings.frontend.experimental,
            },
        );
        try recordSemanticDiagnosticDelta(
            semantic,
            .syntax,
            parsed.tree.source_id,
            reporter,
            diagnostic_start,
        );
    }
    if (reporter.hasErrors()) return false;

    var resolver = try SolidityNameResolver.NameAndTypeResolver.init(
        allocator,
        global_context,
        settings.frontend.evm_version,
        reporter,
        settings.frontend.experimental,
    );
    defer resolver.deinit();

    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        const registered = if (analyze_sources[source_index])
            try resolver.registerSource(&parsed.tree, root)
        else
            try resolver.registerSourceReusingAnnotations(&parsed.tree, root);
        if (!registered) return false;
    }
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        const imported = if (analyze_sources[source_index])
            try resolver.performImports(&parsed.tree, root, source_entries)
        else
            try resolver.performImportsReusingAnnotations(
                &parsed.tree,
                root,
                source_entries,
            );
        if (!imported) return false;
    }
    try resolver.warnHomonymDeclarations();

    var no_errors = true;
    {
        var parser = SolidityDocStringTagParser.DocStringTagParser.init(
            allocator,
            reporter,
            type_provider,
        );
        for (source_order) |source_index| {
            const parsed = @constCast(&parsed_sources[source_index]);
            const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
            if (!analyze_sources[source_index]) {
                try reuseSemanticDiagnostics(
                    semantic,
                    .doc_string_parse,
                    parsed.tree.source_id,
                    reporter,
                );
                continue;
            }
            const diagnostic_start = reporter.diagnostics().len;
            if (!(try parser.parseDocStrings(&parsed.tree, root))) no_errors = false;
            try recordSemanticDiagnosticDelta(
                semantic,
                .doc_string_parse,
                parsed.tree.source_id,
                reporter,
                diagnostic_start,
            );
        }
    }

    // Name resolution consumes parsed @inheritdoc tags.
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        if (!analyze_sources[source_index]) {
            try reuseSemanticDiagnostics(
                semantic,
                .references,
                parsed.tree.source_id,
                reporter,
            );
            continue;
        }
        const diagnostic_start = reporter.diagnostics().len;
        if (!(try SolidityReferencesResolver.resolveSource(
            &parsed.tree,
            &resolver,
            root,
        ))) return false;
        try recordSemanticDiagnosticDelta(
            semantic,
            .references,
            parsed.tree.source_id,
            reporter,
            diagnostic_start,
        );
    }
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        if (!analyze_sources[source_index]) {
            try reuseSemanticDiagnostics(
                semantic,
                .declaration_types,
                parsed.tree.source_id,
                reporter,
            );
            continue;
        }
        const diagnostic_start = reporter.diagnostics().len;
        var checker = SolidityDeclarationTypeChecker.DeclarationTypeChecker.init(
            allocator,
            &parsed.tree,
            reporter,
            type_provider,
            settings.frontend.evm_version,
        );
        defer checker.deinit();
        if (!(try checker.check(root))) return false;
        try recordSemanticDiagnosticDelta(
            semantic,
            .declaration_types,
            parsed.tree.source_id,
            reporter,
            diagnostic_start,
        );
    }
    {
        var parser = SolidityDocStringTagParser.DocStringTagParser.init(
            allocator,
            reporter,
            type_provider,
        );
        for (source_order) |source_index| {
            const parsed = @constCast(&parsed_sources[source_index]);
            const root = parsed.tree.root orelse
                return error.InvalidSolidityParserState;
            if (!analyze_sources[source_index]) {
                try reuseSemanticDiagnostics(
                    semantic,
                    .doc_string_type_validation,
                    parsed.tree.source_id,
                    reporter,
                );
                continue;
            }
            const diagnostic_start = reporter.diagnostics().len;
            if (!(try parser.validateDocStringsUsingTypes(root))) no_errors = false;
            try recordSemanticDiagnosticDelta(
                semantic,
                .doc_string_type_validation,
                parsed.tree.source_id,
                reporter,
                diagnostic_start,
            );
        }
    }
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        if (!analyze_sources[source_index]) {
            try reuseSemanticDiagnostics(
                semantic,
                .contract_level,
                parsed.tree.source_id,
                reporter,
            );
            continue;
        }
        const diagnostic_start = reporter.diagnostics().len;
        var checker = SolidityContractLevelChecker.ContractLevelChecker.init(
            allocator,
            &parsed.tree,
            type_provider,
            reporter,
        );
        checker.setCompatibilityIds(compatibility_ids);
        if (!(try checker.check(root))) no_errors = false;
        try recordSemanticDiagnosticDelta(
            semantic,
            .contract_level,
            parsed.tree.source_id,
            reporter,
            diagnostic_start,
        );
    }
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        if (!analyze_sources[source_index]) {
            try reuseSemanticDiagnostics(
                semantic,
                .type_check,
                parsed.tree.source_id,
                reporter,
            );
            continue;
        }
        const diagnostic_start = reporter.diagnostics().len;
        var checker = SolidityTypeChecker.TypeChecker.init(
            allocator,
            &parsed.tree,
            type_provider,
            settings.frontend.evm_version,
            reporter,
        );
        checker.setCompatibilityIds(compatibility_ids);
        if (!(try checker.checkTypeRequirements(root))) no_errors = false;
        try recordSemanticDiagnosticDelta(
            semantic,
            .type_check,
            parsed.tree.source_id,
            reporter,
            diagnostic_start,
        );
    }
    if (no_errors and !reporter.hasErrors()) {
        var analyzer = SolidityDocStringAnalyser.DocStringAnalyser.init(
            allocator,
            reporter,
            type_provider,
        );
        for (source_order) |source_index| {
            const parsed = @constCast(&parsed_sources[source_index]);
            const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
            if (!analyze_sources[source_index]) {
                try reuseSemanticDiagnostics(
                    semantic,
                    .doc_string_analysis,
                    parsed.tree.source_id,
                    reporter,
                );
                continue;
            }
            const diagnostic_start = reporter.diagnostics().len;
            if (!(try analyzer.analyseDocStrings(&parsed.tree, root))) no_errors = false;
            try recordSemanticDiagnosticDelta(
                semantic,
                .doc_string_analysis,
                parsed.tree.source_id,
                reporter,
                diagnostic_start,
            );
        }
    }
    if (no_errors and !reporter.hasErrors()) {
        var checker = SolidityPostTypeChecker.PostTypeChecker.init(
            allocator,
            reporter,
            type_provider,
        );
        defer checker.deinit();
        for (source_order) |source_index| {
            const parsed = @constCast(&parsed_sources[source_index]);
            const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
            if (!analyze_sources[source_index]) {
                try reuseSemanticDiagnostics(
                    semantic,
                    .post_type,
                    parsed.tree.source_id,
                    reporter,
                );
                continue;
            }
            const diagnostic_start = reporter.diagnostics().len;
            if (!(try checker.check(&parsed.tree, root))) no_errors = false;
            try recordSemanticDiagnosticDelta(
                semantic,
                .post_type,
                parsed.tree.source_id,
                reporter,
                diagnostic_start,
            );
        }
        if (!(try checker.finalize())) no_errors = false;
    }
    if (no_errors and !reporter.hasErrors()) {
        try createAndAssignSolidityCallGraphs(
            semantic,
            type_provider,
            compatibility_ids,
            parsed_sources,
            analyzed_source_order,
        );
        try findAndReportCyclicSolidityContractDependencies(
            allocator,
            parsed_sources,
            source_order,
            reporter,
        );
        if (reporter.hasErrors()) no_errors = false;
    }
    if (no_errors and !reporter.hasErrors())
        for (source_order) |source_index| {
            const parsed = @constCast(&parsed_sources[source_index]);
            const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
            if (!analyze_sources[source_index]) {
                try reuseSemanticDiagnostics(
                    semantic,
                    .post_type_contract,
                    parsed.tree.source_id,
                    reporter,
                );
                continue;
            }
            const diagnostic_start = reporter.diagnostics().len;
            var checker = SolidityPostTypeContractLevelChecker.PostTypeContractLevelChecker.init(
                allocator,
                &parsed.tree,
                reporter,
                type_provider,
            );
            if (!(try checker.check(root))) no_errors = false;
            try recordSemanticDiagnosticDelta(
                semantic,
                .post_type_contract,
                parsed.tree.source_id,
                reporter,
                diagnostic_start,
            );
        };
    if (no_errors and !reporter.hasErrors())
        for (source_order) |source_index| {
            const root = parsed_sources[source_index].tree.root orelse
                return error.InvalidSolidityParserState;
            for (root.payload.source_unit.nodes) |node| {
                if (node.nodeKind() != .contract_definition) continue;
                var validator = SolidityImmutableValidator.ImmutableValidator.init(
                    allocator,
                    reporter,
                    node,
                );
                if (!(try validator.analyze())) no_errors = false;
            }
        };
    if (no_errors and !reporter.hasErrors()) {
        var cfg = SolidityControlFlowGraph.CFG.init(allocator, reporter);
        defer cfg.deinit();
        for (source_order) |source_index| {
            const root = parsed_sources[source_index].tree.root orelse
                return error.InvalidSolidityParserState;
            if (!(try SolidityControlFlowGraphImplementation.constructFlow(&cfg, root)))
                no_errors = false;
        }
        if (no_errors and !reporter.hasErrors()) {
            var pruner = SolidityControlFlowRevertPruner.ControlFlowRevertPruner.init(
                allocator,
                &cfg,
            );
            defer pruner.deinit();
            try pruner.run();
            var analyzer = SolidityControlFlowAnalyzer.ControlFlowAnalyzer.init(
                allocator,
                &cfg,
                reporter,
            );
            defer analyzer.deinit();
            if (!(try analyzer.run())) no_errors = false;
        }
    }
    if (no_errors and !reporter.hasErrors())
        for (source_order) |source_index| {
            const parsed = @constCast(&parsed_sources[source_index]);
            const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
            var analyzer = SolidityStaticAnalyzer.StaticAnalyzer.init(
                allocator,
                &parsed.tree,
                reporter,
                type_provider,
            );
            defer analyzer.deinit();
            if (!(try analyzer.analyze(root))) no_errors = false;
        };
    if (no_errors and !reporter.hasErrors()) {
        const roots = try allocator.alloc(*SolidityAST.Node, source_order.len);
        defer allocator.free(roots);
        for (source_order, 0..) |source_index, index|
            roots[index] = parsed_sources[source_index].tree.root orelse
                return error.InvalidSolidityParserState;
        var checker = SolidityViewPureChecker.ViewPureChecker.init(allocator, reporter);
        defer checker.deinit();
        if (!(try checker.check(roots))) no_errors = false;
    }
    if (no_errors and !reporter.hasErrors()) {
        try collectSemanticDependencyMasks(
            semantic,
            source_graph,
            parsed_sources,
        );
        try appendSolidityFrontendArtifacts(
            artifact_allocator,
            type_provider,
            compatibility_ids,
            parsed_sources,
            source_order,
            &settings.projection.output_selection,
            artifact_contracts,
        );
        if (no_errors and generate_code and !(try appendSolidityViaIRArtifacts(
            allocator,
            artifact_allocator,
            type_provider,
            compatibility_ids,
            parsed_sources,
            source_order,
            settings,
            source_indices,
            parsed_source_index,
            source_graph,
            source_provider,
            artifact_contracts,
            errors_value,
            reporter,
            profiler,
            progress,
            io,
            parallel_artifact_arenas,
            parallel_allocator,
            object_optimizer,
            backend_cache,
        ))) no_errors = false;
    }
    return no_errors and !reporter.hasErrors();
}

fn collectSemanticDependencyMasks(
    semantic: *SemanticRevision,
    source_graph: *const SourceGraph,
    parsed_sources: []const SolidityParser.ParseResult,
) !void {
    try semantic.initializeDependencyMasks(source_graph);
    for (parsed_sources) |*parsed| {
        const importer = parsed.tree.source_id;
        for (parsed.tree.nodesInCreationOrder()) |node| {
            const annotation = SolidityAnnotations.annotationConst(node) orelse continue;
            switch (annotation.*) {
                .struct_declaration => |value| markDocumentedDependency(
                    semantic,
                    source_graph,
                    importer,
                    &value.type_declaration.declaration,
                    null,
                ),
                .contract_definition => |value| {
                    markDocumentedDependency(
                        semantic,
                        source_graph,
                        importer,
                        &value.type_declaration.declaration,
                        &value.documented,
                    );
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.linearized_base_contracts,
                    );
                    if (value.unimplemented_declarations) |declarations|
                        markNodeListDependencies(
                            semantic,
                            source_graph,
                            importer,
                            declarations,
                        );
                    for (value.base_constructor_arguments.items) |argument| {
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            argument.function,
                        );
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            argument.argument_node,
                        );
                    }
                    for (value.contract_dependencies.items) |dependency| {
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            dependency.contract,
                        );
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            dependency.referencing_node,
                        );
                    }
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.interface_events.items,
                    );
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.interface_errors.items,
                    );
                    if (value.creation_call_graph.value) |graph|
                        markCallGraphDependencies(
                            semantic,
                            source_graph,
                            importer,
                            graph,
                        );
                    if (value.deployed_call_graph.value) |graph|
                        markCallGraphDependencies(
                            semantic,
                            source_graph,
                            importer,
                            graph,
                        );
                },
                .documented_callable => |value| {
                    markDocumentedDependency(
                        semantic,
                        source_graph,
                        importer,
                        &value.callable.declaration,
                        &value.documented,
                    );
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.callable.base_functions.items,
                    );
                },
                .variable_declaration => |value| {
                    markDocumentedDependency(
                        semantic,
                        source_graph,
                        importer,
                        &value.declaration,
                        &value.documented,
                    );
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.base_functions.items,
                    );
                },
                .inline_assembly => |value| for (value.external_references.items) |reference|
                    if (reference.info.declaration) |declaration|
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            declaration,
                        ),
                .return_statement => |value| {
                    if (value.function_return_parameters) |parameters|
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            parameters,
                        );
                    if (value.function) |function|
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            function,
                        );
                },
                .identifier_path => |value| {
                    if (value.referenced_declaration) |declaration|
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            declaration,
                        );
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.path_declarations.items,
                    );
                },
                .identifier => |value| {
                    if (value.referenced_declaration) |declaration|
                        markSemanticDependency(
                            semantic,
                            source_graph,
                            importer,
                            declaration,
                        );
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.candidate_declarations.items,
                    );
                    markNodeListDependencies(
                        semantic,
                        source_graph,
                        importer,
                        value.overloaded_declarations.items,
                    );
                },
                .member_access => |value| if (value.referenced_declaration) |declaration|
                    markSemanticDependency(
                        semantic,
                        source_graph,
                        importer,
                        declaration,
                    ),
                .operation => |value| if (value.user_defined_function.value orelse null) |function|
                    markSemanticDependency(
                        semantic,
                        source_graph,
                        importer,
                        function,
                    ),
                .binary_operation => |value| if (value.operation.user_defined_function.value orelse null) |function|
                    markSemanticDependency(
                        semantic,
                        source_graph,
                        importer,
                        function,
                    ),
                else => {},
            }
        }
    }
}

fn markDocumentedDependency(
    semantic: *SemanticRevision,
    source_graph: *const SourceGraph,
    importer: SourceId,
    declaration: *const SolidityAnnotations.DeclarationAnnotation,
    documented: ?*const SolidityAnnotations.StructurallyDocumentedAnnotation,
) void {
    if (declaration.scopable.contract) |contract|
        markSemanticDependency(semantic, source_graph, importer, contract);
    if (documented) |value|
        if (value.inheritdoc_reference) |reference|
            markSemanticDependency(semantic, source_graph, importer, reference);
}

fn markNodeListDependencies(
    semantic: *SemanticRevision,
    source_graph: *const SourceGraph,
    importer: SourceId,
    nodes: []const *const SolidityAST.Node,
) void {
    for (nodes) |node|
        markSemanticDependency(semantic, source_graph, importer, node);
}

fn markCallGraphDependencies(
    semantic: *SemanticRevision,
    source_graph: *const SourceGraph,
    importer: SourceId,
    graph: *const SolidityCallGraph.CallGraph,
) void {
    for (graph.callers.items) |caller| markCallNodeDependency(
        semantic,
        source_graph,
        importer,
        caller,
    );
    for (graph.edges.items) |edge| {
        markCallNodeDependency(semantic, source_graph, importer, edge.caller);
        markCallNodeDependency(semantic, source_graph, importer, edge.callee);
    }
    for (graph.bytecode_dependencies.items) |dependency| {
        markSemanticDependency(semantic, source_graph, importer, dependency.contract);
        markSemanticDependency(semantic, source_graph, importer, dependency.referencing_node);
    }
    markNodeListDependencies(
        semantic,
        source_graph,
        importer,
        graph.emitted_events.items,
    );
    markNodeListDependencies(
        semantic,
        source_graph,
        importer,
        graph.used_errors.items,
    );
}

fn markCallNodeDependency(
    semantic: *SemanticRevision,
    source_graph: *const SourceGraph,
    importer: SourceId,
    node: SolidityCallGraph.Node,
) void {
    switch (node) {
        .callable => |callable| markSemanticDependency(
            semantic,
            source_graph,
            importer,
            callable,
        ),
        .special => {},
    }
}

fn markSemanticDependency(
    semantic: *SemanticRevision,
    source_graph: *const SourceGraph,
    importer: SourceId,
    declaration: *const SolidityAST.Node,
) void {
    if (declaration.location.source_name == null or
        declaration.nodeKind() == .magic_variable_declaration)
        return;
    semantic.markDependencyUsed(
        source_graph,
        importer,
        declaration.node_ref.source,
    );
}

fn appendSolidityFrontendArtifacts(
    allocator: std.mem.Allocator,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    parsed_sources: []SolidityParser.ParseResult,
    source_order: []const usize,
    output_selection: *const OutputSelection,
    contracts_output: *Json,
) !void {
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        var source_contracts: Json = .{ .object = .empty };
        for (root.payload.source_unit.nodes) |node| {
            if (node.nodeKind() != .contract_definition) continue;
            const contract_name = node.payload.contract_definition.declaration.name;
            const wants_abi = isArtifactRequested(
                output_selection,
                parsed.tree.source_name,
                contract_name,
                "abi",
                false,
            );
            const wants_devdoc = isArtifactRequested(
                output_selection,
                parsed.tree.source_name,
                contract_name,
                "devdoc",
                false,
            );
            const wants_userdoc = isArtifactRequested(
                output_selection,
                parsed.tree.source_name,
                contract_name,
                "userdoc",
                false,
            );
            const wants_storage_layout = isArtifactRequested(
                output_selection,
                parsed.tree.source_name,
                contract_name,
                "storageLayout",
                false,
            );
            const wants_transient_storage_layout = isArtifactRequested(
                output_selection,
                parsed.tree.source_name,
                contract_name,
                "transientStorageLayout",
                false,
            );
            const wants_method_identifiers = isArtifactRequested(
                output_selection,
                parsed.tree.source_name,
                contract_name,
                "evm.methodIdentifiers",
                false,
            );
            if (!wants_abi and !wants_devdoc and !wants_userdoc and
                !wants_storage_layout and !wants_transient_storage_layout and
                !wants_method_identifiers) continue;
            var contract_result: Json = .{ .object = .empty };
            if (wants_abi)
                try contract_result.object.put(
                    allocator,
                    "abi",
                    try SolidityABI.ABI.generate(
                        allocator,
                        type_provider,
                        compatibility_ids,
                        &parsed.tree,
                        node,
                    ),
                );
            if (wants_devdoc)
                try contract_result.object.put(
                    allocator,
                    "devdoc",
                    try SolidityNatspec.Natspec.devDocumentation(
                        allocator,
                        type_provider,
                        compatibility_ids,
                        node,
                    ),
                );
            if (wants_userdoc)
                try contract_result.object.put(
                    allocator,
                    "userdoc",
                    try SolidityNatspec.Natspec.userDocumentation(
                        allocator,
                        type_provider,
                        compatibility_ids,
                        node,
                    ),
                );
            if (wants_storage_layout)
                try contract_result.object.put(
                    allocator,
                    "storageLayout",
                    try SolidityStorageLayout.generate(
                        allocator,
                        type_provider,
                        compatibility_ids,
                        node,
                        .Storage,
                    ),
                );
            if (wants_transient_storage_layout)
                try contract_result.object.put(
                    allocator,
                    "transientStorageLayout",
                    try SolidityStorageLayout.generate(
                        allocator,
                        type_provider,
                        compatibility_ids,
                        node,
                        .Transient,
                    ),
                );
            if (wants_method_identifiers) {
                var evm: Json = .{ .object = .empty };
                try evm.object.put(
                    allocator,
                    "methodIdentifiers",
                    try solidityMethodIdentifiers(
                        allocator,
                        type_provider,
                        node,
                    ),
                );
                try contract_result.object.put(allocator, "evm", evm);
            }
            try source_contracts.object.put(allocator, contract_name, contract_result);
        }
        if (source_contracts.object.count() != 0)
            try contracts_output.object.put(
                allocator,
                parsed.tree.source_name,
                source_contracts,
            );
    }
}

fn solidityMethodIdentifiers(
    allocator: std.mem.Allocator,
    type_provider: *SolidityTypeProvider.TypeProvider,
    contract: *const SolidityAST.Node,
) !Json {
    const functions = try SolidityASTBehavior.contractInterfaceFunctionsAlloc(
        type_provider,
        allocator,
        contract,
        true,
    );
    defer allocator.free(functions);
    var result: Json = .{ .object = .empty };
    for (functions) |function| {
        if (function.function_type.payload != .Function)
            return error.InvalidSolidityParserState;
        const signature = try SolidityTypeBehavior.externalSignatureAlloc(
            type_provider,
            allocator,
            function.function_type.payload.Function,
        );
        const selector = function.selector.hex();
        try result.object.put(
            allocator,
            signature,
            try ownedString(allocator, &selector),
        );
    }
    return result;
}

fn appendSolidityViaIRArtifacts(
    scratch_allocator: std.mem.Allocator,
    allocator: std.mem.Allocator,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    parsed_sources: []SolidityParser.ParseResult,
    source_order: []const usize,
    settings: *const CompilationOptions,
    source_indices: []const ASTJsonExporterModule.SourceIndex,
    parsed_source_index: *const ParsedSourceIndex,
    source_graph: *const SourceGraph,
    source_provider: StreamProvider.CharStreamProvider,
    contracts_output: *Json,
    errors_value: *Json,
    reporter: *Diagnostics.ErrorReporter,
    profiler: ?*Profiler,
    progress: ?StandardJson.ProgressReporter,
    io: ?std.Io,
    parallel_artifact_arenas: *std.ArrayList(*std.heap.ArenaAllocator),
    parallel_allocator: std.mem.Allocator,
    object_optimizer: *ObjectOptimizer,
    backend_cache: ?*BackendArtifactCache,
) !bool {
    var via_ir_probe = ProfilerModule.OptionalProbe.init(profiler, "Solidity via-IR artifacts");
    defer via_ir_probe.deinit();
    const assembly_source_codes = try scratch_allocator.alloc(
        EVMAssembly.SourceCode,
        parsed_sources.len,
    );
    defer scratch_allocator.free(assembly_source_codes);
    const assembly_source_indices = try scratch_allocator.alloc(
        EVMAssembly.SourceIndex,
        parsed_sources.len + 1,
    );
    defer scratch_allocator.free(assembly_source_indices);
    for (parsed_sources, assembly_source_codes, assembly_source_indices[0..parsed_sources.len], 0..) |*parsed, *source_code, *source_index, index| {
        source_code.* = .{
            .name = parsed.tree.source_name,
            .code = parsed.tree.source,
        };
        source_index.* = .{
            .source_name = parsed.tree.source_name,
            .index = @intCast(index),
        };
    }
    assembly_source_indices[parsed_sources.len] = .{
        .source_name = "#utility.yul",
        .index = @intCast(parsed_sources.len),
    };

    const ir_source_indices = try scratch_allocator.alloc(
        AsmPrinter.SourceIndexName,
        source_indices.len,
    );
    defer scratch_allocator.free(ir_source_indices);
    for (source_indices, ir_source_indices) |source, *target| {
        target.* = .{
            .index = std.math.cast(u32, source.index) orelse
                return error.InvalidSolidityParserState,
            .name = source.name,
        };
    }
    const metadata_source_items = try scratch_allocator.alloc(
        SolidityCompilerStack.MetadataSource,
        parsed_sources.len,
    );
    defer scratch_allocator.free(metadata_source_items);
    for (parsed_sources, metadata_source_items, 0..) |*parsed, *source, source_index| {
        source.* = .{
            .id = parsed_source_index.sourceId(source_index) orelse
                return error.InvalidSolidityParserState,
            .tree = &parsed.tree,
            .root = parsed.tree.root orelse return error.InvalidSolidityParserState,
        };
    }
    const metadata_sources = parsed_source_index.metadataSources(
        metadata_source_items,
        source_graph,
    );
    const metadata_options: SolidityCompilerStack.MetadataOptions = .{
        .evm_version = settings.frontend.evm_version,
        .optimiser = settings.optimizer.settings,
        .bytecode_hash = settings.metadata.hash,
        .append_cbor = settings.metadata.append_cbor,
        .use_literal_sources = settings.metadata.literal_sources,
        .via_ir = settings.ir.via_ir,
        .experimental = settings.frontend.experimental,
        .via_ssa_cfg = settings.ir.via_ssa_cfg,
        .revert_strings = settings.ir.revert_strings,
        .libraries = settings.link.libraries.items,
        .remappings = settings.frontend.remappings.items,
    };
    var contract_sources: ContractSourceMap = .empty;
    defer contract_sources.deinit(scratch_allocator);
    var contract_count: usize = 0;
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |node| {
            if (node.nodeKind() != .contract_definition) continue;
            try contract_sources.put(scratch_allocator, node, .{
                .tree = &parsed.tree,
                .source_id = metadata_sources.items[source_index].id,
            });
            contract_count += 1;
        }
    }
    var other_yul_objects: SolidityIRGenerator.OtherYulObjects = .empty;
    defer {
        var sources = other_yul_objects.valueIterator();
        while (sources.next()) |source| {
            // Each owner is counted once; borrowed dependency edges add no
            // capacity to its arena. Workers have joined before this teardown.
            if (profiler) |value|
                value.recordCounter("Generated Yul owner retained bytes", source.*.arena.queryCapacity());
            source.*.destroy(scratch_allocator);
        }
        other_yul_objects.deinit(scratch_allocator);
    }

    if (io) |parallel_io|
        if (appendSolidityViaIRArtifactsParallel(
            scratch_allocator,
            allocator,
            type_provider,
            compatibility_ids,
            parsed_sources,
            source_order,
            settings,
            source_provider,
            contracts_output,
            errors_value,
            reporter,
            assembly_source_codes,
            assembly_source_indices,
            ir_source_indices,
            metadata_sources,
            metadata_options,
            &contract_sources,
            &other_yul_objects,
            parallel_io,
            parallel_artifact_arenas,
            parallel_allocator,
            profiler,
            progress,
            contract_count,
            object_optimizer,
            backend_cache,
        ) catch |err| {
            if (err == error.StackTooDeep)
                try completeSolidityMetadata(allocator, scratch_allocator, type_provider, compatibility_ids, parsed_sources, source_order, &settings.projection.output_selection, metadata_sources, metadata_options, contracts_output);
            return err;
        }) |parallel_result| return parallel_result;

    var completed_contracts: usize = 0;
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |contract| {
            if (contract.nodeKind() != .contract_definition) continue;
            const contract_name = contract.payload.contract_definition.declaration.name;
            reportProgress(progress, .{
                .stage = .generating_contracts,
                .completed_items = completed_contracts,
                .estimated_total_items = contract_count,
                .item_name = contract_name,
            });
            defer {
                completed_contracts += 1;
                reportProgress(progress, .{
                    .stage = .generating_contracts,
                    .completed_items = completed_contracts,
                    .estimated_total_items = contract_count,
                });
            }
            const wants_ir = isArtifactRequested(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "ir",
                true,
            );
            const wants_optimized_ir = isArtifactRequested(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "irOptimized",
                true,
            );
            const wants_metadata = isArtifactRequested(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "metadata",
                true,
            );
            const wants_bytecode = requestsMachineObject(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "bytecode",
                false,
            ) or requestsMachineObject(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "deployedBytecode",
                true,
            );
            const wants_assembly = isArtifactRequested(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "evm.assembly",
                true,
            );
            const wants_legacy_assembly = isArtifactRequested(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "evm.legacyAssembly",
                true,
            );
            const wants_gas_estimates = isArtifactRequested(
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "evm.gasEstimates",
                true,
            );
            if (!wants_ir and !wants_optimized_ir and !wants_bytecode and
                !wants_metadata and !wants_assembly and
                !wants_legacy_assembly and !wants_gas_estimates) continue;

            const contract_output = try ensureArtifactContract(
                allocator,
                contracts_output,
                parsed.tree.source_name,
                contract_name,
            );
            const metadata_json = SolidityCompilerStack.createMetadataAlloc(
                scratch_allocator,
                type_provider,
                compatibility_ids,
                metadata_sources,
                metadata_sources.items[source_index].id,
                &parsed.tree,
                contract,
                metadata_options,
            ) catch |err| {
                if (err == error.OutOfMemory) return error.OutOfMemory;
                const message = try std.fmt.allocPrint(
                    allocator,
                    "Zig port: Solidity metadata generation does not yet support this contract ({s}).",
                    .{@errorName(err)},
                );
                try appendError(
                    allocator,
                    errors_value,
                    .UnimplementedFeatureError,
                    message,
                    message,
                    null,
                    null,
                );
                return false;
            };
            defer scratch_allocator.free(metadata_json);
            if (wants_metadata)
                try contract_output.object.put(
                    allocator,
                    "metadata",
                    try ownedString(allocator, metadata_json),
                );
            if (!wants_ir and !wants_optimized_ir and !wants_bytecode and
                !wants_assembly and !wants_legacy_assembly and
                !wants_gas_estimates) continue;

            const contract_definition = contract.payload.contract_definition;
            if (contract_definition.abstract or
                contract_definition.contract_kind == .Interface)
            {
                if (wants_ir)
                    try contract_output.object.put(
                        allocator,
                        "ir",
                        try ownedString(allocator, ""),
                    );
                if (wants_optimized_ir)
                    try contract_output.object.put(
                        allocator,
                        "irOptimized",
                        try ownedString(allocator, ""),
                    );
                try appendEmptyMachineObject(
                    allocator,
                    contract_output,
                    &settings.projection.output_selection,
                    parsed.tree.source_name,
                    contract_name,
                    "bytecode",
                    false,
                );
                try appendEmptyMachineObject(
                    allocator,
                    contract_output,
                    &settings.projection.output_selection,
                    parsed.tree.source_name,
                    contract_name,
                    "deployedBytecode",
                    true,
                );
                const evm = if (wants_assembly or wants_legacy_assembly or
                    wants_gas_estimates)
                    try ensureObject(allocator, contract_output, "evm")
                else
                    null;
                if (wants_assembly)
                    try evm.?.object.put(
                        allocator,
                        "assembly",
                        try ownedString(allocator, ""),
                    );
                if (wants_legacy_assembly)
                    try evm.?.object.put(allocator, "legacyAssembly", .null);
                if (wants_gas_estimates)
                    try evm.?.object.put(allocator, "gasEstimates", .null);
                continue;
            }

            const cbor_metadata = SolidityCompilerStack.createCBORMetadataAlloc(
                scratch_allocator,
                metadata_json,
                metadata_options,
            ) catch |err| {
                if (err == error.OutOfMemory) return error.OutOfMemory;
                const message = try std.fmt.allocPrint(
                    allocator,
                    "Zig port: Solidity CBOR metadata generation failed ({s}).",
                    .{@errorName(err)},
                );
                try appendError(
                    allocator,
                    errors_value,
                    .CompilerError,
                    message,
                    message,
                    null,
                    null,
                );
                return false;
            };
            defer scratch_allocator.free(cbor_metadata);

            const ir = ir_generation: {
                var probe = ProfilerModule.OptionalProbe.init(profiler, "Solidity IR generation");
                defer probe.deinit();
                break :ir_generation generateSolidityYulCached(
                    scratch_allocator,
                    type_provider,
                    compatibility_ids,
                    contract,
                    &contract_sources,
                    metadata_sources,
                    metadata_options,
                    ir_source_indices,
                    settings,
                    source_provider,
                    cbor_metadata,
                    &other_yul_objects,
                    0,
                ) catch |err| {
                    if (err == error.OutOfMemory) return error.OutOfMemory;
                    const message = try std.fmt.allocPrint(
                        allocator,
                        "Zig port: via-IR lowering does not yet support this contract ({s}).",
                        .{@errorName(err)},
                    );
                    try appendError(
                        allocator,
                        errors_value,
                        .UnimplementedFeatureError,
                        message,
                        message,
                        null,
                        null,
                    );
                    return false;
                };
            };
            if (wants_ir)
                try contract_output.object.put(
                    allocator,
                    "ir",
                    .{ .string = try ir.render(allocator, settings.ir.debug_info, source_provider) },
                );

            var stack = try YulStack.init(
                scratch_allocator,
                settings.frontend.evm_version,
                settings.optimizer.settings,
                settings.ir.debug_info,
                source_provider,
                object_optimizer,
            );
            defer stack.deinit();
            stack.setProfiler(profiler);
            const generated_source_name = parsed.tree.source_name;
            const successful = yul_parse: {
                var probe = ProfilerModule.OptionalProbe.init(profiler, "Yul preparation and analysis");
                defer probe.deinit();
                break :yul_parse try stack.analyzeGenerated(generated_source_name, ir);
            };
            if (!successful and !stack.hasErrors()) return error.InvalidYulStackState;
            if (!successful or stack.hasErrors()) {
                for (stack.errors()) |*diagnostic|
                    try appendDiagnostic(
                        allocator,
                        errors_value,
                        &stack,
                        generated_source_name,
                        diagnostic,
                    );
                return false;
            }

            {
                var probe = ProfilerModule.OptionalProbe.init(profiler, "Yul optimizer total");
                defer probe.deinit();
                stack.optimizeTypedSolidity() catch |err| {
                    const message = try std.fmt.allocPrint(
                        allocator,
                        "Yul optimizer failed: {s}",
                        .{@errorName(err)},
                    );
                    try appendError(
                        allocator,
                        errors_value,
                        .YulException,
                        message,
                        message,
                        null,
                        null,
                    );
                    return false;
                };
            }
            const deployed_object_name = try SolidityIRCommon.deployedObjectAlloc(
                scratch_allocator,
                compatibility_ids,
                contract,
            );
            defer scratch_allocator.free(deployed_object_name);
            var assembly_pair = yul_assembly: {
                var probe = ProfilerModule.OptionalProbe.init(profiler, "Yul assembly");
                defer probe.deinit();
                break :yul_assembly assembleAndLinkBackend(
                    scratch_allocator,
                    &stack,
                    deployed_object_name,
                    false,
                    assembly_source_indices,
                    settings.link.libraries.items,
                    backend_cache,
                ) catch |err| {
                    if (err == error.OutOfMemory) return error.OutOfMemory;
                    if (err == error.StackTooDeep and stack.hasErrors()) {
                        errors_value.array.clearRetainingCapacity();
                        for (stack.errors()) |*diagnostic|
                            if (diagnostic.error_type == .YulException)
                                try appendDiagnosticWithProvider(allocator, errors_value, source_provider, diagnostic, false);
                        try completeSolidityMetadata(allocator, scratch_allocator, type_provider, compatibility_ids, parsed_sources, source_order, &settings.projection.output_selection, metadata_sources, metadata_options, contracts_output);
                        return error.StackTooDeep;
                    }
                    const message = try std.fmt.allocPrint(
                        allocator,
                        "Yul code generation failed: {s}",
                        .{@errorName(err)},
                    );
                    try appendError(
                        allocator,
                        errors_value,
                        .YulException,
                        message,
                        message,
                        null,
                        null,
                    );
                    return false;
                };
            };
            defer assembly_pair.deinit();
            if (wants_bytecode or wants_assembly or wants_legacy_assembly or wants_gas_estimates)
                try CodeSizeDiagnostics.report(scratch_allocator, reporter, contract.location, settings.frontend.evm_version, .{
                    .creation = assembly_pair.creation.bytecode.?.bytecode.items.len,
                    .deployed = assembly_pair.deployed.bytecode.?.bytecode.items.len,
                });

            var machine_output: Json = .{ .object = .empty };
            try appendMachineObject(
                allocator,
                &machine_output,
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "bytecode",
                false,
                &assembly_pair.creation,
                settings.frontend.evm_version,
                true,
            );
            try appendMachineObject(
                allocator,
                &machine_output,
                &settings.projection.output_selection,
                parsed.tree.source_name,
                contract_name,
                "deployedBytecode",
                true,
                &assembly_pair.deployed,
                settings.frontend.evm_version,
                true,
            );
            if (artifactContract(
                &machine_output,
                parsed.tree.source_name,
                contract_name,
            )) |generated_contract|
                try ArtifactOutput.mergeContract(allocator, contract_output, generated_contract);

            if (wants_assembly or wants_legacy_assembly or wants_gas_estimates) {
                const evm = try ensureObject(allocator, contract_output, "evm");
                const creation_assembly = assembly_pair.creation.assembly() orelse
                    return error.MissingAssembly;
                if (wants_assembly) {
                    try evm.object.put(
                        allocator,
                        "assembly",
                        .{ .string = try creation_assembly.assemblyStringAllocWithScratch(
                            allocator,
                            scratch_allocator,
                            settings.ir.debug_info,
                            assembly_source_codes,
                        ) },
                    );
                }
                if (wants_legacy_assembly)
                    try evm.object.put(
                        allocator,
                        "legacyAssembly",
                        try creation_assembly.assemblyJSONValue(
                            allocator,
                            assembly_source_indices,
                            true,
                        ),
                    );
                if (wants_gas_estimates)
                    try evm.object.put(
                        allocator,
                        "gasEstimates",
                        try solidityGasEstimates(
                            allocator,
                            type_provider,
                            compatibility_ids,
                            contract,
                            &assembly_pair,
                            settings.frontend.evm_version,
                        ),
                    );
            }

            if (wants_optimized_ir) {
                try contract_output.object.put(
                    allocator,
                    "irOptimized",
                    .{ .string = try stack.printAlloc(allocator) },
                );
            }
        }
    }
    return true;
}

/// Complete only requested metadata after a stack exception. Successful builds
/// keep their existing preparation path; failed workers can release their large
/// artifact arenas instead of retaining them just for small metadata strings.
fn completeSolidityMetadata(
    allocator: std.mem.Allocator,
    scratch_allocator: std.mem.Allocator,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    parsed_sources: []SolidityParser.ParseResult,
    source_order: []const usize,
    output_selection: *const OutputSelection,
    metadata_sources: SolidityCompilerStack.MetadataSources,
    metadata_options: SolidityCompilerStack.MetadataOptions,
    contracts_output: *Json,
) !void {
    for (source_order) |source_index| {
        const parsed = &parsed_sources[source_index];
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |contract| {
            if (contract.nodeKind() != .contract_definition) continue;
            const name = contract.payload.contract_definition.declaration.name;
            if (!isArtifactRequested(output_selection, parsed.tree.source_name, name, "metadata", true)) continue;
            const output = try ensureArtifactContract(allocator, contracts_output, parsed.tree.source_name, name);
            if (output.object.contains("metadata")) continue;
            const metadata = try SolidityCompilerStack.createMetadataAlloc(
                scratch_allocator,
                type_provider,
                compatibility_ids,
                metadata_sources,
                metadata_sources.items[source_index].id,
                &parsed.tree,
                contract,
                metadata_options,
            );
            defer scratch_allocator.free(metadata);
            try output.object.put(allocator, "metadata", try ownedString(allocator, metadata));
        }
    }
}

fn discardSolidityCodegenArtifacts(contracts_output: *Json) void {
    var file_index: usize = 0;
    while (file_index < contracts_output.object.count()) {
        const contracts = &contracts_output.object.values()[file_index];
        var contract_index: usize = 0;
        while (contract_index < contracts.object.count()) {
            const output = &contracts.object.values()[contract_index];
            _ = output.object.orderedRemove("ir");
            _ = output.object.orderedRemove("irOptimized");
            if (output.object.getPtr("evm")) |evm| {
                for ([_][]const u8{ "bytecode", "deployedBytecode", "assembly", "legacyAssembly", "gasEstimates" }) |field|
                    _ = evm.object.orderedRemove(field);
                if (evm.object.count() == 0) _ = output.object.orderedRemove("evm");
            }
            if (output.object.count() == 0) {
                _ = contracts.object.orderedRemove(contracts.object.keys()[contract_index]);
            } else contract_index += 1;
        }
        if (contracts.object.count() == 0) {
            _ = contracts_output.object.orderedRemove(contracts_output.object.keys()[file_index]);
        } else file_index += 1;
    }
}

const ParallelViaIRRequests = struct {
    wants_ir: bool,
    wants_optimized_ir: bool,
    wants_metadata: bool,
    wants_bytecode: bool,
    wants_assembly: bool,
    wants_legacy_assembly: bool,
    wants_gas_estimates: bool,

    fn any(self: ParallelViaIRRequests) bool {
        return self.wants_ir or self.wants_optimized_ir or
            self.wants_metadata or self.wants_bytecode or
            self.wants_assembly or self.wants_legacy_assembly or
            self.wants_gas_estimates;
    }

    fn needsBackend(self: ParallelViaIRRequests) bool {
        return self.wants_ir or self.wants_optimized_ir or
            self.wants_bytecode or self.wants_assembly or
            self.wants_legacy_assembly or self.wants_gas_estimates;
    }
};

const ParallelViaIRFailure = union(enum) {
    out_of_memory,
    internal,
    optimizer: []const u8,
    assembly: []const u8,
    diagnostics,
    stack_too_deep,
};

const ParallelProgress = struct {
    reporter: ?StandardJson.ProgressReporter,
    completed_items: usize = 0,
    total_items: usize,
    mutex: std.Io.Mutex = .init,

    fn reportCurrent(self: *ParallelProgress, item_name: []const u8) void {
        const reporter = self.reporter orelse return;
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        reporter.report(.{
            .stage = .generating_contracts,
            .completed_items = self.completed_items,
            .estimated_total_items = self.total_items,
            .item_name = item_name,
        });
    }

    fn complete(self: *ParallelProgress, item_name: []const u8) void {
        const reporter = self.reporter orelse return;
        std.Io.Threaded.mutexLock(&self.mutex);
        defer std.Io.Threaded.mutexUnlock(&self.mutex);
        self.completed_items += 1;
        reporter.report(.{
            .stage = .generating_contracts,
            .completed_items = self.completed_items,
            .estimated_total_items = self.total_items,
            .item_name = item_name,
        });
    }
};

const ParallelGroup = struct {
    io: std.Io,
    group: std.Io.Group = .init,
    pending: bool = true,
    before_cancel_context: ?*anyopaque = null,
    before_cancel_fn: ?*const fn (?*anyopaque) void = null,

    fn init(io: std.Io) ParallelGroup {
        return .{ .io = io };
    }

    fn async(
        self: *ParallelGroup,
        comptime function: anytype,
        args: std.meta.ArgsTuple(@TypeOf(function)),
    ) void {
        self.group.async(self.io, function, args);
    }

    fn await(self: *ParallelGroup) !void {
        try self.group.await(self.io);
        self.pending = false;
    }

    fn deinit(self: *ParallelGroup) void {
        if (!self.pending) return;
        if (self.before_cancel_fn) |before_cancel|
            before_cancel(self.before_cancel_context);
        self.group.cancel(self.io);
        self.pending = false;
    }
};

const ParallelGroupTestHarness = struct {
    const Control = struct {
        owner_thread: std.Thread.Id,
        started: std.atomic.Value(bool) = .init(false),
        release: std.atomic.Value(bool) = .init(false),
        cleanup_started: std.atomic.Value(bool) = .init(false),
        observed_outstanding: std.atomic.Value(bool) = .init(false),
        finished: std.atomic.Value(bool) = .init(false),
        ran_inline: std.atomic.Value(bool) = .init(false),
    };

    fn run(control: *Control) void {
        if (std.Thread.getCurrentId() == control.owner_thread) {
            control.ran_inline.store(true, .release);
            return;
        }
        control.started.store(true, .release);
        while (!control.release.load(.acquire))
            std.atomic.spinLoopHint();
        control.finished.store(true, .release);
    }

    fn beforeCancel(context: ?*anyopaque) void {
        const control: *Control = @ptrCast(@alignCast(context.?));
        control.observed_outstanding.store(
            control.started.load(.acquire) and !control.finished.load(.acquire),
            .release,
        );
        control.cleanup_started.store(true, .release);
        control.release.store(true, .release);
    }
};

test "parallel group cancellation joins an outstanding async worker" {
    var threaded: std.Io.Threaded = .init(std.testing.allocator, .{
        .async_limit = .limited(1),
    });
    defer threaded.deinit();

    var control: ParallelGroupTestHarness.Control = .{
        .owner_thread = std.Thread.getCurrentId(),
    };
    var group: ParallelGroup = .init(threaded.io());
    defer group.deinit();
    group.before_cancel_context = &control;
    group.before_cancel_fn = ParallelGroupTestHarness.beforeCancel;
    group.async(ParallelGroupTestHarness.run, .{&control});

    while (!control.started.load(.acquire) and !control.ran_inline.load(.acquire))
        std.atomic.spinLoopHint();
    group.deinit();

    try std.testing.expect(!control.ran_inline.load(.acquire));
    try std.testing.expect(control.cleanup_started.load(.acquire));
    try std.testing.expect(control.observed_outstanding.load(.acquire));
    try std.testing.expect(control.finished.load(.acquire));
}

const ParallelViaIRJob = struct {
    artifact_arena: *std.heap.ArenaAllocator,
    artifact_arena_transferred: bool = false,
    output: Json = .{ .object = .empty },
    diagnostics: Json = .null,
    bytecode_sizes: ?CodeSizeDiagnostics.Sizes = null,
    contract: *const SolidityAST.Node,
    compatibility_ids: CompatibilityIdResolver,
    source_name: []const u8,
    contract_name: []const u8,
    ir: ?*const SolidityIRGenerator.GeneratedObject = null,
    requests: ParallelViaIRRequests,
    settings: *const CompilationOptions,
    source_provider: StreamProvider.CharStreamProvider,
    assembly_source_codes: []const EVMAssembly.SourceCode,
    assembly_source_indices: []const EVMAssembly.SourceIndex,
    parallel_allocator: std.mem.Allocator,
    profiler: ?*Profiler,
    progress: *ParallelProgress,
    object_optimizer: *ObjectOptimizer,
    backend_cache: ?*BackendArtifactCache,
    failure: ?ParallelViaIRFailure = null,

    fn run(self: *ParallelViaIRJob, scratch_allocator: std.mem.Allocator) !void {
        const artifact_allocator = self.artifact_arena.allocator();
        var stack = try YulStack.init(
            scratch_allocator,
            self.settings.frontend.evm_version,
            self.settings.optimizer.settings,
            self.settings.ir.debug_info,
            self.source_provider,
            self.object_optimizer,
        );
        defer stack.deinit();
        // Backend analyses end before their emitted assembly is published.
        // Back their per-object arenas directly so child storage is reclaimed
        // rather than retained in the worker's AST/assembly arena.
        stack.backend_scratch_backing_allocator = self.parallel_allocator;
        stack.setProfiler(self.profiler);

        const successful = yul_parse: {
            var probe = ProfilerModule.OptionalProbe.init(
                self.profiler,
                "Yul preparation and analysis",
            );
            defer probe.deinit();
            break :yul_parse try stack.analyzeGenerated(self.source_name, self.ir.?);
        };
        if (!successful and !stack.hasErrors()) return error.InvalidYulStackState;
        if (!successful or stack.hasErrors()) {
            self.diagnostics = .{ .array = std.json.Array.init(artifact_allocator) };
            for (stack.errors()) |*diagnostic|
                try appendDiagnostic(
                    artifact_allocator,
                    &self.diagnostics,
                    &stack,
                    self.source_name,
                    diagnostic,
                );
            self.failure = .diagnostics;
            return;
        }

        {
            var probe = ProfilerModule.OptionalProbe.init(
                self.profiler,
                "Yul optimizer total",
            );
            defer probe.deinit();
            stack.optimizeTypedSolidity() catch |err| {
                self.failure = if (err == error.OutOfMemory)
                    .out_of_memory
                else
                    .{ .optimizer = @errorName(err) };
                return;
            };
        }
        const deployed_object_name = try SolidityIRCommon.deployedObjectAlloc(
            scratch_allocator,
            self.compatibility_ids,
            self.contract,
        );
        defer scratch_allocator.free(deployed_object_name);
        var assembly_pair = yul_assembly: {
            var probe = ProfilerModule.OptionalProbe.init(
                self.profiler,
                "Yul assembly",
            );
            defer probe.deinit();
            break :yul_assembly assembleAndLinkBackend(
                scratch_allocator,
                &stack,
                deployed_object_name,
                false,
                self.assembly_source_indices,
                self.settings.link.libraries.items,
                self.backend_cache,
            ) catch |err| {
                if (err == error.StackTooDeep and stack.hasErrors()) {
                    self.diagnostics = .{ .array = std.json.Array.init(artifact_allocator) };
                    for (stack.errors()) |*diagnostic|
                        if (diagnostic.error_type == .YulException)
                            try appendDiagnosticWithProvider(artifact_allocator, &self.diagnostics, self.source_provider, diagnostic, false);
                    self.failure = .stack_too_deep;
                    return;
                }
                self.failure = if (err == error.OutOfMemory)
                    .out_of_memory
                else
                    .{ .assembly = @errorName(err) };
                return;
            };
        };
        defer assembly_pair.deinit();
        if (self.requests.wants_bytecode or self.requests.wants_assembly or self.requests.wants_legacy_assembly or self.requests.wants_gas_estimates)
            self.bytecode_sizes = .{
                .creation = assembly_pair.creation.bytecode.?.bytecode.items.len,
                .deployed = assembly_pair.deployed.bytecode.?.bytecode.items.len,
            };

        var machine_output: Json = .{ .object = .empty };
        try appendMachineObject(
            artifact_allocator,
            &machine_output,
            &self.settings.projection.output_selection,
            self.source_name,
            self.contract_name,
            "bytecode",
            false,
            &assembly_pair.creation,
            self.settings.frontend.evm_version,
            true,
        );
        try appendMachineObject(
            artifact_allocator,
            &machine_output,
            &self.settings.projection.output_selection,
            self.source_name,
            self.contract_name,
            "deployedBytecode",
            true,
            &assembly_pair.deployed,
            self.settings.frontend.evm_version,
            true,
        );
        if (artifactContract(
            &machine_output,
            self.source_name,
            self.contract_name,
        )) |generated_contract|
            try mergeObject(artifact_allocator, &self.output, generated_contract);

        if (self.requests.wants_assembly or self.requests.wants_legacy_assembly) {
            const evm = try ensureObject(artifact_allocator, &self.output, "evm");
            const creation_assembly = assembly_pair.creation.assembly() orelse
                return error.MissingAssembly;
            if (self.requests.wants_assembly) {
                try evm.object.put(
                    artifact_allocator,
                    "assembly",
                    .{ .string = try creation_assembly.assemblyStringAllocWithScratch(
                        artifact_allocator,
                        scratch_allocator,
                        self.settings.ir.debug_info,
                        self.assembly_source_codes,
                    ) },
                );
            }
            if (self.requests.wants_legacy_assembly)
                try evm.object.put(
                    artifact_allocator,
                    "legacyAssembly",
                    try creation_assembly.assemblyJSONValue(
                        artifact_allocator,
                        self.assembly_source_indices,
                        true,
                    ),
                );
        }

        if (self.requests.wants_optimized_ir) {
            try self.output.object.put(
                artifact_allocator,
                "irOptimized",
                .{ .string = try stack.printAlloc(artifact_allocator) },
            );
        }
    }
};

fn parallelViaIRRequests(
    settings: *const CompilationOptions,
    source_name: []const u8,
    contract_name: []const u8,
) ParallelViaIRRequests {
    return .{
        .wants_ir = isArtifactRequested(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "ir",
            true,
        ),
        .wants_optimized_ir = isArtifactRequested(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "irOptimized",
            true,
        ),
        .wants_metadata = isArtifactRequested(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "metadata",
            true,
        ),
        .wants_bytecode = requestsMachineObject(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "bytecode",
            false,
        ) or requestsMachineObject(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "deployedBytecode",
            true,
        ),
        .wants_assembly = isArtifactRequested(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "evm.assembly",
            true,
        ),
        .wants_legacy_assembly = isArtifactRequested(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "evm.legacyAssembly",
            true,
        ),
        .wants_gas_estimates = isArtifactRequested(
            &settings.projection.output_selection,
            source_name,
            contract_name,
            "evm.gasEstimates",
            true,
        ),
    };
}

fn runParallelViaIRJob(job: *ParallelViaIRJob) void {
    defer job.progress.complete(job.contract_name);
    var scratch_arena = std.heap.ArenaAllocator.init(job.parallel_allocator);
    defer scratch_arena.deinit();
    job.run(scratch_arena.allocator()) catch |err| {
        job.failure = if (err == error.OutOfMemory)
            .out_of_memory
        else
            .internal;
    };
    if (job.profiler) |profiler| {
        // job.run has released its logical owners. These are retained arena
        // capacities before teardown/publication, not live bytes or peak RSS.
        profiler.recordCounter("Backend worker scratch retained bytes", scratch_arena.queryCapacity());
        profiler.recordCounter("Backend worker artifact retained bytes", job.artifact_arena.queryCapacity());
    }
}

fn appendSolidityViaIRArtifactsParallel(
    scratch_allocator: std.mem.Allocator,
    allocator: std.mem.Allocator,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    parsed_sources: []SolidityParser.ParseResult,
    source_order: []const usize,
    settings: *const CompilationOptions,
    source_provider: StreamProvider.CharStreamProvider,
    contracts_output: *Json,
    errors_value: *Json,
    reporter: *Diagnostics.ErrorReporter,
    assembly_source_codes: []const EVMAssembly.SourceCode,
    assembly_source_indices: []const EVMAssembly.SourceIndex,
    ir_source_indices: []const AsmPrinter.SourceIndexName,
    metadata_sources: SolidityCompilerStack.MetadataSources,
    metadata_options: SolidityCompilerStack.MetadataOptions,
    contract_sources: *const ContractSourceMap,
    other_yul_objects: *SolidityIRGenerator.OtherYulObjects,
    io: std.Io,
    artifact_arenas: *std.ArrayList(*std.heap.ArenaAllocator),
    parallel_allocator: std.mem.Allocator,
    profiler: ?*Profiler,
    progress: ?StandardJson.ProgressReporter,
    contract_count: usize,
    object_optimizer: *ObjectOptimizer,
    backend_cache: ?*BackendArtifactCache,
) !?bool {
    var selected_count: usize = 0;
    var backend_job_count: usize = 0;
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |contract| {
            if (contract.nodeKind() != .contract_definition) continue;
            const requests = parallelViaIRRequests(
                settings,
                parsed.tree.source_name,
                contract.payload.contract_definition.declaration.name,
            );
            if (requests.wants_gas_estimates) return null;
            if (!requests.any()) continue;
            selected_count += 1;
            const definition = contract.payload.contract_definition;
            if (!definition.abstract and definition.contract_kind != .Interface and
                requests.needsBackend()) backend_job_count += 1;
        }
    }
    if (backend_job_count < 2) return null;

    var jobs: std.ArrayList(ParallelViaIRJob) = .empty;
    defer {
        for (jobs.items) |*job|
            if (!job.artifact_arena_transferred) job.artifact_arena.deinit();
        jobs.deinit(scratch_allocator);
    }
    try jobs.ensureTotalCapacity(scratch_allocator, selected_count);

    var group: ParallelGroup = .init(io);
    defer group.deinit();
    var parallel_progress: ParallelProgress = .{
        .reporter = progress,
        .total_items = contract_count,
    };
    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |contract| {
            if (contract.nodeKind() != .contract_definition) continue;
            const contract_name = contract.payload.contract_definition.declaration.name;
            parallel_progress.reportCurrent(contract_name);
            const requests = parallelViaIRRequests(
                settings,
                parsed.tree.source_name,
                contract_name,
            );
            if (!requests.any()) {
                parallel_progress.complete(contract_name);
                continue;
            }

            {
                var job: ParallelViaIRJob = .{
                    .artifact_arena = try ArtifactOutput.createArena(allocator, parallel_allocator),
                    .contract = contract,
                    .compatibility_ids = compatibility_ids,
                    .source_name = parsed.tree.source_name,
                    .contract_name = contract_name,
                    .requests = requests,
                    .settings = settings,
                    .source_provider = source_provider,
                    .assembly_source_codes = assembly_source_codes,
                    .assembly_source_indices = assembly_source_indices,
                    .parallel_allocator = parallel_allocator,
                    .profiler = profiler,
                    .progress = &parallel_progress,
                    .object_optimizer = object_optimizer,
                    .backend_cache = backend_cache,
                };
                // Diagnostics may return false without an error. Keep local
                // ownership until the job list takes over on every exit path.
                var owns_artifact_arena = true;
                defer if (owns_artifact_arena) job.artifact_arena.deinit();
                const artifact_allocator = job.artifact_arena.allocator();

                const metadata_json = SolidityCompilerStack.createMetadataAlloc(
                    scratch_allocator,
                    type_provider,
                    compatibility_ids,
                    metadata_sources,
                    metadata_sources.items[source_index].id,
                    &parsed.tree,
                    contract,
                    metadata_options,
                ) catch |err| {
                    if (err == error.OutOfMemory) return error.OutOfMemory;
                    const message = try std.fmt.allocPrint(
                        allocator,
                        "Zig port: Solidity metadata generation does not yet support this contract ({s}).",
                        .{@errorName(err)},
                    );
                    try appendError(
                        allocator,
                        errors_value,
                        .UnimplementedFeatureError,
                        message,
                        message,
                        null,
                        null,
                    );
                    return false;
                };
                defer scratch_allocator.free(metadata_json);
                if (requests.wants_metadata)
                    try job.output.object.put(
                        artifact_allocator,
                        "metadata",
                        try ownedString(artifact_allocator, metadata_json),
                    );
                if (!requests.needsBackend()) {
                    jobs.appendAssumeCapacity(job);
                    owns_artifact_arena = false;
                    parallel_progress.complete(contract_name);
                    continue;
                }

                const definition = contract.payload.contract_definition;
                if (definition.abstract or definition.contract_kind == .Interface) {
                    if (requests.wants_ir)
                        try job.output.object.put(
                            artifact_allocator,
                            "ir",
                            try ownedString(artifact_allocator, ""),
                        );
                    if (requests.wants_optimized_ir)
                        try job.output.object.put(
                            artifact_allocator,
                            "irOptimized",
                            try ownedString(artifact_allocator, ""),
                        );
                    try appendEmptyMachineObject(
                        artifact_allocator,
                        &job.output,
                        &settings.projection.output_selection,
                        parsed.tree.source_name,
                        contract_name,
                        "bytecode",
                        false,
                    );
                    try appendEmptyMachineObject(
                        artifact_allocator,
                        &job.output,
                        &settings.projection.output_selection,
                        parsed.tree.source_name,
                        contract_name,
                        "deployedBytecode",
                        true,
                    );
                    const evm = if (requests.wants_assembly or
                        requests.wants_legacy_assembly)
                        try ensureObject(artifact_allocator, &job.output, "evm")
                    else
                        null;
                    if (requests.wants_assembly)
                        try evm.?.object.put(
                            artifact_allocator,
                            "assembly",
                            try ownedString(artifact_allocator, ""),
                        );
                    if (requests.wants_legacy_assembly)
                        try evm.?.object.put(artifact_allocator, "legacyAssembly", .null);
                    jobs.appendAssumeCapacity(job);
                    owns_artifact_arena = false;
                    parallel_progress.complete(contract_name);
                    continue;
                }

                const cbor_metadata = SolidityCompilerStack.createCBORMetadataAlloc(
                    scratch_allocator,
                    metadata_json,
                    metadata_options,
                ) catch |err| {
                    if (err == error.OutOfMemory) return error.OutOfMemory;
                    const message = try std.fmt.allocPrint(
                        allocator,
                        "Zig port: Solidity CBOR metadata generation failed ({s}).",
                        .{@errorName(err)},
                    );
                    try appendError(
                        allocator,
                        errors_value,
                        .CompilerError,
                        message,
                        message,
                        null,
                        null,
                    );
                    return false;
                };
                defer scratch_allocator.free(cbor_metadata);
                const ir = ir_generation: {
                    var probe = ProfilerModule.OptionalProbe.init(
                        profiler,
                        "Solidity IR generation",
                    );
                    defer probe.deinit();
                    break :ir_generation generateSolidityYulCached(
                        scratch_allocator,
                        type_provider,
                        compatibility_ids,
                        contract,
                        contract_sources,
                        metadata_sources,
                        metadata_options,
                        ir_source_indices,
                        settings,
                        source_provider,
                        cbor_metadata,
                        other_yul_objects,
                        0,
                    ) catch |err| {
                        if (err == error.OutOfMemory) return error.OutOfMemory;
                        const message = try std.fmt.allocPrint(
                            allocator,
                            "Zig port: via-IR lowering does not yet support this contract ({s}).",
                            .{@errorName(err)},
                        );
                        try appendError(
                            allocator,
                            errors_value,
                            .UnimplementedFeatureError,
                            message,
                            message,
                            null,
                            null,
                        );
                        return false;
                    };
                };
                if (requests.wants_ir)
                    try job.output.object.put(
                        artifact_allocator,
                        "ir",
                        .{ .string = try ir.render(artifact_allocator, settings.ir.debug_info, source_provider) },
                    );
                job.ir = ir;
                jobs.appendAssumeCapacity(job);
                owns_artifact_arena = false;
                group.async(
                    runParallelViaIRJob,
                    .{&jobs.items[jobs.items.len - 1]},
                );
            }
        }
    }

    try group.await();

    for (jobs.items) |*job| {
        const failure = job.failure orelse continue;
        switch (failure) {
            .out_of_memory => return error.OutOfMemory,
            .internal => return error.ParallelBackendFailure,
            .optimizer => |error_name| {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "Yul optimizer failed: {s}",
                    .{error_name},
                );
                try appendError(
                    allocator,
                    errors_value,
                    .YulException,
                    message,
                    message,
                    null,
                    null,
                );
                return false;
            },
            .assembly => |error_name| {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "Yul code generation failed: {s}",
                    .{error_name},
                );
                try appendError(
                    allocator,
                    errors_value,
                    .YulException,
                    message,
                    message,
                    null,
                    null,
                );
                return false;
            },
            .diagnostics, .stack_too_deep => {
                try artifact_arenas.append(scratch_allocator, job.artifact_arena);
                job.artifact_arena_transferred = true;
                if (failure == .stack_too_deep) errors_value.array.clearRetainingCapacity();
                for (job.diagnostics.array.items) |diagnostic|
                    try errors_value.array.append(diagnostic);
                if (failure == .stack_too_deep) return error.StackTooDeep;
                return false;
            },
        }
    }

    for (jobs.items) |*job| {
        if (job.bytecode_sizes) |sizes|
            try CodeSizeDiagnostics.report(scratch_allocator, reporter, job.contract.location, settings.frontend.evm_version, sizes);
        try artifact_arenas.append(scratch_allocator, job.artifact_arena);
        job.artifact_arena_transferred = true;
        const contract_output = try ensureArtifactContract(
            allocator,
            contracts_output,
            job.source_name,
            job.contract_name,
        );
        try ArtifactOutput.mergeContract(allocator, contract_output, &job.output);
    }
    return true;
}

fn solidityGasEstimates(
    allocator: std.mem.Allocator,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const SolidityAST.Node,
    assembly_pair: *const YulStackModule.MachineAssemblyPair,
    evm_version: EVMVersion,
) !Json {
    var output: Json = .{ .object = .empty };
    const estimator = SolidityGasEstimator.GasEstimator.init(
        allocator,
        evm_version,
    );

    if (assembly_pair.creation.assembly()) |creation_assembly| {
        const execution = try estimator.functionalEstimation(
            creation_assembly.itemsConst(),
            "",
        );
        const runtime_bytecode = if (assembly_pair.deployed.bytecode) |*value|
            value.bytecode.items
        else
            &.{};
        const deposit: SolidityGasEstimator.GasConsumption = .{
            .value = EVMMeter.dataGas(runtime_bytecode, false, evm_version),
        };
        var creation: Json = .{ .object = .empty };
        try creation.object.put(
            allocator,
            "codeDepositCost",
            try gasConsumptionJson(allocator, deposit),
        );
        try creation.object.put(
            allocator,
            "executionCost",
            try gasConsumptionJson(allocator, execution),
        );
        try creation.object.put(
            allocator,
            "totalCost",
            try gasConsumptionJson(allocator, execution.plus(deposit)),
        );
        try output.object.put(allocator, "creation", creation);
    }

    const runtime_assembly = assembly_pair.deployed.assembly() orelse return output;
    var external_functions: Json = .{ .object = .empty };
    const functions = try SolidityASTBehavior.contractInterfaceFunctionsAlloc(
        type_provider,
        allocator,
        contract,
        true,
    );
    defer allocator.free(functions);
    for (functions) |function| {
        const function_type = switch (function.function_type.payload) {
            .Function => |value| value,
            else => return error.InvalidSolidityParserState,
        };
        const signature = try SolidityTypeBehavior.externalSignatureAlloc(
            type_provider,
            allocator,
            function_type,
        );
        const gas = try estimator.functionalEstimation(
            runtime_assembly.itemsConst(),
            signature,
        );
        try external_functions.object.put(
            allocator,
            signature,
            try gasConsumptionJson(allocator, gas),
        );
    }
    if (try SolidityASTBehavior.contractFallbackFunction(contract) != null) {
        const gas = try estimator.functionalEstimation(
            runtime_assembly.itemsConst(),
            "INVALID",
        );
        try external_functions.object.put(
            allocator,
            "",
            try gasConsumptionJson(allocator, gas),
        );
    }
    if (external_functions.object.count() != 0)
        try output.object.put(allocator, "external", external_functions);

    var internal_functions: Json = .{ .object = .empty };
    for (contract.payload.contract_definition.sub_nodes) |function| {
        if (function.nodeKind() != .function_definition or
            function.isPartOfExternalInterface() or
            !function.payload.function_definition.ordinary()) continue;
        const entry = solidityFunctionEntryPoint(
            if (assembly_pair.deployed.bytecode) |*bytecode| bytecode else null,
            compatibility_ids,
            function,
        );
        const gas = if (entry > 0)
            try estimator.functionalEstimationForFunction(
                runtime_assembly.itemsConst(),
                entry,
                function,
            )
        else
            SolidityGasEstimator.GasConsumption.infinite();
        const signature = try solidityInternalFunctionSignatureAlloc(
            allocator,
            function,
        );
        try internal_functions.object.put(
            allocator,
            signature,
            try gasConsumptionJson(allocator, gas),
        );
    }
    if (internal_functions.object.count() != 0)
        try output.object.put(allocator, "internal", internal_functions);
    return output;
}

fn gasConsumptionJson(
    allocator: std.mem.Allocator,
    gas: SolidityGasEstimator.GasConsumption,
) !Json {
    if (gas.is_infinite) return ownedString(allocator, "infinite");
    const value = try std.fmt.allocPrint(allocator, "{d}", .{gas.value});
    return .{ .string = value };
}

fn solidityFunctionEntryPoint(
    bytecode: ?*const LinkerObject,
    compatibility_ids: CompatibilityIdResolver,
    function: *const SolidityAST.Node,
) usize {
    const object = bytecode orelse return 0;
    const projected_id = compatibility_ids.id(function) orelse return 0;
    if (projected_id < 0) return 0;
    const function_id: usize = @intCast(projected_id);
    for (object.function_debug_data.items) |entry|
        if (entry.data.source_id == function_id)
            return entry.data.instruction_index orelse 0;
    return 0;
}

fn solidityInternalFunctionSignatureAlloc(
    allocator: std.mem.Allocator,
    function: *const SolidityAST.Node,
) ![]u8 {
    const definition = function.payload.function_definition;
    const parameters = definition.callable.parameters;
    if (parameters.nodeKind() != .parameter_list)
        return error.InvalidSolidityParserState;
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try output.appendSlice(allocator, definition.callable.declaration.name);
    try output.append(allocator, '(');
    for (parameters.payload.parameter_list.parameters, 0..) |parameter, index| {
        if (index != 0) try output.append(allocator, ',');
        const annotation = SolidityAnnotations.annotationConst(parameter) orelse
            return error.InvalidSolidityParserState;
        const type_ref = switch (annotation.*) {
            .variable_declaration => |value| value.type_ref,
            else => null,
        } orelse return error.InvalidSolidityParserState;
        const rendered = try SolidityTypeBehavior.toStringAlloc(
            allocator,
            type_ref,
            false,
        );
        defer allocator.free(rendered);
        try output.appendSlice(allocator, rendered);
    }
    try output.append(allocator, ')');
    return output.toOwnedSlice(allocator);
}

fn generateSolidityYulCached(
    allocator: std.mem.Allocator,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    contract: *const SolidityAST.Node,
    contract_sources: *const ContractSourceMap,
    metadata_sources: SolidityCompilerStack.MetadataSources,
    metadata_options: SolidityCompilerStack.MetadataOptions,
    ir_source_indices: []const AsmPrinter.SourceIndexName,
    settings: *const CompilationOptions,
    source_provider: StreamProvider.CharStreamProvider,
    cbor_metadata_override: ?[]const u8,
    other_yul_objects: *SolidityIRGenerator.OtherYulObjects,
    depth: usize,
) !*const SolidityIRGenerator.GeneratedObject {
    if (other_yul_objects.get(contract)) |source| return source;
    if (depth >= 256) return error.InvalidSolidityParserState;
    const contract_source = contract_sources.get(contract) orelse
        return error.InvalidSolidityParserState;
    const annotation = try solidityContractAnnotationConst(contract);
    for (annotation.contract_dependencies.items) |dependency|
        _ = try generateSolidityYulCached(
            allocator,
            type_provider,
            compatibility_ids,
            dependency.contract,
            contract_sources,
            metadata_sources,
            metadata_options,
            ir_source_indices,
            settings,
            source_provider,
            null,
            other_yul_objects,
            depth + 1,
        );

    var owned_cbor_metadata: ?[]u8 = null;
    defer if (owned_cbor_metadata) |metadata| allocator.free(metadata);
    const cbor_metadata = cbor_metadata_override orelse metadata: {
        const metadata_json = try SolidityCompilerStack.createMetadataAlloc(
            allocator,
            type_provider,
            compatibility_ids,
            metadata_sources,
            contract_source.source_id,
            contract_source.tree,
            @constCast(contract),
            metadata_options,
        );
        defer allocator.free(metadata_json);
        owned_cbor_metadata = try SolidityCompilerStack.createCBORMetadataAlloc(
            allocator,
            metadata_json,
            metadata_options,
        );
        break :metadata owned_cbor_metadata.?;
    };

    var generator = try SolidityIRGenerator.IRGenerator.init(
        allocator,
        type_provider,
        compatibility_ids,
        settings.frontend.evm_version,
        settings.ir.revert_strings,
        ir_source_indices,
        settings.ir.debug_info,
        source_provider,
        settings.optimizer.settings,
    );
    defer generator.deinit();
    const ir = try generator.run(
        contract_source.tree,
        @constCast(contract),
        cbor_metadata,
        other_yul_objects,
    );
    errdefer ir.destroy(allocator);
    try other_yul_objects.put(allocator, contract, ir);
    return ir;
}

fn ensureArtifactContract(
    allocator: std.mem.Allocator,
    contracts: *Json,
    source_name: []const u8,
    contract_name: []const u8,
) !*Json {
    if (contracts.* != .object) return error.InvalidSolidityParserState;
    const source = if (contracts.object.getPtr(source_name)) |existing|
        existing
    else created: {
        try contracts.object.put(allocator, source_name, .{ .object = .empty });
        break :created contracts.object.getPtr(source_name).?;
    };
    if (source.* != .object) return error.InvalidSolidityParserState;
    if (source.object.getPtr(contract_name)) |existing| return existing;
    try source.object.put(allocator, contract_name, .{ .object = .empty });
    return source.object.getPtr(contract_name).?;
}

fn artifactContract(
    output: *Json,
    source_name: []const u8,
    contract_name: []const u8,
) ?*const Json {
    const contracts = objectMember(output, "contracts") orelse return null;
    const source = objectMember(contracts, source_name) orelse return null;
    return objectMember(source, contract_name);
}

fn mergeObject(
    allocator: std.mem.Allocator,
    destination: *Json,
    source: *const Json,
) !void {
    if (destination.* != .object or source.* != .object)
        return error.InvalidSolidityParserState;
    for (source.object.keys(), source.object.values()) |key, value|
        try destination.object.put(allocator, key, value);
}

fn createAndAssignSolidityCallGraphs(
    semantic: *SemanticRevision,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    parsed_sources: []SolidityParser.ParseResult,
    source_order: []const usize,
) !void {
    var contract_count: usize = 0;
    for (source_order) |source_index| {
        const root = parsed_sources[source_index].tree.root orelse
            return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |node|
            if (node.nodeKind() == .contract_definition) {
                contract_count += 1;
            };
    }
    try semantic.call_graphs.ensureUnusedCapacity(
        semantic.semanticAllocator(),
        contract_count,
    );

    for (source_order) |source_index| {
        const parsed = @constCast(&parsed_sources[source_index]);
        const root = parsed.tree.root orelse return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |node| {
            if (node.nodeKind() != .contract_definition) continue;
            const graphs = try buildAndAssignSolidityCallGraphs(
                semantic,
                type_provider,
                compatibility_ids,
                parsed.tree.allocator(),
                node,
            );
            _ = graphs;
        }
    }
}

fn buildAndAssignSolidityCallGraphs(
    semantic: *SemanticRevision,
    type_provider: *SolidityTypeProvider.TypeProvider,
    compatibility_ids: CompatibilityIdResolver,
    annotation_allocator: std.mem.Allocator,
    contract: *SolidityAST.Node,
) !*SemanticRevisionModule.ContractCallGraphs {
    const allocator = semantic.semanticAllocator();
    var creation = try SolidityFunctionCallGraph.FunctionCallGraphBuilder.buildCreationGraph(
        allocator,
        type_provider,
        contract,
        compatibility_ids,
    );
    var graphs_adopted = false;
    errdefer if (!graphs_adopted) creation.deinit();
    var deployed = try SolidityFunctionCallGraph.FunctionCallGraphBuilder.buildDeployedGraph(
        allocator,
        type_provider,
        contract,
        &creation,
        compatibility_ids,
    );
    errdefer if (!graphs_adopted) deployed.deinit();
    const graphs = try semantic.adoptCallGraphs(&creation, &deployed);
    graphs_adopted = true;

    const annotation = try solidityContractAnnotation(contract);
    if (annotation.contract_dependencies.items.len != 0 or
        annotation.internal_function_ids.items.len != 0)
        return error.InvalidSolidityParserState;
    try mergeSolidityContractDependencies(
        annotation_allocator,
        &annotation.contract_dependencies,
        graphs.creation.bytecode_dependencies.items,
    );
    try mergeSolidityContractDependencies(
        annotation_allocator,
        &annotation.contract_dependencies,
        graphs.deployed.bytecode_dependencies.items,
    );
    try mergeSolidityInterfaceDeclarations(
        annotation_allocator,
        compatibility_ids,
        &annotation.interface_events,
        graphs.creation.emitted_events.items,
    );
    try mergeSolidityInterfaceDeclarations(
        annotation_allocator,
        compatibility_ids,
        &annotation.interface_events,
        graphs.deployed.emitted_events.items,
    );
    try mergeSolidityInterfaceDeclarations(
        annotation_allocator,
        compatibility_ids,
        &annotation.interface_errors,
        graphs.creation.used_errors.items,
    );
    try mergeSolidityInterfaceDeclarations(
        annotation_allocator,
        compatibility_ids,
        &annotation.interface_errors,
        graphs.deployed.used_errors.items,
    );
    try annotateSolidityInternalFunctionIds(
        annotation_allocator,
        annotation,
        &graphs.deployed,
        &graphs.creation,
    );
    try annotation.creation_call_graph.assign(&graphs.creation);
    try annotation.deployed_call_graph.assign(&graphs.deployed);
    return graphs;
}

fn mergeSolidityInterfaceDeclarations(
    allocator: std.mem.Allocator,
    compatibility_ids: CompatibilityIdResolver,
    declarations: *std.ArrayList(*const SolidityAST.Node),
    additions: []const *const SolidityAST.Node,
) !void {
    for (additions) |addition| {
        var exists = false;
        for (declarations.items) |declaration|
            if (declaration == addition) {
                exists = true;
                break;
            };
        if (!exists) try declarations.append(allocator, addition);
    }
    std.sort.insertion(*const SolidityAST.Node, declarations.items, compatibility_ids, struct {
        fn lessThan(
            resolver: CompatibilityIdResolver,
            left: *const SolidityAST.Node,
            right: *const SolidityAST.Node,
        ) bool {
            return resolver.id(left).? < resolver.id(right).?;
        }
    }.lessThan);
}

fn mergeSolidityContractDependencies(
    allocator: std.mem.Allocator,
    dependencies: *std.ArrayList(SolidityAnnotations.ContractDependency),
    additions: []const SolidityCallGraph.BytecodeDependency,
) !void {
    for (additions) |addition| {
        var exists = false;
        for (dependencies.items) |dependency|
            if (dependency.contract == addition.contract) {
                exists = true;
                break;
            };
        if (!exists) try dependencies.append(allocator, .{
            .contract = addition.contract,
            .referencing_node = addition.referencing_node,
        });
    }
}

fn annotateSolidityInternalFunctionIds(
    allocator: std.mem.Allocator,
    annotation: *SolidityAnnotations.ContractDefinitionAnnotation,
    deployed: *const SolidityCallGraph.CallGraph,
    creation: *const SolidityCallGraph.CallGraph,
) !void {
    var next_id: u64 = 1;
    for (deployed.edges.items) |edge| {
        if (!SolidityCallGraph.Node.eql(
            edge.caller,
            .{ .special = .InternalDispatch },
        )) continue;
        const callable = switch (edge.callee) {
            .callable => |value| value,
            .special => return error.InvalidSolidityParserState,
        };
        if (callable.nodeKind() != .function_definition) continue;
        if (solidityInternalFunctionId(annotation, callable) != null) continue;
        try annotation.internal_function_ids.append(allocator, .{
            .function = callable,
            .id = next_id,
        });
        next_id += 1;
    }
    for (creation.edges.items) |edge| {
        if (!SolidityCallGraph.Node.eql(
            edge.caller,
            .{ .special = .InternalDispatch },
        )) continue;
        const callable = switch (edge.callee) {
            .callable => |value| value,
            .special => return error.InvalidSolidityParserState,
        };
        if (callable.nodeKind() == .function_definition and
            solidityInternalFunctionId(annotation, callable) == null)
            return error.InvalidSolidityParserState;
    }
}

fn solidityInternalFunctionId(
    annotation: *const SolidityAnnotations.ContractDefinitionAnnotation,
    function: *const SolidityAST.Node,
) ?u64 {
    for (annotation.internal_function_ids.items) |entry|
        if (entry.function == function) return entry.id;
    return null;
}

fn findAndReportCyclicSolidityContractDependencies(
    allocator: std.mem.Allocator,
    parsed_sources: []const SolidityParser.ParseResult,
    source_order: []const usize,
    reporter: *Diagnostics.ErrorReporter,
) !void {
    var reported_references = std.AutoHashMap(*const SolidityAST.Node, void).init(allocator);
    defer reported_references.deinit();

    for (source_order) |source_index| {
        const root = parsed_sources[source_index].tree.root orelse
            return error.InvalidSolidityParserState;
        for (root.payload.source_unit.nodes) |contract| {
            if (contract.nodeKind() != .contract_definition) continue;
            var processing = std.AutoHashMap(*const SolidityAST.Node, void).init(allocator);
            defer processing.deinit();
            var processed = std.AutoHashMap(*const SolidityAST.Node, void).init(allocator);
            defer processed.deinit();
            try processing.put(contract, {});
            const annotation = try solidityContractAnnotationConst(contract);
            for (annotation.contract_dependencies.items) |dependency| {
                if (!(try solidityContractDependencyCycleReachable(
                    allocator,
                    dependency.contract,
                    2,
                    &processing,
                    &processed,
                    reporter,
                ))) continue;
                if (reported_references.contains(dependency.referencing_node)) break;
                try reported_references.put(dependency.referencing_node, {});
                var secondary: Diagnostics.SecondarySourceLocation = .{};
                defer secondary.deinit(allocator);
                try secondary.append(
                    allocator,
                    "Referenced contract is here:",
                    dependency.contract.location,
                );
                try reporter.reportWithSecondary(
                    .{ .value = 7813 },
                    .TypeError,
                    dependency.referencing_node.location,
                    &secondary,
                    "Circular reference to contract bytecode either via \"new\" or \"type(...).creationCode\" / \"type(...).runtimeCode\".",
                );
                break;
            }
        }
    }
}

fn solidityContractDependencyCycleReachable(
    allocator: std.mem.Allocator,
    contract: *const SolidityAST.Node,
    depth: usize,
    processing: *std.AutoHashMap(*const SolidityAST.Node, void),
    processed: *std.AutoHashMap(*const SolidityAST.Node, void),
    reporter: *Diagnostics.ErrorReporter,
) !bool {
    if (processed.contains(contract)) return false;
    if (processing.contains(contract)) return true;
    if (depth >= 256) {
        try reporter.fatal(
            .{ .value = 7864 },
            .TypeError,
            contract.location,
            null,
            "Contract dependencies exhausting cyclic dependency validator",
        );
        unreachable;
    }
    try processing.put(contract, {});
    defer _ = processing.remove(contract);
    const annotation = try solidityContractAnnotationConst(contract);
    for (annotation.contract_dependencies.items) |dependency|
        if (try solidityContractDependencyCycleReachable(
            allocator,
            dependency.contract,
            depth + 1,
            processing,
            processed,
            reporter,
        )) return true;
    try processed.put(contract, {});
    return false;
}

fn soliditySourceOrderAlloc(
    allocator: std.mem.Allocator,
    parsed_sources: []const SolidityParser.ParseResult,
    parsed_source_index: *const ParsedSourceIndex,
) ![]usize {
    const seen = try allocator.alloc(bool, parsed_sources.len);
    defer allocator.free(seen);
    @memset(seen, false);
    var order: std.ArrayList(usize) = .empty;
    errdefer order.deinit(allocator);
    var frames: std.ArrayList(SourceDfsFrame) = .empty;
    defer frames.deinit(allocator);

    for (0..parsed_sources.len) |root_index| {
        try frames.append(allocator, .{ .index = root_index, .leave = false });
        while (frames.pop()) |frame| {
            if (frame.leave) {
                try order.append(allocator, frame.index);
                continue;
            }
            if (seen[frame.index]) continue;
            seen[frame.index] = true;
            try frames.append(allocator, .{ .index = frame.index, .leave = true });
            const source_root = parsed_sources[frame.index].tree.root orelse
                return error.InvalidSolidityParserState;
            var node_index = source_root.payload.source_unit.nodes.len;
            while (node_index != 0) {
                node_index -= 1;
                const node = source_root.payload.source_unit.nodes[node_index];
                if (node.nodeKind() != .import_directive) continue;
                const annotation = SolidityAnnotations.annotation(node) orelse
                    return error.InvalidSolidityParserState;
                const import_annotation = switch (annotation.*) {
                    .import => |*value| value,
                    else => return error.InvalidSolidityParserState,
                };
                const imported = import_annotation.source_unit orelse
                    return error.InvalidSolidityParserState;
                const imported_index = parsed_source_index.parsedIndexForRoot(imported) orelse
                    return error.InvalidSolidityParserState;
                if (!seen[imported_index])
                    try frames.append(allocator, .{
                        .index = imported_index,
                        .leave = false,
                    });
            }
        }
    }
    return order.toOwnedSlice(allocator);
}

fn soliditySourceUnitAnnotation(
    tree: *SolidityAST.Tree,
    node: *SolidityAST.Node,
) !*SolidityAnnotations.SourceUnitAnnotation {
    const annotation = try SolidityAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .source_unit => |*value| value,
        else => error.InvalidSolidityParserState,
    };
}

fn solidityImportAnnotation(
    tree: *SolidityAST.Tree,
    node: *SolidityAST.Node,
) !*SolidityAnnotations.ImportAnnotation {
    const annotation = try SolidityAnnotations.ensure(tree, node);
    return switch (annotation.*) {
        .import => |*value| value,
        else => error.InvalidSolidityParserState,
    };
}

fn solidityContractAnnotation(
    node: *SolidityAST.Node,
) !*SolidityAnnotations.ContractDefinitionAnnotation {
    const annotation = SolidityAnnotations.annotation(node) orelse
        return error.InvalidSolidityParserState;
    return switch (annotation.*) {
        .contract_definition => |*value| value,
        else => error.InvalidSolidityParserState,
    };
}

fn solidityContractAnnotationConst(
    node: *const SolidityAST.Node,
) !*const SolidityAnnotations.ContractDefinitionAnnotation {
    return solidityContractAnnotation(@constCast(node));
}

/// Compiles a validated Standard JSON root whose language is `Yul`.
/// Returned bytes are allocator-owned, compact, key-sorted, and newline
/// terminated.
pub fn compileYulStandardJsonAlloc(
    allocator: std.mem.Allocator,
    input: *const Json,
    loaded_sources: []const SourceContent,
    shared_object_optimizer: ?*ObjectOptimizer,
    shared_backend_cache: ?*BackendArtifactCache,
) ![]u8 {
    const backend_cache = shared_backend_cache;
    var output_arena = std.heap.ArenaAllocator.init(allocator);
    defer output_arena.deinit();
    const arena = output_arena.allocator();

    var output: Json = .{ .object = .empty };
    const errors = std.json.Array.init(arena);
    try output.object.put(arena, "errors", .{ .array = errors });
    const errors_value = output.object.getPtr("errors").?;

    const parsed_options = try parseSettings(
        arena,
        input,
    );
    var settings = switch (parsed_options) {
        .options => |value| value,
        .fatal => |fatal| {
            try appendError(arena, errors_value, fatal.error_type, fatal.message, fatal.message, null, null);
            return finishOutput(allocator, &output);
        },
    };
    defer settings.deinit();

    if (settings.frontend.evm_version_deprecation_warning) {
        const message = "Support for EVM versions older than constantinople is deprecated and will be removed in the future.";
        try appendError(arena, errors_value, .Warning, message, message, null, null);
    }

    const sources_value = objectMember(input, "sources") orelse {
        try appendError(arena, errors_value, .JSONError, "No input sources specified.", "No input sources specified.", null, null);
        return finishOutput(allocator, &output);
    };
    const sources = jsonObject(sources_value) orelse {
        try appendError(arena, errors_value, .JSONError, "\"sources\" is not a JSON object.", "\"sources\" is not a JSON object.", null, null);
        return finishOutput(allocator, &output);
    };
    if (sources.count() != 1) {
        try appendError(arena, errors_value, .JSONError, "Yul mode only supports exactly one input file.", "Yul mode only supports exactly one input file.", null, null);
        return finishOutput(allocator, &output);
    }
    if (settings.frontend.has_smt_responses) {
        try appendError(arena, errors_value, .JSONError, "Yul mode does not support smtlib2responses.", "Yul mode does not support smtlib2responses.", null, null);
        return finishOutput(allocator, &output);
    }
    if (settings.frontend.remappings.items.len != 0) {
        try appendError(arena, errors_value, .JSONError, "Field \"settings.remappings\" cannot be used for Yul.", "Field \"settings.remappings\" cannot be used for Yul.", null, null);
        return finishOutput(allocator, &output);
    }
    if (settings.ir.revert_strings != .Default) {
        try appendError(arena, errors_value, .JSONError, "Field \"settings.debug.revertStrings\" cannot be used for Yul.", "Field \"settings.debug.revertStrings\" cannot be used for Yul.", null, null);
        return finishOutput(allocator, &output);
    }
    if (settings.ir.via_ssa_cfg) {
        const message = "Zig port: experimental Yul SSA-CFG code generation is not implemented.";
        try appendError(arena, errors_value, .UnimplementedFeatureError, message, message, null, null);
        return finishOutput(allocator, &output);
    }
    if (settings.ir.debug_info.ethdebug or hasAnyEthdebugRequest(&settings.projection.output_selection)) {
        const message = "Zig port: ethdebug output is not implemented.";
        try appendError(arena, errors_value, .UnimplementedFeatureError, message, message, null, null);
        return finishOutput(allocator, &output);
    }
    if (hasExactArtifactRequest(&settings.projection.output_selection, "yulCFGJson")) {
        const message = "Zig port: experimental Yul CFG JSON output is not implemented.";
        try appendError(arena, errors_value, .UnimplementedFeatureError, message, message, null, null);
        return finishOutput(allocator, &output);
    }

    const source_name = sources.keys()[0];
    const source_entry = &sources.values()[0];
    const source_contents = resolveSource(source_name, source_entry, loaded_sources) orelse {
        try appendError(arena, errors_value, .IOError, "Source callback failed.", "Source callback failed.", null, null);
        return finishOutput(allocator, &output);
    };

    if (objectMember(source_entry, "keccak256")) |hash_value| {
        if (jsonString(hash_value)) |hash| {
            if (!hashMatchesContent(hash, source_contents)) {
                const message = try std.fmt.allocPrint(
                    arena,
                    "Mismatch between content and supplied hash for \"{s}\"",
                    .{source_name},
                );
                try appendError(arena, errors_value, .IOError, message, message, null, null);
                return finishOutput(allocator, &output);
            }
        }
    }

    var stack = try YulStack.init(
        allocator,
        settings.frontend.evm_version,
        settings.optimizer.settings,
        settings.ir.debug_info,
        null,
        shared_object_optimizer,
    );
    defer stack.deinit();

    const successful = try stack.parseAndAnalyze(source_name, source_contents);
    if (!successful and !stack.hasErrors()) return error.InvalidYulStackState;

    var ast_owner: ?@import("../../libyul/asm_json_converter.zig").OwnedYulJson = null;
    defer if (ast_owner) |*owner| owner.deinit();
    var assembly_pair: YulStackModule.MachineAssemblyPair = .{};
    defer assembly_pair.deinit();

    var contract_name: []const u8 = "";
    if (successful) {
        const parser_result = try stack.parserResult();
        contract_name = try arena.dupe(u8, parser_result.name);

        if (isArtifactRequested(&settings.projection.output_selection, source_name, contract_name, "ir", true)) {
            const contract = try ensureContract(arena, &output, source_name, contract_name);
            try contract.object.put(arena, "ir", .{ .string = try stack.printAlloc(arena) });
        }

        if (isArtifactRequested(&settings.projection.output_selection, source_name, contract_name, "ast", true)) {
            ast_owner = try stack.astJson();
            var source_result: Json = .{ .object = .empty };
            try source_result.object.put(arena, "id", .{ .integer = 0 });
            try source_result.object.put(arena, "ast", ast_owner.?.value);
            const output_sources = try ensureObject(arena, &output, "sources");
            try output_sources.object.put(arena, source_name, source_result);
        }

        stack.optimize() catch |err| {
            if (err == error.OutOfMemory) return error.OutOfMemory;
            const message = try std.fmt.allocPrint(arena, "Yul optimizer failed: {s}", .{@errorName(err)});
            try appendError(arena, errors_value, .YulException, message, message, null, null);
            return finishOutput(allocator, &output);
        };
        const assembly_source_indices = try stack.assemblySourceIndicesAlloc(allocator);
        defer allocator.free(assembly_source_indices);
        assembly_pair = assembleAndLinkBackend(
            allocator,
            &stack,
            null,
            false,
            assembly_source_indices,
            settings.link.libraries.items,
            backend_cache,
        ) catch |err| {
            if (err == error.OutOfMemory) return error.OutOfMemory;
            const message = try std.fmt.allocPrint(arena, "Yul code generation failed: {s}", .{@errorName(err)});
            try appendError(arena, errors_value, .YulException, message, message, null, null);
            return finishOutput(allocator, &output);
        };
    }

    for (stack.errors()) |*diagnostic| {
        try appendDiagnostic(
            arena,
            output.object.getPtr("errors").?,
            &stack,
            source_name,
            diagnostic,
        );
    }
    if (stack.hasErrors()) return finishOutput(allocator, &output);

    try appendMachineObject(
        arena,
        &output,
        &settings.projection.output_selection,
        source_name,
        contract_name,
        "bytecode",
        false,
        &assembly_pair.creation,
        settings.frontend.evm_version,
        false,
    );
    try appendMachineObject(
        arena,
        &output,
        &settings.projection.output_selection,
        source_name,
        contract_name,
        "deployedBytecode",
        true,
        &assembly_pair.deployed,
        settings.frontend.evm_version,
        false,
    );

    if (isArtifactRequested(&settings.projection.output_selection, source_name, contract_name, "irOptimized", true)) {
        const contract = try ensureContract(arena, &output, source_name, contract_name);
        try contract.object.put(arena, "irOptimized", .{ .string = try stack.printAlloc(arena) });
    }
    if (isArtifactRequested(&settings.projection.output_selection, source_name, contract_name, "evm.assembly", true)) {
        const assembly = assembly_pair.creation.assembly() orelse return error.MissingAssembly;
        const contract = try ensureContract(arena, &output, source_name, contract_name);
        const evm = try ensureObject(arena, contract, "evm");
        try evm.object.put(arena, "assembly", .{ .string = try assembly.assemblyStringAllocWithScratch(
            arena,
            allocator,
            stack.debugInfoSelection(),
            &.{},
        ) });
    }

    return finishOutput(allocator, &output);
}

fn parseSettings(
    allocator: std.mem.Allocator,
    input: *const Json,
) !CompilationOptionsResult {
    var result = CompilationOptions.init(allocator);
    var result_transferred = false;
    defer if (!result_transferred) result.deinit();

    if (objectMember(input, "auxiliaryInput")) |auxiliary| {
        if (try checkKeys(allocator, auxiliary, &.{"smtlib2responses"}, "auxiliaryInput")) |fatal|
            return .{ .fatal = fatal };
        if (objectMember(auxiliary, "smtlib2responses")) |responses|
            result.frontend.has_smt_responses = !jsonEmpty(responses);
    }

    const settings_value = objectMember(input, "settings") orelse {
        result_transferred = true;
        return .{ .options = result };
    };
    if (jsonEmpty(settings_value)) {
        result_transferred = true;
        return .{ .options = result };
    }
    if (try checkKeys(
        allocator,
        settings_value,
        &.{ "debug", "evmVersion", "experimental", "libraries", "metadata", "modelChecker", "optimizer", "outputSelection", "remappings", "stopAfter", "viaIR", "viaSSACFG" },
        "settings",
    )) |fatal| return .{ .fatal = fatal };

    if (objectMember(settings_value, "experimental")) |value| {
        result.frontend.experimental = jsonBool(value) orelse
            return .{ .fatal = .{ .message = "'settings.experimental' must be a Boolean." } };
    }
    if (objectMember(settings_value, "stopAfter")) |value| {
        const stop_after = jsonString(value) orelse
            return .{ .fatal = .{ .message = "\"settings.stopAfter\" must be a string." } };
        if (!std.mem.eql(u8, stop_after, "parsing"))
            return .{ .fatal = .{ .message = "Invalid value for \"settings.stopAfter\". Only valid value is \"parsing\"." } };
        result.frontend.stop_after_parsing = true;
    }
    if (objectMember(settings_value, "viaIR")) |value| {
        result.ir.via_ir = jsonBool(value) orelse
            return .{ .fatal = .{ .message = "\"settings.viaIR\" must be a Boolean." } };
        result.ir.via_ir_explicit = true;
    }
    if (objectMember(settings_value, "viaSSACFG")) |value| {
        result.ir.via_ssa_cfg = jsonBool(value) orelse
            return .{ .fatal = .{ .message = "\"settings.viaSSACFG\" must be a Boolean." } };
        if (result.ir.via_ssa_cfg and result.ir.via_ir_explicit and !result.ir.via_ir)
            return .{ .fatal = .{ .message = "\"settings.viaSSACFG\" requires compilation via IR." } };
        if (result.ir.via_ssa_cfg) result.ir.via_ir = true;
    }
    if (objectMember(settings_value, "evmVersion")) |value| {
        const version_name = jsonString(value) orelse
            return .{ .fatal = .{ .message = "evmVersion must be a string." } };
        result.frontend.evm_version = EVMVersion.fromString(version_name) orelse
            return .{ .fatal = .{ .message = "Invalid EVM version requested." } };
        result.frontend.evm_version_deprecation_warning = result.frontend.evm_version.before(
            EVMVersion.init(.Constantinople),
        );
        if (result.frontend.evm_version.isExperimental() and !result.frontend.experimental) {
            const message = try std.fmt.allocPrint(
                allocator,
                "EVM version '{s}' is experimental and can only be used with the 'settings.experimental' option enabled.",
                .{result.frontend.evm_version.name()},
            );
            return .{ .fatal = .{ .message = message } };
        }
    }
    if (objectMember(settings_value, "debug")) |debug| {
        if (try checkKeys(allocator, debug, &.{ "revertStrings", "debugInfo" }, "settings.debug")) |fatal|
            return .{ .fatal = fatal };
        if (objectMember(debug, "revertStrings")) |value| {
            const revert_strings = jsonString(value) orelse
                return .{ .fatal = .{ .message = "settings.debug.revertStrings must be a string." } };
            if (!isOneOf(revert_strings, &.{ "default", "strip", "debug", "verboseDebug" }))
                return .{ .fatal = .{ .message = "Invalid value for settings.debug.revertStrings." } };
            if (std.mem.eql(u8, revert_strings, "verboseDebug"))
                return .{ .fatal = .{ .error_type = .UnimplementedFeatureError, .message = "Only \"default\", \"strip\" and \"debug\" are implemented for settings.debug.revertStrings for now." } };
            result.ir.revert_strings = DebugSettings.RevertStrings.fromString(revert_strings) orelse
                return .{ .fatal = .{ .message = "Invalid value for settings.debug.revertStrings." } };
        }
        if (objectMember(debug, "debugInfo")) |value| {
            const components = jsonArray(value) orelse
                return .{ .fatal = .{ .message = "settings.debug.debugInfo must be an array." } };
            var selection = DebugInfoSelection.noneValue();
            for (components.items) |*component_value| {
                const component = jsonString(component_value) orelse
                    return .{ .fatal = .{ .message = "Invalid value in settings.debug.debugInfo." } };
                if (std.mem.eql(u8, component, "*")) {
                    selection = DebugInfoSelection.allExceptExperimental();
                } else if (!selection.enable(component)) {
                    return .{ .fatal = .{ .message = "Invalid value in settings.debug.debugInfo." } };
                }
            }
            if (selection.snippet and !selection.location)
                return .{ .fatal = .{ .message = "To use 'snippet' with settings.debug.debugInfo you must select also 'location'." } };
            result.ir.debug_info = selection;
        }
    }

    if (objectMember(settings_value, "remappings")) |value| {
        const remappings = jsonArray(value) orelse
            return .{ .fatal = .{ .message = "\"settings.remappings\" must be an array of strings." } };
        for (remappings.items) |*remapping_value| {
            const text = jsonString(remapping_value) orelse
                return .{ .fatal = .{ .message = "\"settings.remappings\" must be an array of strings" } };
            const remapping = SolidityImportRemapper.parseRemapping(text) orelse {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "Invalid remapping: \"{s}\"",
                    .{text},
                );
                return .{ .fatal = .{ .message = message } };
            };
            try result.addRemapping(remapping);
        }
    }

    if (objectMember(settings_value, "optimizer")) |optimizer| {
        const optimizer_result = try parseOptimizer(allocator, optimizer);
        switch (optimizer_result) {
            .settings => |value| try result.setOptimizer(value),
            .fatal => |fatal| return .{ .fatal = fatal },
        }
    }

    if (objectMember(settings_value, "libraries")) |libraries| {
        const libraries_object = jsonObject(libraries) orelse
            return .{ .fatal = .{ .message = "\"libraries\" is not a JSON object." } };
        for (libraries_object.keys(), libraries_object.values()) |source_name, *source_value| {
            const source_object = jsonObject(source_value) orelse
                return .{ .fatal = .{ .message = "Library entry is not a JSON object." } };
            for (source_object.keys(), source_object.values()) |library_name, *address_value| {
                const address_text = jsonString(address_value) orelse
                    return .{ .fatal = .{ .message = "Library address must be a string." } };
                if (!std.mem.startsWith(u8, address_text, "0x"))
                    return .{ .fatal = .{ .message = "Library address is not prefixed with \"0x\"." } };
                if (address_text.len != 42)
                    return .{ .fatal = .{ .message = "Library address is of invalid length." } };
                const address = FixedHash.H160.fromString(
                    address_text,
                    .from_hex,
                    .fail_if_different,
                ) catch {
                    const message = try std.fmt.allocPrint(
                        allocator,
                        "Invalid library address (\"{s}\") supplied.",
                        .{address_text},
                    );
                    return .{ .fatal = .{ .message = message } };
                };
                const qualified_name = try std.fmt.allocPrint(
                    allocator,
                    "{s}:{s}",
                    .{ source_name, library_name },
                );
                defer allocator.free(qualified_name);
                try result.addLibrary(.{
                    .name = qualified_name,
                    .address = address,
                });
            }
        }
    }

    if (objectMember(settings_value, "metadata")) |metadata| {
        if (try validateMetadata(allocator, metadata)) |fatal| return .{ .fatal = fatal };
        if (objectMember(metadata, "appendCBOR")) |value|
            result.metadata.append_cbor = jsonBool(value).?;
        if (objectMember(metadata, "useLiteralContent")) |value|
            result.metadata.literal_sources = jsonBool(value).?;
        if (objectMember(metadata, "bytecodeHash")) |value| {
            const hash = jsonString(value).?;
            result.metadata.hash = if (std.mem.eql(u8, hash, "ipfs"))
                .ipfs
            else if (std.mem.eql(u8, hash, "bzzr1"))
                .bzzr1
            else
                .none;
        }
    }
    if (objectMember(settings_value, "modelChecker")) |model_checker| {
        if (try checkKeys(
            allocator,
            model_checker,
            &.{ "bmcLoopIterations", "contracts", "divModNoSlacks", "engine", "extCalls", "invariants", "printQuery", "showProvedSafe", "showUnproved", "showUnsupported", "solvers", "targets", "timeout" },
            "modelChecker",
        )) |fatal| return .{ .fatal = fatal };
    }
    if (objectMember(settings_value, "outputSelection")) |selection| {
        if (try validateOutputSelection(allocator, selection)) |fatal| return .{ .fatal = fatal };
        result.projection.output_selection.was_specified = true;
        if (jsonObject(selection)) |source_selections| {
            for (source_selections.keys(), source_selections.values()) |source_name, *source_value| {
                const contract_selections = jsonObject(source_value) orelse continue;
                for (contract_selections.keys(), contract_selections.values()) |contract_name, *contract_value| {
                    const artifacts = jsonArray(contract_value) orelse continue;
                    for (artifacts.items) |*artifact_value|
                        try result.addOutput(
                            source_name,
                            contract_name,
                            jsonString(artifact_value).?,
                        );
                }
            }
        } else {
            // Preserve the legacy parser's distinction between an absent
            // selection and a present-but-empty non-object value.
            result.projection.output_selection.only_frontend_artifacts = false;
        }
    }
    if (result.frontend.stop_after_parsing and
        isBinaryRequested(&result.projection.output_selection))
        return .{ .fatal = .{ .message = "Requested output selection conflicts with \"settings.stopAfter\"." } };

    if (!result.frontend.experimental) {
        if (hasAnyEthdebugRequest(&result.projection.output_selection) or
            hasExactArtifactRequest(&result.projection.output_selection, "irAst") or
            hasExactArtifactRequest(&result.projection.output_selection, "irOptimizedAst") or
            hasExactArtifactRequest(&result.projection.output_selection, "yulCFGJson"))
        {
            return .{ .fatal = .{ .error_type = .FatalError, .message = "'irAst', 'irOptimizedAst', 'yulCFGJson', and 'ethdebug' outputs are experimental and can only be used with the 'settings.experimental' option enabled." } };
        }
        if (result.ir.via_ssa_cfg)
            return .{ .fatal = .{ .error_type = .FatalError, .message = "'viaSSACFG' setting is experimental and can only be used with the 'settings.experimental' option enabled." } };
        if (result.ir.debug_info.ethdebug)
            return .{ .fatal = .{ .error_type = .FatalError, .message = "Ethdebug annotations are experimental and can only be included in 'settings.debug.debugInfo' by enabling the 'settings.experimental' option." } };
    }

    result_transferred = true;
    return .{ .options = result };
}

const OptimizerResult = union(enum) {
    settings: OptimiserSettings,
    fatal: Fatal,
};

fn parseOptimizer(allocator: std.mem.Allocator, input: *const Json) !OptimizerResult {
    if (try checkKeys(allocator, input, &.{ "details", "enabled", "runs" }, "settings.optimizer")) |fatal|
        return .{ .fatal = fatal };
    var settings = OptimiserSettings.minimal();
    if (objectMember(input, "enabled")) |enabled_value| {
        const enabled = jsonBool(enabled_value) orelse
            return .{ .fatal = .{ .message = "The \"enabled\" setting must be a Boolean." } };
        if (enabled) settings = OptimiserSettings.standard();
    }
    if (objectMember(input, "runs")) |runs_value| {
        settings.expected_executions_per_deployment = JSON.get(u64, runs_value) catch
            return .{ .fatal = .{ .message = "The \"runs\" setting must be an unsigned number." } };
    }
    const details = objectMember(input, "details") orelse return .{ .settings = settings };
    if (try checkKeys(
        allocator,
        details,
        &.{ "peephole", "inliner", "jumpdestRemover", "orderLiterals", "deduplicate", "cse", "constantOptimizer", "yul", "yulDetails", "simpleCounterForLoopUncheckedIncrement" },
        "settings.optimizer.details",
    )) |fatal| return .{ .fatal = fatal };

    const Detail = struct { name: []const u8, field: *bool };
    var detail_fields = [_]Detail{
        .{ .name = "peephole", .field = &settings.run_peephole },
        .{ .name = "inliner", .field = &settings.run_inliner },
        .{ .name = "jumpdestRemover", .field = &settings.run_jumpdest_remover },
        .{ .name = "orderLiterals", .field = &settings.run_order_literals },
        .{ .name = "deduplicate", .field = &settings.run_deduplicate },
        .{ .name = "cse", .field = &settings.run_cse },
        .{ .name = "constantOptimizer", .field = &settings.run_constant_optimiser },
        .{ .name = "yul", .field = &settings.run_yul_optimiser },
        .{ .name = "simpleCounterForLoopUncheckedIncrement", .field = &settings.simple_counter_for_loop_unchecked_increment },
    };
    for (&detail_fields) |detail| if (objectMember(details, detail.name)) |value| {
        detail.field.* = jsonBool(value) orelse {
            const message = try std.fmt.allocPrint(
                allocator,
                "\"settings.optimizer.details.{s}\" must be Boolean",
                .{detail.name},
            );
            return .{ .fatal = .{ .message = message } };
        };
    };
    settings.optimize_stack_allocation = settings.run_yul_optimiser;

    if (objectMember(details, "yulDetails")) |yul_details| {
        const allowed: []const []const u8 = if (settings.run_yul_optimiser)
            &.{ "stackAllocation", "optimizerSteps" }
        else
            &.{"optimizerSteps"};
        if (try checkKeys(allocator, yul_details, allowed, "settings.optimizer.details.yulDetails")) |fatal| {
            if (!settings.run_yul_optimiser)
                return .{ .fatal = .{ .message = "Only optimizerSteps can be set in yulDetails when Yul optimizer is disabled." } };
            return .{ .fatal = fatal };
        }
        if (settings.run_yul_optimiser) {
            if (objectMember(yul_details, "stackAllocation")) |value| {
                settings.optimize_stack_allocation = jsonBool(value) orelse
                    return .{ .fatal = .{ .message = "\"settings.optimizer.details.yulDetails.stackAllocation\" must be Boolean" } };
            }
        }
        if (objectMember(yul_details, "optimizerSteps")) |value| {
            const sequence = jsonString(value) orelse
                return .{ .fatal = .{ .message = "\"settings.optimizer.details.yulDetails.optimizerSteps\" must be a string" } };
            if (!settings.run_yul_optimiser and !OptimiserSuite.isEmptyOptimizerSequence(sequence))
                return .{ .fatal = .{ .message = "If Yul optimizer is disabled, only an empty optimizerSteps sequence is accepted. Note that the empty optimizer sequence is properly denoted by \":\"." } };
            OptimiserSuite.validateSequence(sequence) catch |err| {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "Invalid optimizer step sequence in \"settings.optimizer.details.yulDetails.optimizerSteps\": {s}",
                    .{@errorName(err)},
                );
                return .{ .fatal = .{ .message = message } };
            };
            if (std.mem.findScalar(u8, sequence, ':')) |delimiter| {
                settings.yul_optimiser_steps = sequence[0..delimiter];
                settings.yul_optimiser_cleanup_steps = sequence[delimiter + 1 ..];
            } else {
                settings.yul_optimiser_steps = sequence;
            }
        }
    }
    return .{ .settings = settings };
}

fn validateMetadata(allocator: std.mem.Allocator, input: *const Json) !?Fatal {
    if (try checkKeys(allocator, input, &.{ "appendCBOR", "useLiteralContent", "bytecodeHash" }, "settings.metadata")) |fatal|
        return fatal;
    if (objectMember(input, "appendCBOR")) |value| if (jsonBool(value) == null)
        return .{ .message = "\"settings.metadata.appendCBOR\" must be Boolean" };
    if (objectMember(input, "useLiteralContent")) |value| if (jsonBool(value) == null)
        return .{ .message = "\"settings.metadata.useLiteralContent\" must be Boolean" };
    if (objectMember(input, "bytecodeHash")) |value| {
        const hash = jsonString(value) orelse
            return .{ .message = "\"settings.metadata.bytecodeHash\" must be \"ipfs\", \"bzzr1\" or \"none\"" };
        if (!isOneOf(hash, &.{ "ipfs", "bzzr1", "none" }))
            return .{ .message = "\"settings.metadata.bytecodeHash\" must be \"ipfs\", \"bzzr1\" or \"none\"" };
    }
    return null;
}

fn validateOutputSelection(allocator: std.mem.Allocator, input: *const Json) !?Fatal {
    const selection = jsonObject(input) orelse {
        if (jsonEmpty(input)) return null;
        return .{ .message = "\"settings.outputSelection\" must be an object" };
    };
    for (selection.keys(), selection.values()) |source_name, *source_value| {
        const source = jsonObject(source_value) orelse {
            const message = try std.fmt.allocPrint(
                allocator,
                "\"settings.outputSelection.{s}\" must be an object",
                .{source_name},
            );
            return .{ .message = message };
        };
        for (source.keys(), source.values()) |contract_name, *contract_value| {
            const artifacts = jsonArray(contract_value) orelse {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "\"settings.outputSelection.{s}.{s}\" must be a string array",
                    .{ source_name, contract_name },
                );
                return .{ .message = message };
            };
            for (artifacts.items) |*artifact| if (jsonString(artifact) == null) {
                const message = try std.fmt.allocPrint(
                    allocator,
                    "\"settings.outputSelection.{s}.{s}\" must be a string array",
                    .{ source_name, contract_name },
                );
                return .{ .message = message };
            };
        }
    }
    return null;
}

pub fn isArtifactRequested(
    output_selection: *const OutputSelection,
    file: []const u8,
    contract: []const u8,
    artifact: []const u8,
    wildcard_matches_experimental: bool,
) bool {
    return output_selection.requests(
        file,
        contract,
        artifact,
        wildcard_matches_experimental,
    );
}

fn appendMachineObject(
    allocator: std.mem.Allocator,
    output: *Json,
    output_selection: *const OutputSelection,
    source_name: []const u8,
    contract_name: []const u8,
    kind: []const u8,
    deployed: bool,
    machine_object: *const YulStackModule.MachineAssemblyObject,
    evm_version: EVMVersion,
    include_generated_sources: bool,
) !void {
    const prefix = try std.fmt.allocPrint(allocator, "evm.{s}", .{kind});
    const component_names = [_][]const u8{
        "",                 "object",         "opcodes",  "sourceMap",           "functionDebugData",
        "generatedSources", "linkReferences", "ethdebug", "immutableReferences",
    };
    var any_component = false;
    for (component_names) |component| {
        if ((!std.mem.eql(u8, component, "generatedSources") or
            include_generated_sources) and
            (deployed or !std.mem.eql(u8, component, "immutableReferences")))
        {
            const artifact = if (component.len == 0)
                prefix
            else
                try std.fmt.allocPrint(allocator, "{s}.{s}", .{ prefix, component });
            if (isArtifactRequested(output_selection, source_name, contract_name, artifact, true)) {
                any_component = true;
                break;
            }
        }
    }
    if (!any_component) return;
    const bytecode = if (machine_object.bytecode) |*value| value else return;

    var bytecode_json: Json = .{ .object = .empty };
    if (requestedElement(output_selection, source_name, contract_name, prefix, "object")) {
        const value = try bytecode.toHexAlloc(allocator);
        try bytecode_json.object.put(allocator, "object", .{ .string = value });
    }
    if (requestedElement(output_selection, source_name, contract_name, prefix, "opcodes")) {
        const value = try Disassemble.disassembleAlloc(allocator, bytecode.bytecode.items, evm_version, " ");
        try bytecode_json.object.put(allocator, "opcodes", .{ .string = value });
    }
    if (requestedElement(output_selection, source_name, contract_name, prefix, "sourceMap")) {
        try bytecode_json.object.put(
            allocator,
            "sourceMap",
            try ownedString(allocator, machine_object.source_mappings orelse ""),
        );
    }
    if (requestedElement(output_selection, source_name, contract_name, prefix, "functionDebugData")) {
        try bytecode_json.object.put(
            allocator,
            "functionDebugData",
            try formatFunctionDebugData(allocator, bytecode),
        );
    }
    if (include_generated_sources and
        requestedElement(output_selection, source_name, contract_name, prefix, "generatedSources"))
        try bytecode_json.object.put(
            allocator,
            "generatedSources",
            .{ .array = std.json.Array.init(allocator) },
        );
    if (requestedElement(output_selection, source_name, contract_name, prefix, "linkReferences")) {
        try bytecode_json.object.put(
            allocator,
            "linkReferences",
            try formatLinkReferences(allocator, bytecode),
        );
    }
    if (deployed and requestedElement(output_selection, source_name, contract_name, prefix, "immutableReferences")) {
        try bytecode_json.object.put(
            allocator,
            "immutableReferences",
            try formatImmutableReferences(allocator, bytecode),
        );
    }
    const contract = try ensureContract(allocator, output, source_name, contract_name);
    const evm = try ensureObject(allocator, contract, "evm");
    try evm.object.put(allocator, kind, bytecode_json);
}

fn appendEmptyMachineObject(
    allocator: std.mem.Allocator,
    contract: *Json,
    output_selection: *const OutputSelection,
    source_name: []const u8,
    contract_name: []const u8,
    kind: []const u8,
    deployed: bool,
) !void {
    const prefix = try std.fmt.allocPrint(allocator, "evm.{s}", .{kind});
    defer allocator.free(prefix);
    if (!requestsMachineObject(
        output_selection,
        source_name,
        contract_name,
        kind,
        deployed,
    )) return;

    var bytecode_json: Json = .{ .object = .empty };
    if (requestedElement(output_selection, source_name, contract_name, prefix, "object"))
        try bytecode_json.object.put(allocator, "object", try ownedString(allocator, ""));
    if (requestedElement(output_selection, source_name, contract_name, prefix, "opcodes"))
        try bytecode_json.object.put(allocator, "opcodes", try ownedString(allocator, ""));
    if (requestedElement(output_selection, source_name, contract_name, prefix, "sourceMap"))
        try bytecode_json.object.put(allocator, "sourceMap", try ownedString(allocator, ""));
    if (requestedElement(output_selection, source_name, contract_name, prefix, "functionDebugData"))
        try bytecode_json.object.put(allocator, "functionDebugData", .{ .object = .empty });
    if (requestedElement(output_selection, source_name, contract_name, prefix, "generatedSources"))
        try bytecode_json.object.put(
            allocator,
            "generatedSources",
            .{ .array = std.json.Array.init(allocator) },
        );
    if (requestedElement(output_selection, source_name, contract_name, prefix, "linkReferences"))
        try bytecode_json.object.put(allocator, "linkReferences", .{ .object = .empty });
    if (deployed and requestedElement(
        output_selection,
        source_name,
        contract_name,
        prefix,
        "immutableReferences",
    ))
        try bytecode_json.object.put(allocator, "immutableReferences", .{ .object = .empty });

    const evm = try ensureObject(allocator, contract, "evm");
    try evm.object.put(allocator, kind, bytecode_json);
}

fn requestsMachineObject(
    output_selection: *const OutputSelection,
    source_name: []const u8,
    contract_name: []const u8,
    kind: []const u8,
    deployed: bool,
) bool {
    var prefix_buffer: [64]u8 = undefined;
    const prefix = std.fmt.bufPrint(&prefix_buffer, "evm.{s}", .{kind}) catch
        return false;
    if (isArtifactRequested(
        output_selection,
        source_name,
        contract_name,
        prefix,
        true,
    )) return true;
    const components = [_][]const u8{
        "object",
        "opcodes",
        "sourceMap",
        "functionDebugData",
        "generatedSources",
        "linkReferences",
        "ethdebug",
        "immutableReferences",
    };
    for (components) |component| {
        if (!deployed and std.mem.eql(u8, component, "immutableReferences")) continue;
        var artifact_buffer: [96]u8 = undefined;
        const artifact = std.fmt.bufPrint(
            &artifact_buffer,
            "{s}.{s}",
            .{ prefix, component },
        ) catch continue;
        if (isArtifactRequested(
            output_selection,
            source_name,
            contract_name,
            artifact,
            true,
        )) return true;
    }
    return false;
}

fn requestedElement(
    output_selection: *const OutputSelection,
    source_name: []const u8,
    contract_name: []const u8,
    prefix: []const u8,
    element: []const u8,
) bool {
    var buffer: [128]u8 = undefined;
    const artifact = std.fmt.bufPrint(&buffer, "{s}.{s}", .{ prefix, element }) catch return false;
    return isArtifactRequested(output_selection, source_name, contract_name, artifact, true);
}

fn formatFunctionDebugData(allocator: std.mem.Allocator, bytecode: *const LinkerObject) !Json {
    var result: Json = .{ .object = .empty };
    for (bytecode.function_debug_data.items) |entry| {
        var function: Json = .{ .object = .empty };
        try function.object.put(allocator, "id", optionalInteger(entry.data.source_id));
        try function.object.put(allocator, "entryPoint", optionalInteger(entry.data.bytecode_offset));
        try function.object.put(allocator, "parameterSlots", usizeInteger(entry.data.params));
        try function.object.put(allocator, "returnSlots", usizeInteger(entry.data.returns));
        // Machine artifacts are released before the complete Standard JSON
        // tree is serialized, so cached function names cannot be borrowed as
        // object keys.
        try result.object.put(
            allocator,
            try allocator.dupe(u8, entry.name),
            function,
        );
    }
    return result;
}

fn formatLinkReferences(allocator: std.mem.Allocator, bytecode: *const LinkerObject) !Json {
    var result: Json = .{ .object = .empty };
    for (bytecode.link_references.items) |reference| {
        const colon = std.mem.findScalarLast(u8, reference.library_name, ':');
        const file = if (colon) |index| reference.library_name[0..index] else "";
        const name = if (colon) |index| reference.library_name[index + 1 ..] else reference.library_name;
        const file_key = if (result.object.contains(file))
            file
        else
            try allocator.dupe(u8, file);
        const file_object = try ensureObject(allocator, &result, file_key);
        var array_value = file_object.object.getPtr(name);
        if (array_value == null) {
            const name_key = try allocator.dupe(u8, name);
            try file_object.object.put(allocator, name_key, .{ .array = std.json.Array.init(allocator) });
            array_value = file_object.object.getPtr(name_key);
        }
        var entry: Json = .{ .object = .empty };
        try entry.object.put(allocator, "start", usizeInteger(reference.offset));
        try entry.object.put(allocator, "length", .{ .integer = 20 });
        try array_value.?.array.append(entry);
    }
    return result;
}

fn formatImmutableReferences(allocator: std.mem.Allocator, bytecode: *const LinkerObject) !Json {
    var result: Json = .{ .object = .empty };
    for (bytecode.immutable_references.items) |reference| {
        var ranges = std.json.Array.init(allocator);
        for (reference.references.offsets.items) |offset| {
            var range: Json = .{ .object = .empty };
            try range.object.put(allocator, "start", usizeInteger(offset));
            try range.object.put(allocator, "length", .{ .integer = 32 });
            try ranges.append(range);
        }
        // The linker object is torn down before the Standard JSON tree is
        // serialized, so its identifier cannot be borrowed as an object key.
        try result.object.put(
            allocator,
            try allocator.dupe(u8, reference.references.identifier),
            .{ .array = ranges },
        );
    }
    return result;
}

const SoliditySourceProvider = struct {
    streams: []const CharStream,
    source_index: union(enum) {
        parsed: *const ParsedSourceIndex,
        /// Early parsing failures have no completed graph or parsed index.
        /// Streams use the existing registry's dense IDs in that case.
        registry: *const SourceRegistry,
    },

    fn provider(self: *const SoliditySourceProvider) StreamProvider.CharStreamProvider {
        return .{ .context = self, .get_fn = get };
    }

    fn get(
        opaque_context: *const anyopaque,
        source_name: []const u8,
    ) StreamProvider.ProviderError!*const CharStream {
        const self: *const SoliditySourceProvider = @ptrCast(@alignCast(opaque_context));
        const index = switch (self.source_index) {
            .parsed => |parsed| parsed.parsedIndexForName(source_name) orelse return error.SourceNameMismatch,
            .registry => |registry| (registry.idForName(source_name) orelse return error.SourceNameMismatch).index(),
        };
        if (index >= self.streams.len) return error.SourceNameMismatch;
        return &self.streams[index];
    }
};

/// A diagnostic-limit abort is ordinary compiler output. Serialize while the
/// pending registry owns source bytes; commitCompleted then aborts this
/// graph-incomplete revision, leaving prior semantic/cache state intact.
fn finishParsingDiagnostics(allocator: std.mem.Allocator, arena: std.mem.Allocator, output: *Json, reporter: *const Diagnostics.ErrorReporter, registry: *const SourceRegistry) ![]u8 {
    const streams = try arena.alloc(CharStream, registry.knownCount());
    for (registry.parseOrder()) |id| {
        const source = registry.record(id) orelse return error.InvalidSolidityParserState;
        streams[id.index()] = CharStream.initBorrowed(source.content, source.name);
    }
    const provider: SoliditySourceProvider = .{ .streams = streams, .source_index = .{ .registry = registry } };
    for (reporter.diagnostics()) |*diagnostic|
        try appendDiagnosticWithProvider(arena, output.object.getPtr("errors").?, provider.provider(), diagnostic, true);
    try output.object.put(arena, "sources", .{ .object = .empty });
    return finishOutput(allocator, output);
}

fn sortParsedSourcesByRegistry(
    allocator: std.mem.Allocator,
    registry: *const SourceRegistry,
    parsed_sources: *std.ArrayList(SolidityParser.ParseResult),
) !void {
    const parse_order = registry.parseOrder();
    if (parse_order.len != parsed_sources.items.len)
        return error.InvalidSolidityParserState;

    const sorted_ids = try registry.sortedActiveIdsAlloc(allocator);
    defer allocator.free(sorted_ids);
    if (sorted_ids.len != parsed_sources.items.len)
        return error.InvalidSolidityParserState;

    var parse_indices_by_id: std.AutoHashMapUnmanaged(SourceId, usize) = .empty;
    defer parse_indices_by_id.deinit(allocator);
    try parse_indices_by_id.ensureTotalCapacity(
        allocator,
        std.math.cast(u32, parse_order.len) orelse return error.TooManySources,
    );
    for (parse_order, 0..) |source_id, parse_index| {
        if (parse_indices_by_id.contains(source_id))
            return error.InvalidSolidityParserState;
        parse_indices_by_id.putAssumeCapacityNoClobber(source_id, parse_index);
    }

    const sorted = try allocator.alloc(SolidityParser.ParseResult, sorted_ids.len);
    errdefer allocator.free(sorted);
    for (sorted_ids, sorted) |source_id, *target| {
        const parse_index = parse_indices_by_id.get(source_id) orelse
            return error.InvalidSolidityParserState;
        if (parse_index >= parsed_sources.items.len)
            return error.InvalidSolidityParserState;
        target.* = parsed_sources.items[parse_index];
    }

    parsed_sources.deinit(allocator);
    parsed_sources.* = .fromOwnedSlice(sorted);
}

fn sortedObjectIndices(
    allocator: std.mem.Allocator,
    object: *const std.json.ObjectMap,
) std.mem.Allocator.Error![]usize {
    const indices = try allocator.alloc(usize, object.count());
    for (indices, 0..) |*slot, index| slot.* = index;
    const keys = object.keys();
    std.mem.sort(usize, indices, keys, struct {
        fn lessThan(names: []const []const u8, left: usize, right: usize) bool {
            return std.mem.order(u8, names[left], names[right]) == .lt;
        }
    }.lessThan);
    return indices;
}

fn appendDiagnostic(
    allocator: std.mem.Allocator,
    errors_value: *Json,
    stack: *const YulStack,
    source_name: []const u8,
    diagnostic: *const Diagnostics.Diagnostic,
) !void {
    const stream = try stack.charStream(source_name);
    var singleton = StreamProvider.SingletonCharStreamProvider.init(stream);
    try appendDiagnosticWithProvider(
        allocator,
        errors_value,
        singleton.provider(),
        diagnostic,
        false,
    );
}

fn appendDiagnosticWithProvider(
    allocator: std.mem.Allocator,
    errors_value: *Json,
    provider: StreamProvider.CharStreamProvider,
    diagnostic: *const Diagnostics.Diagnostic,
    include_error_code: bool,
) !void {
    const formatted = try SourceReferenceFormatter.formatTypedDiagnosticAlloc(
        allocator,
        provider,
        diagnostic,
        false,
        false,
    );
    try appendError(
        allocator,
        errors_value,
        diagnostic.error_type,
        diagnostic.description,
        formatted,
        diagnostic.location,
        &diagnostic.secondary,
    );
    if (include_error_code and diagnostic.error_id.value != 0) {
        const error_code = try std.fmt.allocPrint(allocator, "{d}", .{diagnostic.error_id.value});
        const appended = &errors_value.array.items[errors_value.array.items.len - 1];
        try appended.object.put(allocator, "errorCode", .{ .string = error_code });
    }
}

fn appendError(
    allocator: std.mem.Allocator,
    errors_value: *Json,
    error_type: ErrorType,
    message: []const u8,
    formatted_message: []const u8,
    location: ?Diagnostics.SourceLocation,
    secondary: ?*const Diagnostics.SecondarySourceLocation,
) !void {
    var value: Json = .{ .object = .empty };
    try value.object.put(allocator, "type", try ownedString(allocator, Diagnostics.formatErrorType(error_type)));
    try value.object.put(allocator, "component", try ownedString(allocator, "general"));
    try value.object.put(allocator, "severity", try ownedString(allocator, Diagnostics.formatErrorSeverityLowercase(Diagnostics.errorSeverity(error_type))));
    try value.object.put(allocator, "message", try ownedString(allocator, message));
    try value.object.put(allocator, "formattedMessage", try ownedString(allocator, formatted_message));
    if (location) |source_location| if (source_location.source_name != null) {
        try value.object.put(allocator, "sourceLocation", try formatSourceLocation(allocator, source_location));
    };
    if (secondary) |secondary_locations| if (secondary_locations.infos.items.len != 0) {
        var locations = std.json.Array.init(allocator);
        for (secondary_locations.infos.items) |info| {
            if (info.location.source_name == null) continue;
            var formatted = try formatSourceLocation(allocator, info.location);
            try formatted.object.put(allocator, "message", try ownedString(allocator, info.message));
            try locations.append(formatted);
        }
        try value.object.put(allocator, "secondarySourceLocations", .{ .array = locations });
    };
    try errors_value.array.append(value);
}

fn formatSourceLocation(allocator: std.mem.Allocator, location: Diagnostics.SourceLocation) !Json {
    var value: Json = .{ .object = .empty };
    try value.object.put(allocator, "file", try ownedString(allocator, location.source_name.?));
    try value.object.put(allocator, "start", .{ .integer = location.start });
    try value.object.put(allocator, "end", .{ .integer = location.end });
    return value;
}

fn ensureContract(
    allocator: std.mem.Allocator,
    output: *Json,
    source_name: []const u8,
    contract_name: []const u8,
) !*Json {
    const contracts = try ensureObject(allocator, output, "contracts");
    const source = try ensureObject(allocator, contracts, source_name);
    return ensureObject(allocator, source, contract_name);
}

fn ensureObject(allocator: std.mem.Allocator, parent: *Json, name: []const u8) !*Json {
    if (parent.* != .object) return error.ExpectedJsonObject;
    if (parent.object.getPtr(name)) |existing| {
        if (existing.* != .object) return error.ExpectedJsonObject;
        return existing;
    }
    try parent.object.put(allocator, name, .{ .object = .empty });
    return parent.object.getPtr(name).?;
}

fn finishOutput(allocator: std.mem.Allocator, output: *const Json) ![]u8 {
    return JSON.jsonPrintAlloc(allocator, output, .{ .trailing_newline = true });
}

fn resolveIndexedSource(
    source_name: []const u8,
    source_entry: *const Json,
    loaded_sources_by_name: *const std.StringHashMapUnmanaged([]const u8),
) ?[]const u8 {
    if (objectMember(source_entry, "content")) |content_value|
        if (jsonString(content_value)) |content| return content;
    return loaded_sources_by_name.get(source_name);
}

fn resolveSource(
    source_name: []const u8,
    source_entry: *const Json,
    loaded_sources: []const SourceContent,
) ?[]const u8 {
    if (objectMember(source_entry, "content")) |content_value|
        if (jsonString(content_value)) |content| return content;
    for (loaded_sources) |loaded|
        if (std.mem.eql(u8, source_name, loaded.name)) return loaded.content;
    return null;
}

fn hashMatchesContent(hash: []const u8, content: []const u8) bool {
    if (hash.len != 66 or !std.mem.startsWith(u8, hash, "0x")) return false;
    const expected = FixedHash.H256.fromString(hash, .from_hex, .fail_if_different) catch return false;
    const actual = Keccak256.keccak256(content);
    return expected.eql(&actual);
}

fn checkKeys(
    allocator: std.mem.Allocator,
    input: *const Json,
    allowed: []const []const u8,
    name: []const u8,
) !?Fatal {
    if (!jsonEmpty(input) and input.* != .object) {
        const message = try std.fmt.allocPrint(allocator, "\"{s}\" must be an object", .{name});
        return .{ .message = message };
    }
    const object = jsonObject(input) orelse return null;
    var unknown: ?[]const u8 = null;
    for (object.keys()) |key| {
        if (isOneOf(key, allowed)) continue;
        if (unknown == null or std.mem.order(u8, key, unknown.?) == .lt) unknown = key;
    }
    if (unknown) |key| {
        const message = try std.fmt.allocPrint(allocator, "Unknown key \"{s}\"", .{key});
        return .{ .message = message };
    }
    return null;
}

fn isBinaryRequested(output_selection: *const OutputSelection) bool {
    return output_selection.binary_requested;
}

/// Returns true only when every explicitly selected artifact is already
/// produced by the typed frontend. Keeping this whitelist narrow prevents a
/// successful ABI request from masking an unimplemented IR or EVM artifact.
fn requestsOnlyImplementedSolidityFrontendArtifacts(
    output_selection: *const OutputSelection,
) bool {
    return output_selection.only_frontend_artifacts;
}

/// `*`, `evm`, and every `evm.*` selection can cause the compiler to enter an
/// EVM-producing backend. Method identifiers happen to be derivable from the
/// frontend, but retaining the namespace-wide rule keeps the public contract
/// simple and prevents wildcard requests from selecting legacy codegen.
pub fn requestsSolidityEvmOutput(output_selection: *const OutputSelection) bool {
    return output_selection.solidity_evm_output_requested;
}

fn hasExactArtifactRequest(output_selection: *const OutputSelection, artifact: []const u8) bool {
    return output_selection.hasExactArtifact(artifact);
}

fn hasAnyEthdebugRequest(output_selection: *const OutputSelection) bool {
    const names = [_][]const u8{
        "evm.bytecode.ethdebug",
        "evm.deployedBytecode.ethdebug",
        "ethdebug.resources",
        "ethdebug.compilation",
    };
    for (names) |name| if (hasExactArtifactRequest(output_selection, name)) return true;
    return false;
}

fn isOneOf(value: []const u8, values: []const []const u8) bool {
    for (values) |candidate| if (std.mem.eql(u8, value, candidate)) return true;
    return false;
}

fn ownedString(allocator: std.mem.Allocator, value: []const u8) !Json {
    return .{ .string = try allocator.dupe(u8, value) };
}

fn optionalInteger(value: ?usize) Json {
    return if (value) |integer| usizeInteger(integer) else .null;
}

fn usizeInteger(value: usize) Json {
    return .{ .integer = std.math.cast(i64, value) orelse std.math.maxInt(i64) };
}

fn objectMember(input: *const Json, name: []const u8) ?*const Json {
    const object = jsonObject(input) orelse return null;
    return object.getPtr(name);
}

fn jsonObject(input: *const Json) ?*const std.json.ObjectMap {
    return switch (input.*) {
        .object => |*value| value,
        else => null,
    };
}

fn jsonArray(input: *const Json) ?*const std.json.Array {
    return switch (input.*) {
        .array => |*value| value,
        else => null,
    };
}

fn jsonString(input: *const Json) ?[]const u8 {
    return switch (input.*) {
        .string => |value| value,
        else => null,
    };
}

fn jsonBool(input: *const Json) ?bool {
    return switch (input.*) {
        .bool => |value| value,
        else => null,
    };
}

fn jsonEmpty(input: *const Json) bool {
    return switch (input.*) {
        .null => true,
        .array => |value| value.items.len == 0,
        .object => |value| value.count() == 0,
        .string => |value| value.len == 0,
        else => false,
    };
}

test "artifact selection preserves StandardCompiler prefix and wildcard rules" {
    var selection: OutputSelection = .{};
    defer selection.deinit(std.testing.allocator);
    try selection.add(std.testing.allocator, "A.yul", "A", "evm.bytecode");
    try selection.add(std.testing.allocator, "A.yul", "A", "ir");
    try std.testing.expect(isArtifactRequested(&selection, "A.yul", "A", "evm.bytecode.object", true));
    try std.testing.expect(isArtifactRequested(&selection, "A.yul", "A", "ir", true));
    try std.testing.expect(!isArtifactRequested(&selection, "A.yul", "A", "ast", true));
}

test "Solidity EVM selection is distinguished from frontend-only artifacts" {
    var frontend: OutputSelection = .{};
    defer frontend.deinit(std.testing.allocator);
    try frontend.add(std.testing.allocator, "A.sol", "A", "abi");
    try frontend.add(std.testing.allocator, "A.sol", "", "ast");
    try std.testing.expect(!requestsSolidityEvmOutput(&frontend));

    var evm: OutputSelection = .{};
    defer evm.deinit(std.testing.allocator);
    try evm.add(std.testing.allocator, "*", "*", "evm.bytecode.object");
    try std.testing.expect(requestsSolidityEvmOutput(&evm));
}

test "parsed compilation options do not borrow the JSON document" {
    var parsed = try JSON.jsonParseStrict(
        std.testing.allocator,
        "{\"settings\":{\"remappings\":[\"src:pkg/=vendor/\"]," ++
            "\"optimizer\":{\"enabled\":false,\"details\":{\"yulDetails\":{" ++
            "\"optimizerSteps\":\":\"}}},\"libraries\":{\"A.sol\":{" ++
            "\"L\":\"0x1111111111111111111111111111111111111111\"}}," ++
            "\"outputSelection\":{\"A.sol\":{\"A\":[\"evm.bytecode\"]}}}}",
    );
    const root = parsed.document.rootConst();
    const result = try parseSettings(std.testing.allocator, root);
    var options = switch (result) {
        .options => |value| value,
        .fatal => return error.UnexpectedFatalOptions,
    };
    defer options.deinit();
    parsed.deinit();

    try std.testing.expectEqualStrings(
        "src",
        options.frontend.remappings.items[0].context,
    );
    try std.testing.expectEqualStrings(
        "pkg/",
        options.frontend.remappings.items[0].prefix,
    );
    try std.testing.expectEqualStrings(
        "vendor/",
        options.frontend.remappings.items[0].target,
    );
    try std.testing.expectEqualStrings("", options.optimizer.settings.yul_optimiser_steps);
    try std.testing.expectEqualStrings("", options.optimizer.settings.yul_optimiser_cleanup_steps);
    try std.testing.expectEqualStrings("A.sol:L", options.link.libraries.items[0].name);
    try std.testing.expect(options.projection.output_selection.requests(
        "A.sol",
        "A",
        "evm.bytecode.object",
        true,
    ));
}
