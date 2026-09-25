// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Yul orchestration: parse, analyze, optimize, lower, assemble.
//!
//! Uses the EVM backend. Experimental SSA-CFG and ethdebug export return
//! unsupported errors.

const std = @import("std");
const AsmAnalysis = @import("asm_analysis.zig");
const AssemblyItem = @import("../libevmasm/assembly_item.zig");
const AssemblyModule = @import("../libevmasm/assembly.zig");
const Assembly = AssemblyModule.Assembly;
const CharStreamModule = @import("../liblangutil/char_stream.zig");
const CharStream = CharStreamModule.CharStream;
const CharStreamProvider = @import("../liblangutil/char_stream_provider.zig").CharStreamProvider;
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const EVMObjectCompiler = @import("backends/evm/evm_object_compiler.zig").EVMObjectCompiler;
const EVMDialect = @import("backends/evm/evm_dialect.zig");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const EthAssemblyAdapter = @import("backends/evm/eth_assembly_adapter.zig").EthAssemblyAdapter;
const JSON = @import("../libsolutil/json.zig");
const LinkerObject = @import("../libevmasm/linker_object.zig").LinkerObject;
const ObjectModule = @import("object.zig");
const Object = ObjectModule.Object;
const ObjectOptimizerModule = @import("object_optimizer.zig");
const ObjectOptimizer = ObjectOptimizerModule.ObjectOptimizer;
const ObjectParser = @import("object_parser.zig").ObjectParser;
const OptimiserSettingsModule = @import("../libsolidity/interface/optimiser_settings.zig");
const OptimiserSettings = OptimiserSettingsModule.OptimiserSettings;
const OptimiserSuite = @import("optimiser/suite.zig").OptimiserSuite;
const Profiler = @import("../libsolutil/profiler.zig").Profiler;
const Scanner = @import("../liblangutil/scanner.zig").Scanner;
const Semantics = @import("optimiser/semantics.zig");
const SolidityDebugNormalizer = @import("solidity_debug_normalizer.zig");

pub const Machine = enum(c_int) {
    evm,
};

pub const State = enum(c_int) {
    empty,
    parsed,
    analysis_successful,
};

const AssemblyOwner = struct {
    allocator: std.mem.Allocator,
    references: usize = 0,
    root: *Assembly,

    fn retain(self: *AssemblyOwner, assembly: *Assembly) AssemblyReference {
        self.references += 1;
        return .{ .owner = self, .value = assembly };
    }

    fn release(self: *AssemblyOwner) void {
        std.debug.assert(self.references != 0);
        self.references -= 1;
        if (self.references != 0) return;
        const allocator = self.allocator;
        self.root.destroy();
        allocator.destroy(self);
    }
};

/// Move-only shared reference into one owned assembly tree. A deployed
/// assembly can therefore outlive the creation artifact without deep-copying
/// or dangling inside its parent.
pub const AssemblyReference = struct {
    owner: ?*AssemblyOwner = null,
    value: ?*Assembly = null,

    pub fn get(self: *const AssemblyReference) ?*Assembly {
        return self.value;
    }

    pub fn deinit(self: *AssemblyReference) void {
        if (self.owner) |owner| owner.release();
        self.* = .{};
    }

    pub fn take(self: *AssemblyReference) AssemblyReference {
        const result = self.*;
        self.* = .{};
        return result;
    }
};

pub const MachineAssemblyObject = struct {
    allocator: ?std.mem.Allocator = null,
    bytecode: ?LinkerObject = null,
    assembly_reference: AssemblyReference = .{},
    source_mappings: ?[]u8 = null,

    pub fn assembly(self: *const MachineAssemblyObject) ?*Assembly {
        return self.assembly_reference.get();
    }

    pub fn deinit(self: *MachineAssemblyObject) void {
        if (self.allocator) |allocator| {
            if (self.bytecode) |*bytecode| bytecode.deinit(allocator);
            if (self.source_mappings) |source_mappings| allocator.free(source_mappings);
        }
        self.assembly_reference.deinit();
        self.* = .{};
    }

    pub fn take(self: *MachineAssemblyObject) MachineAssemblyObject {
        const result = self.*;
        self.* = .{};
        return result;
    }
};

pub const MachineAssemblyPair = struct {
    creation: MachineAssemblyObject = .{},
    deployed: MachineAssemblyObject = .{},

    pub fn deinit(self: *MachineAssemblyPair) void {
        // The deployed reference points into the creation tree.
        self.deployed.deinit();
        self.creation.deinit();
        self.* = .{};
    }

    pub fn takeCreation(self: *MachineAssemblyPair) MachineAssemblyObject {
        return self.creation.take();
    }
};

/// Move-only shared references to a lowered assembly tree. This is the
/// portable-cache seam before metadata-dependent bytecode assembly.
pub const AssemblyPair = struct {
    creation: AssemblyReference = .{},
    deployed: AssemblyReference = .{},

    pub fn initOwnedRoot(
        allocator: std.mem.Allocator,
        root: *Assembly,
        deployed_index: ?usize,
    ) !AssemblyPair {
        if (deployed_index) |index|
            if (index >= root.subs.items.len) return error.DeployObjectNotFound;
        const owner = try allocator.create(AssemblyOwner);
        owner.* = .{ .allocator = allocator, .root = root };
        var result: AssemblyPair = .{ .creation = owner.retain(root) };
        if (deployed_index) |index|
            result.deployed = owner.retain(root.subs.items[index]);
        return result;
    }

    pub fn deinit(self: *AssemblyPair) void {
        self.deployed.deinit();
        self.creation.deinit();
        self.* = .{};
    }

    pub fn deployedIndex(self: *const AssemblyPair) !?usize {
        const root = self.creation.get() orelse return error.MissingAssembly;
        const deployed = self.deployed.get() orelse return null;
        for (root.subs.items, 0..) |candidate, index|
            if (candidate == deployed) return index;
        return error.DeployObjectNotFound;
    }
};

pub const YulStack = struct {
    allocator: std.mem.Allocator,
    evm_version: EVMVersion,
    optimiser_settings: OptimiserSettings,
    debug_info_selection: DebugInfoSelection,
    solidity_source_provider: ?CharStreamProvider,
    char_stream: ?CharStream = null,
    stack_state: State = .empty,
    parser_result: ?*Object = null,
    error_reporter: Diagnostics.ErrorReporter,
    object_optimizer: *ObjectOptimizer,
    owns_object_optimizer: bool,
    profiler: ?*Profiler = null,
    /// Borrowed for assembly materialization; the caller owns the complete
    /// source graph table, which can exceed the creation object's subset.
    assembly_source_indices: ?[]const AssemblyItem.SourceIndex = null,
    /// Borrowed for lowering and assembly optimization. Backend intermediates
    /// and assembly CSE chunks use arenas backed here; emitted assembly remains
    /// owned by `allocator`. The backing allocator must outlive each call.
    backend_scratch_backing_allocator: ?std.mem.Allocator = null,

    pub fn initDefault(allocator: std.mem.Allocator) !YulStack {
        return init(
            allocator,
            EVMVersion.current(),
            OptimiserSettings.none(),
            DebugInfoSelection.defaultValue(),
            null,
            null,
        );
    }

    pub fn init(
        allocator: std.mem.Allocator,
        evm_version: EVMVersion,
        optimiser_settings: OptimiserSettings,
        debug_info_selection: DebugInfoSelection,
        solidity_source_provider: ?CharStreamProvider,
        shared_object_optimizer: ?*ObjectOptimizer,
    ) !YulStack {
        const object_optimizer = if (shared_object_optimizer) |optimizer|
            optimizer
        else optimizer: {
            const value = try allocator.create(ObjectOptimizer);
            value.* = ObjectOptimizer.init(allocator);
            break :optimizer value;
        };
        return .{
            .allocator = allocator,
            .evm_version = evm_version,
            .optimiser_settings = optimiser_settings,
            .debug_info_selection = debug_info_selection,
            .solidity_source_provider = solidity_source_provider,
            .error_reporter = Diagnostics.ErrorReporter.init(allocator),
            .object_optimizer = object_optimizer,
            .owns_object_optimizer = shared_object_optimizer == null,
        };
    }

    pub fn deinit(self: *YulStack) void {
        self.error_reporter.deinit();
        if (self.parser_result) |object| object.destroy();
        if (self.char_stream) |*stream| stream.deinit();
        if (self.owns_object_optimizer) {
            self.object_optimizer.deinit();
            self.allocator.destroy(self.object_optimizer);
        }
        self.* = undefined;
    }

    pub fn state(self: *const YulStack) State {
        return self.stack_state;
    }

    pub fn setProfiler(self: *YulStack, profiler: ?*Profiler) void {
        self.profiler = profiler;
    }

    pub fn charStream(self: *const YulStack, source_name: []const u8) !*const CharStream {
        const stream = if (self.char_stream) |*value| value else return error.InvalidStackState;
        if (!std.mem.eql(u8, stream.name(), source_name)) return error.SourceNameMismatch;
        return stream;
    }

    pub fn parseAndAnalyze(
        self: *YulStack,
        source_name: []const u8,
        source: []const u8,
    ) !bool {
        if (self.stack_state != .empty) return error.InvalidStackState;
        self.resetFailedInput();
        if (!try self.parse(source_name, source)) return false;
        const object = self.parser_result orelse return error.MissingParserResult;
        const success = try self.analyzeObjectTree(object);
        if (success) self.stack_state = .analysis_successful;
        return success;
    }

    /// Materialize an immutable generated graph directly. The copy is the
    /// consumer's mutation boundary; no generated source or parser is involved.
    pub fn analyzeGenerated(self: *YulStack, source_name: []const u8, generated: *const @import("generated_object.zig").GeneratedObject) !bool {
        if (self.stack_state != .empty) return error.InvalidStackState;
        self.resetFailedInput();
        self.char_stream = try CharStream.initOwned(self.allocator, "", source_name, false);
        const object = try generated.materialize(self.allocator);
        self.parser_result = object;
        self.stack_state = .parsed;
        const success = try self.analyzeObjectTree(object);
        if (success) self.stack_state = .analysis_successful;
        return success;
    }

    fn parse(self: *YulStack, source_name: []const u8, source: []const u8) !bool {
        self.char_stream = try CharStream.initOwned(
            self.allocator,
            source,
            source_name,
            false,
        );
        var scanner = try Scanner.init(self.allocator, &self.char_stream.?, .Solidity);
        defer scanner.deinit();
        const evm_dialect = try EVMDialect.strictAssemblyForEVMObjects(self.evm_version);
        var parser = ObjectParser.init(
            self.allocator,
            &scanner,
            &self.error_reporter,
            evm_dialect.dialect(),
        );
        self.parser_result = try parser.parse(false);
        if (!self.error_reporter.hasErrors() and self.parser_result != null)
            self.stack_state = .parsed;
        return self.stack_state == .parsed;
    }

    fn resetFailedInput(self: *YulStack) void {
        // Reconstruct the reporter so a failed parse can be retried without
        // retaining its counters. Its diagnostic locations still point into
        // the old stream, so release it before that stream.
        self.error_reporter.deinit();
        self.error_reporter = Diagnostics.ErrorReporter.init(self.allocator);
        if (self.parser_result) |object| object.destroy();
        self.parser_result = null;
        if (self.char_stream) |*stream| stream.deinit();
        self.char_stream = null;
    }

    fn analyzeObjectTree(self: *YulStack, object: *Object) !bool {
        const evm_dialect = try EVMDialect.strictAssemblyForEVMObjects(self.evm_version);
        var success = try AsmAnalysis.analyzeObject(
            self.allocator,
            object,
            &self.error_reporter,
            .{},
            AsmAnalysis.instructionValidatorForEVMDialect(evm_dialect),
        );
        for (object.sub_objects.items) |*node| switch (node.*) {
            .object => |child| if (!try self.analyzeObjectTree(child)) {
                success = false;
            },
            .data => {},
        };
        return success;
    }

    pub fn optimize(self: *YulStack) !void {
        return self.optimizeImpl(false);
    }

    /// All Solidity debug selections retain the typed tree. Annotation
    /// propagation follows the selected projection without generating source.
    pub fn optimizeTypedSolidity(self: *YulStack) !void {
        return self.optimizeImpl(true);
    }

    fn optimizeImpl(self: *YulStack, typed_solidity: bool) !void {
        if (self.stack_state != .analysis_successful) return error.AnalysisNotSuccessful;
        const object = self.parser_result orelse return error.MissingParserResult;
        if (!self.optimiser_settings.run_yul_optimiser and
            try Semantics.MSizeFinder.containsMSizeObject(object))
            return;

        var optimize_stack_allocation: bool = undefined;
        var yul_optimiser_steps: []const u8 = undefined;
        var yul_optimiser_cleanup_steps: []const u8 = undefined;
        if (!self.optimiser_settings.run_yul_optimiser) {
            const sequence = try std.fmt.allocPrint(
                self.allocator,
                "{s}:{s}",
                .{
                    self.optimiser_settings.yul_optimiser_steps,
                    self.optimiser_settings.yul_optimiser_cleanup_steps,
                },
            );
            defer self.allocator.free(sequence);
            optimize_stack_allocation = true;
            if (OptimiserSuite.isEmptyOptimizerSequence(sequence)) {
                yul_optimiser_steps = "";
                yul_optimiser_cleanup_steps = "";
            } else {
                if (!std.mem.eql(
                    u8,
                    self.optimiser_settings.yul_optimiser_steps,
                    OptimiserSettingsModule.default_yul_optimiser_steps,
                ) or !std.mem.eql(
                    u8,
                    self.optimiser_settings.yul_optimiser_cleanup_steps,
                    OptimiserSettingsModule.default_yul_optimiser_cleanup_steps,
                )) return error.InvalidDisabledOptimizerSequence;
                yul_optimiser_steps = "u";
                yul_optimiser_cleanup_steps = "";
            }
        } else {
            optimize_stack_allocation = self.optimiser_settings.optimize_stack_allocation;
            yul_optimiser_steps = self.optimiser_settings.yul_optimiser_steps;
            yul_optimiser_cleanup_steps = self.optimiser_settings.yul_optimiser_cleanup_steps;
        }

        self.stack_state = .parsed;
        try self.object_optimizer.optimize(object, .{
            .evm_version = self.evm_version,
            .optimize_stack_allocation = optimize_stack_allocation,
            .yul_optimiser_steps = yul_optimiser_steps,
            .yul_optimiser_cleanup_steps = yul_optimiser_cleanup_steps,
            .expected_executions_per_deployment = self.optimiser_settings.expected_executions_per_deployment,
            .profiler = self.profiler,
            .typed_solidity = typed_solidity,
        });
        try self.reanalyze(typed_solidity);
    }

    fn reanalyze(self: *YulStack, typed_solidity: bool) !void {
        const object = self.parser_result orelse return error.MissingParserResult;
        if (typed_solidity) {
            // Solidity artifacts only observe original-source locations.
            SolidityDebugNormalizer.normalize(object, self.debug_info_selection);
        } else {
            const stream = if (self.char_stream) |*value| value else return error.MissingCharStream;
            _ = try @import("asm_stream.zig").projectObject(object, stream.name(), self.debug_info_selection, self.solidity_source_provider);
        }
        var temporary_reporter = Diagnostics.ErrorReporter.init(self.allocator);
        defer temporary_reporter.deinit();
        const evm_dialect = try EVMDialect.strictAssemblyForEVMObjects(self.evm_version);
        if (!try analyzeObjectTreeWithReporter(
            self.allocator,
            object,
            &temporary_reporter,
            evm_dialect,
        ) or temporary_reporter.hasErrors()) return error.InvalidOptimizedYul;
        self.stack_state = .analysis_successful;
    }

    pub fn assemble(self: *YulStack, machine: Machine, via_ssa_cfg: bool) !MachineAssemblyObject {
        _ = machine;
        var pair = try self.assembleWithDeployed(null, via_ssa_cfg);
        defer pair.deinit();
        return pair.takeCreation();
    }

    pub fn assembleWithDeployed(
        self: *YulStack,
        deploy_name: ?[]const u8,
        via_ssa_cfg: bool,
    ) !MachineAssemblyPair {
        var assemblies = try self.lowerToAssemblyWithDeployed(deploy_name, via_ssa_cfg);
        defer assemblies.deinit();
        return self.materializeAssemblyPair(&assemblies);
    }

    pub fn materializeAssemblyPair(
        self: *YulStack,
        assemblies: *AssemblyPair,
    ) !MachineAssemblyPair {
        if (assemblies.creation.get() == null) return .{};

        var result: MachineAssemblyPair = .{};
        errdefer result.deinit();
        result.creation = try self.machineObjectFromAssembly(assemblies.creation.take(), true);
        if (assemblies.deployed.get() != null)
            result.deployed = try self.machineObjectFromAssembly(assemblies.deployed.take(), false);
        return result;
    }

    fn machineObjectFromAssembly(
        self: *YulStack,
        assembly_reference_input: AssemblyReference,
        creation: bool,
    ) !MachineAssemblyObject {
        var assembly_reference = assembly_reference_input;
        errdefer assembly_reference.deinit();
        const assembly = assembly_reference.get() orelse return error.MissingAssembly;
        const assembled = try assembly.assemble();
        if (creation and assembled.immutable_references.items.len != 0)
            return error.LeftoverImmutables;
        var bytecode = try assembled.clone(self.allocator);
        errdefer bytecode.deinit(self.allocator);
        const source_indices = try self.assemblySourceIndicesAlloc(self.allocator);
        defer self.allocator.free(source_indices);
        const source_mappings = try AssemblyItem.computeSourceMappingAlloc(
            self.allocator,
            assembly.itemsConst(),
            source_indices,
        );
        return .{
            .allocator = self.allocator,
            .bytecode = bytecode,
            .assembly_reference = assembly_reference,
            .source_mappings = source_mappings,
        };
    }

    pub fn lowerToAssemblyWithDeployed(
        self: *YulStack,
        deploy_name: ?[]const u8,
        via_ssa_cfg: bool,
    ) !AssemblyPair {
        if (via_ssa_cfg) return error.SSACFGBackendUnavailable;
        if (self.debug_info_selection.ethdebug) return error.EthdebugUnavailable;
        if (self.stack_state != .analysis_successful) return error.AnalysisNotSuccessful;
        const object = self.parser_result orelse return error.MissingParserResult;
        if (!object.hasCode() or object.analysis_info == null) return error.MissingAnalysisInfo;

        const root = try Assembly.create(self.allocator, self.evm_version, true, "");
        var root_owned = true;
        errdefer if (root_owned) root.destroy();
        {
            var adapter = EthAssemblyAdapter.init(self.allocator, root);
            defer adapter.deinit();
            const optimize_stack = self.optimiser_settings.optimize_stack_allocation or
                (!self.optimiser_settings.run_yul_optimiser and
                    !try Semantics.MSizeFinder.containsMSizeObject(object));
            try EVMObjectCompiler.compileWithDiagnostics(
                self.allocator,
                self.backend_scratch_backing_allocator,
                object,
                adapter.abstractAssembly(),
                optimize_stack,
                false,
                &self.error_reporter,
            );
        }
        try root.optimiseWithScratch(self.optimiser_settings.assemblySettings(), self.backend_scratch_backing_allocator);

        var deployed: ?*Assembly = null;
        if (deploy_name) |name| {
            for (root.subs.items) |sub_assembly| {
                if (std.mem.eql(u8, sub_assembly.name(), name)) {
                    deployed = sub_assembly;
                    break;
                }
            }
            if (deployed == null) return error.DeployObjectNotFound;
        } else if (root.subs.items.len == 1) {
            deployed = root.subs.items[0];
        }

        const owner = try self.allocator.create(AssemblyOwner);
        owner.* = .{ .allocator = self.allocator, .root = root };
        root_owned = false;
        var result: AssemblyPair = .{ .creation = owner.retain(root) };
        if (deployed) |runtime| result.deployed = owner.retain(runtime);
        return result;
    }

    pub fn errors(self: *const YulStack) []const Diagnostics.Diagnostic {
        return self.error_reporter.diagnostics();
    }

    pub fn hasErrors(self: *const YulStack) bool {
        return self.error_reporter.hasErrors();
    }

    pub fn hasErrorsWarningsOrInfos(self: *const YulStack) bool {
        return self.error_reporter.hasErrorsWarningsOrInfos();
    }

    pub fn print(self: *const YulStack) ![]u8 {
        return self.printAlloc(self.allocator);
    }

    /// Returns allocator-owned final IR. Only renderer temporaries use the
    /// stack allocator; the result remains valid after the stack is destroyed.
    pub fn printAlloc(self: *const YulStack, allocator: std.mem.Allocator) ![]u8 {
        if (@intFromEnum(self.stack_state) < @intFromEnum(State.parsed))
            return error.InvalidStackState;
        const object = self.parser_result orelse return error.MissingParserResult;
        return object.formatIRAlloc(allocator, self.debug_info_selection, self.solidity_source_provider);
    }

    pub fn astJson(self: *const YulStack) !@import("asm_json_converter.zig").OwnedYulJson {
        if (@intFromEnum(self.stack_state) < @intFromEnum(State.parsed))
            return error.InvalidStackState;
        const object = self.parser_result orelse return error.MissingParserResult;
        return object.toJsonAlloc(self.allocator);
    }

    pub fn cfgJson(_: *const YulStack) !JSON.Json {
        return error.ExperimentalCFGUnavailable;
    }

    pub fn parserResult(self: *const YulStack) !*const Object {
        if (self.stack_state != .analysis_successful) return error.AnalysisNotSuccessful;
        return self.parser_result orelse error.MissingParserResult;
    }

    pub fn dialect(self: *const YulStack) !@import("ast.zig").Dialect {
        const object = try self.parserResult();
        return (object.dialect() orelse return error.MissingDialect).*;
    }

    pub fn debugInfoSelection(self: *const YulStack) DebugInfoSelection {
        return self.debug_info_selection;
    }

    pub fn optimiserSettings(self: *const YulStack) OptimiserSettings {
        return self.optimiser_settings;
    }

    pub fn evmVersion(self: *const YulStack) EVMVersion {
        return self.evm_version;
    }

    /// Allocator shared by the parsed object, lowered assembly, and machine
    /// artifacts. Backend cache decoding must use this allocator so the
    /// resulting move-only objects retain correct ownership.
    pub fn artifactAllocator(self: *const YulStack) std.mem.Allocator {
        return self.allocator;
    }

    /// Returns an owned index table whose names remain borrowed from the
    /// analyzed object/character stream.
    pub fn assemblySourceIndicesAlloc(
        self: *const YulStack,
        allocator: std.mem.Allocator,
    ) ![]AssemblyItem.SourceIndex {
        if (self.assembly_source_indices) |indices|
            return allocator.dupe(AssemblyItem.SourceIndex, indices);
        const stream = if (self.char_stream) |*value| value else return error.MissingCharStream;
        if (self.parser_result) |object|
            if (object.debug_data) |debug_data|
                if (debug_data.source_names) |source_names|
                    if (source_names.entries.items.len != 0) {
                        const result = try allocator.alloc(
                            AssemblyItem.SourceIndex,
                            source_names.entries.items.len,
                        );
                        for (source_names.entries.items, result) |entry, *target|
                            target.* = .{
                                .source_name = entry.name,
                                .index = entry.index,
                            };
                        return result;
                    };
        const result = try allocator.alloc(AssemblyItem.SourceIndex, 1);
        result[0] = .{ .source_name = stream.name(), .index = 0 };
        return result;
    }
};

fn analyzeObjectTreeWithReporter(
    allocator: std.mem.Allocator,
    object: *Object,
    reporter: *Diagnostics.ErrorReporter,
    dialect: *const EVMDialect.EVMDialect,
) !bool {
    var success = try AsmAnalysis.analyzeObject(
        allocator,
        object,
        reporter,
        .{},
        AsmAnalysis.instructionValidatorForEVMDialect(dialect),
    );
    for (object.sub_objects.items) |*node| switch (node.*) {
        .object => |child| if (!try analyzeObjectTreeWithReporter(
            allocator,
            child,
            reporter,
            dialect,
        )) {
            success = false;
        },
        .data => {},
    };
    return success;
}

fn reparseForTest(self: *YulStack) !void {
    if (!@import("builtin").is_test) @compileError("text reparsing is a test oracle only");
    const stream = if (self.char_stream) |*value| value else return error.MissingCharStream;
    const source = try self.print();
    defer self.allocator.free(source);
    var temporary_reporter = Diagnostics.ErrorReporter.init(self.allocator);
    defer temporary_reporter.deinit();
    const evm_dialect = try EVMDialect.strictAssemblyForEVMObjects(self.evm_version);
    const replacement = (try ObjectParser.parseSource(
        self.allocator,
        source,
        stream.name(),
        &temporary_reporter,
        evm_dialect.dialect(),
    )) orelse return error.InvalidOptimizedYul;
    errdefer replacement.destroy();
    if (temporary_reporter.hasErrors()) return error.InvalidOptimizedYul;
    if (!try analyzeObjectTreeWithReporter(
        self.allocator,
        replacement,
        &temporary_reporter,
        evm_dialect,
    ) or temporary_reporter.hasErrors()) return error.InvalidOptimizedYul;
    if (self.parser_result) |old| old.destroy();
    self.parser_result = replacement;
    self.stack_state = .analysis_successful;
}

test "Yul stack parses, analyzes, prints, exports JSON, and retries failures" {
    const allocator = std.testing.allocator;
    var stack = try YulStack.initDefault(allocator);
    defer stack.deinit();
    try std.testing.expect(!try stack.parseAndAnalyze("input.yul", "{ let := }"));
    try std.testing.expect(stack.hasErrors());
    try std.testing.expect(try stack.parseAndAnalyze("input.yul", "{ let x := 1 pop(x) }"));
    try std.testing.expectEqual(State.analysis_successful, stack.state());
    try std.testing.expect(!stack.hasErrors());
    const printed = try stack.print();
    defer allocator.free(printed);
    try std.testing.expect(std.mem.find(u8, printed, "let x := 1") != null);
    var json = try stack.astJson();
    defer json.deinit();
    try std.testing.expect(json.value == .object);
    try std.testing.expectError(error.ExperimentalCFGUnavailable, stack.cfgJson());
}

test "ordinary Yul stack assembles creation and deployed bytecode with shared ownership" {
    const allocator = std.testing.allocator;
    var settings = OptimiserSettings.none();
    settings.yul_optimiser_steps = "";
    settings.yul_optimiser_cleanup_steps = "";
    var stack = try YulStack.init(
        allocator,
        EVMVersion.current(),
        settings,
        DebugInfoSelection.noneValue(),
        null,
        null,
    );
    defer stack.deinit();
    const source =
        \\object "Root" {
        \\  code { datacopy(0, dataoffset("Root_deployed"), datasize("Root_deployed")) return(0, datasize("Root_deployed")) }
        \\  object "Root_deployed" { code { mstore(0, 42) return(0, 32) } }
        \\}
    ;
    try std.testing.expect(try stack.parseAndAnalyze("input.yul", source));
    try stack.optimize();
    var pair = try stack.assembleWithDeployed(null, false);
    defer pair.deinit();
    try std.testing.expect(pair.creation.bytecode.?.bytecode.items.len != 0);
    try std.testing.expect(pair.deployed.bytecode.?.bytecode.items.len != 0);
    try std.testing.expect(pair.creation.assembly() != null);
    try std.testing.expect(pair.deployed.assembly() != null);
    try std.testing.expect(pair.creation.source_mappings != null);
    try std.testing.expectError(
        error.SSACFGBackendUnavailable,
        stack.assembleWithDeployed(null, true),
    );
}

test "Yul stack typed Solidity reanalysis preserves artifacts and tree ownership" {
    const allocator = std.testing.allocator;
    const source =
        \\/// @use-src 0:"input.sol"
        \\object "Root" {
        \\ code {
        \\  /// @src 0:0:50
        \\  mstore(0, f(calldataload(0)))
        \\  return(0, 32)
        \\  /// @ast-id 7
        \\  function f(x) -> r {
        \\   /// @src 0:10:20
        \\   switch x case 0 { r := 42 } default { r := add(x, 1) }
        \\  }
        \\ }
        \\}
    ;
    for ([_]DebugInfoSelection{
        DebugInfoSelection.defaultValue(),
        DebugInfoSelection.noneValue(),
        DebugInfoSelection.only(.location),
        DebugInfoSelection.only(.ast_id),
    }) |debug_selection| {
        var reference = try YulStack.init(allocator, EVMVersion.current(), OptimiserSettings.standard(), debug_selection, null, null);
        defer reference.deinit();
        var candidate = try YulStack.init(allocator, EVMVersion.current(), OptimiserSettings.standard(), debug_selection, null, null);
        defer candidate.deinit();
        try std.testing.expect(try reference.parseAndAnalyze("input.sol", source));
        try std.testing.expect(try candidate.parseAndAnalyze("input.sol", source));
        const original = candidate.parser_result.?;
        try reference.optimize();
        try candidate.optimizeTypedSolidity();
        try std.testing.expect(original == candidate.parser_result.?);
        const expected_ir = try reference.print();
        defer allocator.free(expected_ir);
        const actual_ir = try candidate.print();
        defer allocator.free(actual_ir);
        try std.testing.expectEqualStrings(expected_ir, actual_ir);
        var expected = try reference.assemble(.evm, false);
        defer expected.deinit();
        var actual = try candidate.assemble(.evm, false);
        defer actual.deinit();
        try std.testing.expectEqualSlices(u8, expected.bytecode.?.bytecode.items, actual.bytecode.?.bytecode.items);
        try std.testing.expectEqualStrings(expected.source_mappings.?, actual.source_mappings.?);
    }
}

test "Yul stack accepts the complete Solidity source table during assembly" {
    const allocator = std.testing.allocator;
    var stack = try YulStack.initDefault(allocator);
    defer stack.deinit();
    try std.testing.expect(try stack.parseAndAnalyze("generated.yul",
        \\/// @use-src 3:"Root.sol"
        \\object "Root" {
        \\ code { }
        \\ /// @use-src 3:"Root.sol", 7:"Library.sol"
        \\ object "Root_deployed" {
        \\  code { /// @src 7:10:20
        \\   mstore(0, 1) return(0, 32)
        \\  }
        \\  /// @use-src 9:"Nested.sol"
        \\  object "Nested" { code { } }
        \\ }
        \\}
    ));
    stack.assembly_source_indices = &.{
        .{ .source_name = "Root.sol", .index = 3 },
        .{ .source_name = "Library.sol", .index = 7 },
        .{ .source_name = "Nested.sol", .index = 9 },
    };
    const indices = try stack.assemblySourceIndicesAlloc(allocator);
    defer allocator.free(indices);
    try std.testing.expectEqual(@as(usize, 3), indices.len);
    try std.testing.expectEqual(@as(u32, 7), indices[1].index);
    try std.testing.expectEqualStrings("Library.sol", indices[1].source_name);
    try std.testing.expectEqual(@as(u32, 9), indices[2].index);
    var pair = try stack.assembleWithDeployed("Root_deployed", false);
    defer pair.deinit();
    try std.testing.expect(std.mem.startsWith(u8, pair.deployed.source_mappings.?, "10:10:7:"));
}

test "structured Yul cache survives producer destruction and consumer mutation" {
    const allocator = std.testing.allocator;
    const source =
        \\/// @use-src 0:"input.sol"
        \\object "Root" { code {
        \\ /// @src 0:1:20
        \\ mstore(0, f(calldataload(0))) return(0, 32)
        \\ /// @ast-id 7 @src 0:30:80
        \\ function f(x) -> r {
        \\  switch x case 0 { r := 42 } default { r := add(x, 1) }
        \\ }
        \\} }
    ;
    const Store = @import("../incremental/artifact_store.zig");
    const Fingerprint = @import("../incremental/phase_key.zig").CompilerFingerprint;
    var store = Store.MemoryArtifactStore.init(allocator);
    defer store.deinit();
    for (0..2) |restart| {
        var cache = try ObjectOptimizer.initWithBackingStore(allocator, Fingerprint.init("structured-cache-test"), store.artifactStore());
        defer cache.deinit();
        for ([_]DebugInfoSelection{ .defaultValue(), .noneValue(), .only(.location), .only(.ast_id) }) |selection| {
            var reference = try YulStack.initDefault(allocator);
            defer reference.deinit();
            reference.debug_info_selection = selection;
            try std.testing.expect(try reference.parseAndAnalyze("input.sol", source));
            try reference.optimize();
            const expected_ir = try reference.print();
            defer allocator.free(expected_ir);
            var expected = try reference.assemble(.evm, false);
            defer expected.deinit();

            for (0..3) |_| {
                var candidate = try YulStack.init(allocator, EVMVersion.current(), OptimiserSettings.none(), selection, null, &cache);
                defer candidate.deinit();
                try std.testing.expect(try candidate.parseAndAnalyze("input.sol", source));
                try candidate.optimizeTypedSolidity();
                const actual_ir = try candidate.print();
                defer allocator.free(actual_ir);
                try std.testing.expectEqualStrings(expected_ir, actual_ir);
                var actual = try candidate.assemble(.evm, false);
                defer actual.deinit();
                try std.testing.expectEqualSlices(u8, expected.bytecode.?.bytecode.items, actual.bytecode.?.bytecode.items);
                try std.testing.expectEqualStrings(expected.source_mappings.?, actual.source_mappings.?);
                // Destroying or modifying a consumer cannot mutate the cached tree.
                candidate.parser_result.?.code_value.?.root_block.debug_data = null;
            }
        }
        try std.testing.expectEqual(@as(u64, if (restart == 0) 1 else 0), cache.statistics().optimization_runs);
        try std.testing.expectEqual(@as(u64, if (restart == 0) 0 else 1), cache.statistics().persistent_hits);
        try std.testing.expectEqual(@as(u64, 11), cache.statistics().memory_hits);
    }
}

test "Yul stack normalizes synthetic annotations and native offsets without reparsing" {
    const AST = @import("ast.zig");
    const allocator = std.testing.allocator;
    const source =
        \\/// @use-src 0:"input.sol"
        \\object "Root" { code {
        \\ /// @src 0:1:10
        \\ let x := calldataload(0)
        \\ mstore(0, x)
        \\ function f(a) -> r {
        \\  /// @ast-id 12 @src 0:20:30
        \\  for { let i := 0 } lt(i, a) { i := add(i, 1) } {
        \\   if eq(i, 3) { continue }
        \\   switch i case 1 { r := add(r, 1) } default { r := add(r, 2) }
        \\   if gt(r, 8) { break }
        \\  }
        \\  leave
        \\ }
        \\ mstore(32, f(x))
        \\ return(0, 64)
        \\} }
    ;
    for ([_]DebugInfoSelection{ .defaultValue(), .noneValue(), .only(.location), .only(.ast_id) }) |selection| for ([_]bool{ false, true }) |typed_solidity| {
        var reference = try YulStack.initDefault(allocator);
        defer reference.deinit();
        var candidate = try YulStack.initDefault(allocator);
        defer candidate.deinit();
        reference.debug_info_selection = selection;
        candidate.debug_info_selection = selection;
        for ([_]*YulStack{ &reference, &candidate }) |stack| {
            try std.testing.expect(try stack.parseAndAnalyze("input.sol", source));
            const statements = stack.parser_result.?.code_value.?.root_block.statements.items;
            // Optimizers can synthesize missing annotations and give a call and
            // its name different annotations. Both must follow scanner semantics.
            const call = &statements[1].expression_statement.expression.function_call;
            statements[1].expression_statement.debug_data = null;
            call.debug_data = .{ .origin_location = .{ .start = 40, .end = 50, .source_name = "input.sol" } };
            call.function_name.builtin.debug_data = .{ .ast_id = 9, .origin_location = call.debug_data.?.origin_location };
            call.arguments.items[0].literal.debug_data = null;
            const definition: *AST.FunctionDefinition = &statements[2].function_definition;
            definition.body.debug_data = null;
            definition.parameters.items[0].debug_data = null;
            definition.body.statements.items[0].for_loop.body.statements.items[1].switch_statement.cases.items[0].debug_data = null;
        }
        try reparseForTest(&reference);
        try candidate.reanalyze(typed_solidity);
        const expected_ir = try reference.print();
        defer allocator.free(expected_ir);
        const actual_ir = try candidate.print();
        defer allocator.free(actual_ir);
        try std.testing.expectEqualStrings(expected_ir, actual_ir);

        var expected = try reference.astJson();
        defer expected.deinit();
        var actual = try candidate.astJson();
        defer actual.deinit();
        const Projection = struct {
            fn removeNativeLocations(value: *JSON.Json) void {
                switch (value.*) {
                    .object => |*object| {
                        _ = object.swapRemove("nativeSrc");
                        for (object.values()) |*child| removeNativeLocations(child);
                    },
                    .array => |*array| for (array.items) |*child| removeNativeLocations(child),
                    else => {},
                }
            }
        };
        if (typed_solidity) {
            Projection.removeNativeLocations(&expected.value);
            Projection.removeNativeLocations(&actual.value);
        }
        const expected_json = try JSON.jsonCompactPrintAlloc(allocator, &expected.value);
        defer allocator.free(expected_json);
        const actual_json = try JSON.jsonCompactPrintAlloc(allocator, &actual.value);
        defer allocator.free(actual_json);
        try std.testing.expectEqualStrings(expected_json, actual_json);
    };
}

test "structured Yul cache preserves native artifacts across memory and disk hits" {
    const allocator = std.testing.allocator;
    const source =
        \\object "Root" { code { datacopy(0, dataoffset("Child"), datasize("Child")) return(0, datasize("Child")) }
        \\ object "Child" { code {
        \\  let x := verbatim_0i_1o(hex"6001")
        \\  for { let i := 0 } lt(i, 4) { i := add(i, 1) } {
        \\   switch i case 2 { continue } default { x := add(x, i) }
        \\  }
        \\  mstore(0, x) return(0, 32)
        \\ } }
        \\}
    ;
    const Store = @import("../incremental/artifact_store.zig");
    const Fingerprint = @import("../incremental/phase_key.zig").CompilerFingerprint;
    var store = Store.MemoryArtifactStore.init(allocator);
    defer store.deinit();
    for (0..2) |restart| {
        var cache = try ObjectOptimizer.initWithBackingStore(allocator, Fingerprint.init("native-ast-cache-test"), store.artifactStore());
        defer cache.deinit();
        for ([_]DebugInfoSelection{ .defaultValue(), .noneValue(), .only(.location), .only(.ast_id) }) |selection| {
            var reference = try YulStack.init(allocator, EVMVersion.current(), OptimiserSettings.standard(), selection, null, null);
            defer reference.deinit();
            reference.debug_info_selection = selection;
            try std.testing.expect(try reference.parseAndAnalyze("input.yul", source));
            try reference.optimize();
            const expected_ir = try reference.print();
            defer allocator.free(expected_ir);
            var expected = try reference.assembleWithDeployed("Child", false);
            defer expected.deinit();
            for (0..2) |_| {
                var candidate = try YulStack.init(allocator, EVMVersion.current(), OptimiserSettings.standard(), selection, null, &cache);
                defer candidate.deinit();
                try std.testing.expect(try candidate.parseAndAnalyze("input.yul", source));
                try candidate.optimize();
                const actual_ir = try candidate.print();
                defer allocator.free(actual_ir);
                try std.testing.expectEqualStrings(expected_ir, actual_ir);
                var actual = try candidate.assembleWithDeployed("Child", false);
                defer actual.deinit();
                inline for (.{ "creation", "deployed" }) |field| {
                    try std.testing.expectEqualSlices(u8, @field(expected, field).bytecode.?.bytecode.items, @field(actual, field).bytecode.?.bytecode.items);
                    try std.testing.expectEqualStrings(@field(expected, field).source_mappings.?, @field(actual, field).source_mappings.?);
                }
            }
        }
        try std.testing.expectEqual(@as(u64, if (restart == 0) 2 else 0), cache.statistics().optimization_runs);
        try std.testing.expectEqual(@as(u64, if (restart == 0) 0 else 2), cache.statistics().persistent_hits);
        try std.testing.expectEqual(@as(u64, 14), cache.statistics().memory_hits);
    }
}

test "Yul stack owned printing survives independent allocator failures and owner destruction" {
    const allocator = std.testing.allocator;
    const source = "object \"A\" { code { let x := add(1, 2) pop(x) } data \"blob\" hex\"0102\" }";
    var reference = try YulStack.initDefault(allocator);
    defer reference.deinit();
    try std.testing.expect(try reference.parseAndAnalyze("print-ownership.yul", source));
    reference.debug_info_selection = .{};
    const object = try reference.parserResult();
    const body = try object.formatAlloc(allocator, .{}, null);
    defer allocator.free(body);
    var empty: [0]u8 = .{};
    var writer = std.Io.Writer.fixed(&empty);
    try std.testing.expectError(error.WriteFailed, object.writeTo(&writer, .{}, null));
    const Check = struct {
        fn run(failing: std.mem.Allocator, input: []const u8, expected: []const u8, fail_output: bool, ethdebug: bool) !void {
            const output_allocator = if (fail_output) failing else std.testing.allocator;
            const result = blk: {
                const stack_allocator = if (fail_output) std.testing.allocator else failing;
                var stack = try YulStack.initDefault(stack_allocator);
                defer stack.deinit();
                try std.testing.expect(try stack.parseAndAnalyze("print-ownership.yul", input));
                stack.debug_info_selection = .{ .ethdebug = ethdebug };
                break :blk try stack.printAlloc(output_allocator);
            };
            defer output_allocator.free(result);
            try std.testing.expectEqualStrings(expected, result);
        }
    };
    for ([_]bool{ false, true }) |ethdebug| {
        const expected = try std.fmt.allocPrint(allocator, "{s}{s}\n", .{
            if (ethdebug) "/// ethdebug: enabled\n" else "", body,
        });
        defer allocator.free(expected);
        try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ source, expected, false, ethdebug });
        try std.testing.checkAllAllocationFailures(allocator, Check.run, .{ source, expected, true, ethdebug });
    }
}
