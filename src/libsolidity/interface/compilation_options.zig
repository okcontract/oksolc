// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned, phase-oriented options for one compiler request.
//!
//! No field borrows the Standard JSON DOM. Hash tables are used only for
//! lookup; externally visible ordering remains the responsibility of output
//! projection.

const std = @import("std");
const DebugInfoSelection = @import("../../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const EVMVersion = @import("../../liblangutil/evm_version.zig").EVMVersion;
const LinkerObject = @import("../../libevmasm/linker_object.zig");
const CompilerStack = @import("compiler_stack.zig");
const DebugSettings = @import("debug_settings.zig");
const ImportRemapper = @import("import_remapper.zig");
const OptimiserSettings = @import("optimiser_settings.zig").OptimiserSettings;

pub const FrontendOptions = struct {
    evm_version: EVMVersion = EVMVersion.current(),
    remappings: std.ArrayList(ImportRemapper.NormalizedRemapping) = .empty,
    experimental: bool = false,
    has_smt_responses: bool = false,
    stop_after_parsing: bool = false,
    evm_version_deprecation_warning: bool = false,

    fn deinit(self: *FrontendOptions, allocator: std.mem.Allocator) void {
        for (self.remappings.items) |*remapping| remapping.deinit(allocator);
        self.remappings.deinit(allocator);
        self.* = undefined;
    }

    fn addRemapping(
        self: *FrontendOptions,
        allocator: std.mem.Allocator,
        remapping: ImportRemapper.Remapping,
    ) std.mem.Allocator.Error!void {
        var normalized = try ImportRemapper.NormalizedRemapping.initAlloc(
            allocator,
            remapping,
        );
        errdefer normalized.deinit(allocator);
        try self.remappings.append(allocator, normalized);
    }
};

pub const IrOptions = struct {
    debug_info: DebugInfoSelection = DebugInfoSelection.defaultValue(),
    revert_strings: DebugSettings.RevertStrings = .Default,
    via_ir: bool = false,
    via_ir_explicit: bool = false,
    via_ssa_cfg: bool = false,
};

pub const OptimizerOptions = struct {
    settings: OptimiserSettings = OptimiserSettings.minimal(),
    owned_steps: ?[]u8 = null,
    owned_cleanup_steps: ?[]u8 = null,

    fn deinit(self: *OptimizerOptions, allocator: std.mem.Allocator) void {
        if (self.owned_cleanup_steps) |steps| allocator.free(steps);
        if (self.owned_steps) |steps| allocator.free(steps);
        self.* = undefined;
    }

    fn assignOwned(
        self: *OptimizerOptions,
        allocator: std.mem.Allocator,
        settings: OptimiserSettings,
    ) std.mem.Allocator.Error!void {
        const steps = try allocator.dupe(u8, settings.yul_optimiser_steps);
        errdefer allocator.free(steps);
        const cleanup_steps = try allocator.dupe(
            u8,
            settings.yul_optimiser_cleanup_steps,
        );
        errdefer allocator.free(cleanup_steps);

        if (self.owned_cleanup_steps) |old| allocator.free(old);
        if (self.owned_steps) |old| allocator.free(old);
        self.settings = settings;
        self.settings.yul_optimiser_steps = steps;
        self.settings.yul_optimiser_cleanup_steps = cleanup_steps;
        self.owned_steps = steps;
        self.owned_cleanup_steps = cleanup_steps;
    }
};

pub const MetadataOptions = struct {
    hash: CompilerStack.MetadataHash = .ipfs,
    append_cbor: bool = true,
    literal_sources: bool = false,
};

pub const LinkOptions = struct {
    libraries: std.ArrayList(LinkerObject.LibraryAddress) = .empty,

    fn deinit(self: *LinkOptions, allocator: std.mem.Allocator) void {
        for (self.libraries.items) |library| allocator.free(library.name);
        self.libraries.deinit(allocator);
        self.* = undefined;
    }

    fn addLibrary(
        self: *LinkOptions,
        allocator: std.mem.Allocator,
        library: LinkerObject.LibraryAddress,
    ) std.mem.Allocator.Error!void {
        const name = try allocator.dupe(u8, library.name);
        errdefer allocator.free(name);
        try self.libraries.append(allocator, .{
            .name = name,
            .address = library.address,
        });
    }
};

const ArtifactSet = struct {
    exact: std.StringHashMapUnmanaged(void) = .empty,

    fn deinit(self: *ArtifactSet, allocator: std.mem.Allocator) void {
        var iterator = self.exact.keyIterator();
        while (iterator.next()) |key| allocator.free(key.*);
        self.exact.deinit(allocator);
        self.* = undefined;
    }

    fn add(
        self: *ArtifactSet,
        allocator: std.mem.Allocator,
        artifact: []const u8,
    ) std.mem.Allocator.Error![]const u8 {
        const result = try self.exact.getOrPut(allocator, artifact);
        if (result.found_existing) return result.key_ptr.*;
        const owned = allocator.dupe(u8, artifact) catch |err| {
            _ = self.exact.remove(artifact);
            return err;
        };
        result.key_ptr.* = owned;
        result.value_ptr.* = {};
        return owned;
    }

    fn requests(
        self: *const ArtifactSet,
        artifact: []const u8,
        wildcard_matches_experimental: bool,
    ) bool {
        var iterator = self.exact.keyIterator();
        while (iterator.next()) |requested_pointer| {
            const requested = requested_pointer.*;
            if (std.mem.eql(u8, artifact, requested) or
                (artifact.len > requested.len and
                    std.mem.startsWith(u8, artifact, requested) and
                    artifact[requested.len] == '.'))
            {
                if (std.mem.find(u8, artifact, "ethdebug") != null)
                    return std.mem.eql(u8, artifact, requested);
                return true;
            }
            if (std.mem.eql(u8, requested, "*")) {
                if (std.mem.eql(u8, artifact, "yulCFGJson")) continue;
                if (std.mem.find(u8, artifact, "ethdebug") != null) continue;
                if (!isExperimentalArtifact(artifact) or wildcard_matches_experimental)
                    return true;
            }
        }
        return false;
    }
};

const SourceSelection = struct {
    contracts: std.StringHashMapUnmanaged(ArtifactSet) = .empty,

    fn deinit(self: *SourceSelection, allocator: std.mem.Allocator) void {
        var iterator = self.contracts.iterator();
        while (iterator.next()) |entry| {
            entry.value_ptr.deinit(allocator);
            allocator.free(entry.key_ptr.*);
        }
        self.contracts.deinit(allocator);
        self.* = undefined;
    }

    fn add(
        self: *SourceSelection,
        allocator: std.mem.Allocator,
        contract: []const u8,
        artifact: []const u8,
    ) std.mem.Allocator.Error![]const u8 {
        const result = try self.contracts.getOrPut(allocator, contract);
        if (!result.found_existing) {
            const owned = allocator.dupe(u8, contract) catch |err| {
                _ = self.contracts.remove(contract);
                return err;
            };
            result.key_ptr.* = owned;
            result.value_ptr.* = .{};
        }
        return result.value_ptr.add(allocator, artifact);
    }

    fn requests(
        self: *const SourceSelection,
        contract: []const u8,
        artifact: []const u8,
        wildcard_matches_experimental: bool,
    ) bool {
        if (contract.len == 0) {
            const selected = self.contracts.get("") orelse return false;
            return selected.requests(artifact, wildcard_matches_experimental);
        }
        const candidates = [_][]const u8{ contract, "*" };
        for (candidates) |candidate| {
            const selected = self.contracts.get(candidate) orelse continue;
            if (selected.requests(artifact, wildcard_matches_experimental)) return true;
        }
        return false;
    }
};

/// Borrowed view of one output-selection rule. The containing
/// `OutputSelection` owns all three strings.
pub const OutputSelectionRule = struct {
    file: []const u8,
    contract: []const u8,
    artifact: []const u8,

    fn lessThan(_: void, left: OutputSelectionRule, right: OutputSelectionRule) bool {
        const file_order = std.mem.order(u8, left.file, right.file);
        if (file_order != .eq) return file_order == .lt;
        const contract_order = std.mem.order(u8, left.contract, right.contract);
        if (contract_order != .eq) return contract_order == .lt;
        return std.mem.order(u8, left.artifact, right.artifact) == .lt;
    }
};

/// Owned and pre-indexed Standard JSON output-selection matcher.
pub const OutputSelection = struct {
    sources: std.StringHashMapUnmanaged(SourceSelection) = .empty,
    /// Keys borrow artifact strings owned by `sources`; deinit this map first.
    all_artifacts: std.StringHashMapUnmanaged(void) = .empty,
    was_specified: bool = false,
    binary_requested: bool = false,
    only_frontend_artifacts: bool = true,
    solidity_evm_output_requested: bool = false,

    pub fn deinit(self: *OutputSelection, allocator: std.mem.Allocator) void {
        self.all_artifacts.deinit(allocator);
        var iterator = self.sources.iterator();
        while (iterator.next()) |entry| {
            entry.value_ptr.deinit(allocator);
            allocator.free(entry.key_ptr.*);
        }
        self.sources.deinit(allocator);
        self.* = undefined;
    }

    pub fn add(
        self: *OutputSelection,
        allocator: std.mem.Allocator,
        file: []const u8,
        contract: []const u8,
        artifact: []const u8,
    ) std.mem.Allocator.Error!void {
        self.was_specified = true;
        const result = try self.sources.getOrPut(allocator, file);
        if (!result.found_existing) {
            const owned = allocator.dupe(u8, file) catch |err| {
                _ = self.sources.remove(file);
                return err;
            };
            result.key_ptr.* = owned;
            result.value_ptr.* = .{};
        }
        const stored_artifact = try result.value_ptr.add(
            allocator,
            contract,
            artifact,
        );
        try self.all_artifacts.put(allocator, stored_artifact, {});

        if (!std.mem.eql(u8, artifact, "ast")) {
            self.binary_requested = true;
        }
        if (!isFrontendArtifact(artifact)) self.only_frontend_artifacts = false;
        if (std.mem.eql(u8, artifact, "*") or
            std.mem.eql(u8, artifact, "evm") or
            std.mem.startsWith(u8, artifact, "evm."))
        {
            self.solidity_evm_output_requested = true;
        }
    }

    pub fn requests(
        self: *const OutputSelection,
        file: []const u8,
        contract: []const u8,
        artifact: []const u8,
        wildcard_matches_experimental: bool,
    ) bool {
        const candidates = [_][]const u8{ file, "*" };
        for (candidates) |candidate| {
            const selected = self.sources.get(candidate) orelse continue;
            if (selected.requests(
                contract,
                artifact,
                wildcard_matches_experimental,
            )) return true;
        }
        return false;
    }

    pub fn hasExactArtifact(self: *const OutputSelection, artifact: []const u8) bool {
        return self.all_artifacts.contains(artifact);
    }

    /// Returns allocator-owned rule storage in canonical lexical order. Rule
    /// strings remain borrowed from `self` and must not outlive it.
    pub fn canonicalRulesAlloc(
        self: *const OutputSelection,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]OutputSelectionRule {
        var rules: std.ArrayList(OutputSelectionRule) = .empty;
        errdefer rules.deinit(allocator);

        var source_iterator = self.sources.iterator();
        while (source_iterator.next()) |source_entry| {
            var contract_iterator = source_entry.value_ptr.contracts.iterator();
            while (contract_iterator.next()) |contract_entry| {
                var artifact_iterator = contract_entry.value_ptr.exact.keyIterator();
                while (artifact_iterator.next()) |artifact| {
                    try rules.append(allocator, .{
                        .file = source_entry.key_ptr.*,
                        .contract = contract_entry.key_ptr.*,
                        .artifact = artifact.*,
                    });
                }
            }
        }
        std.mem.sort(OutputSelectionRule, rules.items, {}, OutputSelectionRule.lessThan);
        return rules.toOwnedSlice(allocator);
    }
};

pub const ProjectionOptions = struct {
    output_selection: OutputSelection = .{},

    fn deinit(self: *ProjectionOptions, allocator: std.mem.Allocator) void {
        self.output_selection.deinit(allocator);
        self.* = undefined;
    }
};

pub const CompilationOptions = struct {
    allocator: std.mem.Allocator,
    frontend: FrontendOptions = .{},
    ir: IrOptions = .{},
    optimizer: OptimizerOptions = .{},
    metadata: MetadataOptions = .{},
    link: LinkOptions = .{},
    projection: ProjectionOptions = .{},
    pub fn init(allocator: std.mem.Allocator) CompilationOptions {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *CompilationOptions) void {
        self.projection.deinit(self.allocator);
        self.link.deinit(self.allocator);
        self.optimizer.deinit(self.allocator);
        self.frontend.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addRemapping(
        self: *CompilationOptions,
        remapping: ImportRemapper.Remapping,
    ) std.mem.Allocator.Error!void {
        return self.frontend.addRemapping(self.allocator, remapping);
    }

    pub fn setOptimizer(
        self: *CompilationOptions,
        settings: OptimiserSettings,
    ) std.mem.Allocator.Error!void {
        return self.optimizer.assignOwned(self.allocator, settings);
    }

    pub fn addLibrary(
        self: *CompilationOptions,
        library: LinkerObject.LibraryAddress,
    ) std.mem.Allocator.Error!void {
        return self.link.addLibrary(self.allocator, library);
    }

    pub fn addOutput(
        self: *CompilationOptions,
        file: []const u8,
        contract: []const u8,
        artifact: []const u8,
    ) std.mem.Allocator.Error!void {
        return self.projection.output_selection.add(
            self.allocator,
            file,
            contract,
            artifact,
        );
    }
};

fn isFrontendArtifact(artifact: []const u8) bool {
    const names = [_][]const u8{
        "abi",
        "ast",
        "devdoc",
        "userdoc",
        "storageLayout",
        "transientStorageLayout",
    };
    for (names) |candidate| if (std.mem.eql(u8, artifact, candidate)) return true;
    return false;
}

fn isExperimentalArtifact(artifact: []const u8) bool {
    const names = [_][]const u8{
        "ir",
        "irAst",
        "irOptimized",
        "irOptimizedAst",
        "yulCFGJson",
        "ethdebug",
    };
    for (names) |candidate| if (std.mem.eql(u8, artifact, candidate)) return true;
    return false;
}

test "compiled output selection preserves wildcard and prefix semantics" {
    var selection: OutputSelection = .{};
    defer selection.deinit(std.testing.allocator);
    try selection.add(std.testing.allocator, "A.sol", "A", "evm.bytecode");
    try selection.add(std.testing.allocator, "*", "*", "abi");
    try selection.add(std.testing.allocator, "A.sol", "A", "*");

    try std.testing.expect(selection.requests(
        "A.sol",
        "A",
        "evm.bytecode.object",
        false,
    ));
    try std.testing.expect(selection.requests("B.sol", "B", "abi", false));
    try std.testing.expect(!selection.requests("A.sol", "A", "ir", false));
    try std.testing.expect(selection.requests("A.sol", "A", "ir", true));
    try std.testing.expect(!selection.requests("A.sol", "A", "yulCFGJson", true));
    try std.testing.expect(selection.hasExactArtifact("evm.bytecode"));
    try std.testing.expect(selection.binary_requested);
    try std.testing.expect(!selection.only_frontend_artifacts);
    try std.testing.expect(selection.solidity_evm_output_requested);
}

test "compiled output selection exposes deterministic canonical rules" {
    var first: OutputSelection = .{};
    defer first.deinit(std.testing.allocator);
    try first.add(std.testing.allocator, "B.sol", "B", "abi");
    try first.add(std.testing.allocator, "A.sol", "A", "evm.bytecode");
    try first.add(std.testing.allocator, "A.sol", "A", "abi");

    var second: OutputSelection = .{};
    defer second.deinit(std.testing.allocator);
    try second.add(std.testing.allocator, "A.sol", "A", "abi");
    try second.add(std.testing.allocator, "A.sol", "A", "evm.bytecode");
    try second.add(std.testing.allocator, "B.sol", "B", "abi");

    const first_rules = try first.canonicalRulesAlloc(std.testing.allocator);
    defer std.testing.allocator.free(first_rules);
    const second_rules = try second.canonicalRulesAlloc(std.testing.allocator);
    defer std.testing.allocator.free(second_rules);

    try std.testing.expectEqual(@as(usize, 3), first_rules.len);
    try std.testing.expectEqual(first_rules.len, second_rules.len);
    for (first_rules, second_rules) |left, right| {
        try std.testing.expectEqualStrings(left.file, right.file);
        try std.testing.expectEqualStrings(left.contract, right.contract);
        try std.testing.expectEqualStrings(left.artifact, right.artifact);
    }
    try std.testing.expectEqualStrings("A.sol", first_rules[0].file);
    try std.testing.expectEqualStrings("abi", first_rules[0].artifact);
    try std.testing.expectEqualStrings("evm.bytecode", first_rules[1].artifact);
    try std.testing.expectEqualStrings("B.sol", first_rules[2].file);
}

test "compilation options own every variable-length input" {
    var options = CompilationOptions.init(std.testing.allocator);
    defer options.deinit();

    var context = [_]u8{ 's', 'r', 'c' };
    var prefix = [_]u8{ 'p', 'k', 'g', '/' };
    var target = [_]u8{ 'v', 'e', 'n', 'd', 'o', 'r', '/' };
    try options.addRemapping(.{
        .context = &context,
        .prefix = &prefix,
        .target = &target,
    });
    var library_name = [_]u8{ 'A', '.', 's', 'o', 'l', ':', 'L' };
    try options.addLibrary(.{
        .name = &library_name,
        .address = .{},
    });
    var steps = [_]u8{ 'd', 'h', 'f' };
    var cleanup = [_]u8{ 'f', 'd' };
    var optimizer = OptimiserSettings.standard();
    optimizer.yul_optimiser_steps = &steps;
    optimizer.yul_optimiser_cleanup_steps = &cleanup;
    try options.setOptimizer(optimizer);
    var file = [_]u8{ 'A', '.', 's', 'o', 'l' };
    var contract = [_]u8{'A'};
    var artifact = [_]u8{ 'e', 'v', 'm' };
    try options.addOutput(&file, &contract, &artifact);

    @memset(&context, 'x');
    @memset(&prefix, 'x');
    @memset(&target, 'x');
    @memset(&library_name, 'x');
    @memset(&steps, 'x');
    @memset(&cleanup, 'x');
    @memset(&file, 'x');
    @memset(&contract, 'x');
    @memset(&artifact, 'x');

    try std.testing.expectEqualStrings("src", options.frontend.remappings.items[0].context);
    try std.testing.expectEqualStrings("pkg/", options.frontend.remappings.items[0].prefix);
    try std.testing.expectEqualStrings("vendor/", options.frontend.remappings.items[0].target);
    try std.testing.expectEqualStrings(
        "src",
        options.frontend.remappings.items[0].original_context,
    );
    try std.testing.expectEqualStrings(
        "pkg/",
        options.frontend.remappings.items[0].original_prefix,
    );
    try std.testing.expectEqualStrings(
        "vendor/",
        options.frontend.remappings.items[0].original_target,
    );
    try std.testing.expectEqualStrings("A.sol:L", options.link.libraries.items[0].name);
    try std.testing.expectEqualStrings("dhf", options.optimizer.settings.yul_optimiser_steps);
    try std.testing.expectEqualStrings("fd", options.optimizer.settings.yul_optimiser_cleanup_steps);
    try std.testing.expect(options.projection.output_selection.requests(
        "A.sol",
        "A",
        "evm.bytecode.object",
        false,
    ));
}
