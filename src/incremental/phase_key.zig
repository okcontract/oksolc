// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Versioned artifact keys and phase-specific option fingerprints.

const std = @import("std");
const builtin = @import("builtin");
const build_options = @import("build_options");
const CompilationOptions = @import("../libsolidity/interface/compilation_options.zig").CompilationOptions;
const H256 = @import("key_hasher.zig").H256;
const KeyHasher = @import("key_hasher.zig").KeyHasher;
const Identity = @import("identity.zig");
const Version = @import("../libsolidity/interface/version.zig");

pub const SourceKey = Identity.SourceKey;
pub const ContractKey = Identity.ContractKey;
pub const FrontendFingerprint = H256;

/// Stable wire values for cache namespaces. Append new kinds; never renumber
/// an existing kind without replacing the artifact-key schema.
pub const ArtifactKind = enum(u8) {
    exact_response = 1,
    optimized_yul = 2,
    solidity_ir = 3,
    creation_machine = 4,
    deployed_machine = 5,
    metadata = 6,
    linked_creation = 7,
    linked_deployed = 8,
    projected_output = 9,
    assembly_blueprint = 10,
};

fn DigestKey(comptime key_domain: []const u8) type {
    return struct {
        const Self = @This();

        digest: H256,

        pub fn fromDigest(value: H256) Self {
            return .{ .digest = value };
        }

        pub fn fromBytes(value: [H256.size]u8) Self {
            return fromDigest(H256.fromArray(value));
        }

        pub fn bytes(self: *const Self) []const u8 {
            return self.digest.bytes();
        }

        pub fn eql(self: *const Self, other: *const Self) bool {
            return self.digest.eql(&other.digest);
        }

        pub fn lessThan(self: *const Self, other: *const Self) bool {
            return self.digest.lessThan(&other.digest);
        }

        pub const domain = key_domain;
    };
}

pub const CompilerFingerprint = struct {
    const Storage = DigestKey("compiler");
    const schema_version: u32 = 1;
    pub const cache_abi_epoch: u32 = 1;

    storage: Storage,
    persistent_safe: bool,

    /// Fingerprints an explicit compiler/executable identity supplied by the
    /// embedding application.
    pub fn init(identity: []const u8) CompilerFingerprint {
        var hasher = KeyHasher.init("compiler.executable", schema_version);
        hasher.addU32(1, cache_abi_epoch);
        hasher.addBytes(2, identity);
        return fromDigest(hasher.finish());
    }

    pub fn current() CompilerFingerprint {
        var hasher = KeyHasher.init("compiler.executable", schema_version);
        hasher.addU32(1, cache_abi_epoch);
        hasher.addBytes(2, Version.VersionString);
        hasher.addBytes(3, builtin.zig_version_string);
        hasher.addBytes(4, @tagName(builtin.mode));
        hasher.addBytes(5, @tagName(builtin.target.cpu.arch));
        hasher.addBytes(6, @tagName(builtin.target.os.tag));
        hasher.addBytes(7, @tagName(builtin.target.abi));
        hasher.addBool(8, build_options.compiler_build_identity_available);
        hasher.addBytes(9, build_options.compiler_build_identity);
        return .{
            .storage = Storage.fromDigest(hasher.finish()),
            .persistent_safe = build_options.compiler_build_identity_available,
        };
    }

    pub fn fromDigest(value: H256) CompilerFingerprint {
        return .{
            .storage = Storage.fromDigest(value),
            .persistent_safe = true,
        };
    }

    pub fn unidentified() CompilerFingerprint {
        var result = init("unidentified");
        result.persistent_safe = false;
        return result;
    }

    pub fn digest(self: *const CompilerFingerprint) H256 {
        return self.storage.digest;
    }

    pub fn bytes(self: *const CompilerFingerprint) []const u8 {
        return self.storage.bytes();
    }

    pub fn eql(self: *const CompilerFingerprint, other: *const CompilerFingerprint) bool {
        return self.persistent_safe == other.persistent_safe and
            self.storage.eql(&other.storage);
    }

    pub fn isPersistentSafe(self: CompilerFingerprint) bool {
        return self.persistent_safe;
    }
};

pub const PersistentFingerprintError = error{UnidentifiedCompilerBuild};

pub const ArtifactKey = struct {
    const Storage = DigestKey("artifact");

    storage: Storage,

    pub fn fromDigest(value: H256) ArtifactKey {
        return .{ .storage = Storage.fromDigest(value) };
    }

    pub fn fromBytes(value: [H256.size]u8) ArtifactKey {
        return fromDigest(H256.fromArray(value));
    }

    pub fn digest(self: *const ArtifactKey) H256 {
        return self.storage.digest;
    }

    pub fn bytes(self: *const ArtifactKey) []const u8 {
        return self.storage.bytes();
    }

    pub fn eql(self: *const ArtifactKey, other: *const ArtifactKey) bool {
        return self.storage.eql(&other.storage);
    }

    pub fn lessThan(self: *const ArtifactKey, other: *const ArtifactKey) bool {
        return self.storage.lessThan(&other.storage);
    }
};

/// Builds the artifact key described by the incremental cache schema. Calls
/// are ordered: dependency and input order is part of the canonical key.
pub const PhaseKeyBuilder = struct {
    pub const schema_version: u32 = 1;

    hasher: KeyHasher,

    pub fn init(kind: ArtifactKind, compiler: CompilerFingerprint) PhaseKeyBuilder {
        var hasher = KeyHasher.init("compiler.artifact", schema_version);
        hasher.addU8(1, @intFromEnum(kind));
        const compiler_digest = compiler.digest();
        hasher.addDigest(2, &compiler_digest);
        return .{ .hasher = hasher };
    }

    pub fn addSettings(self: *PhaseKeyBuilder, settings: H256) void {
        self.hasher.addDigest(3, &settings);
    }

    pub fn addSource(self: *PhaseKeyBuilder, source: SourceKey) void {
        const digest = source.digest();
        self.hasher.addDigest(4, &digest);
    }

    pub fn addContract(self: *PhaseKeyBuilder, contract: ContractKey) void {
        const digest = contract.digest();
        self.hasher.addDigest(5, &digest);
    }

    pub fn addInputDigest(self: *PhaseKeyBuilder, digest: H256) void {
        self.hasher.addDigest(6, &digest);
    }

    pub fn addInputBytes(self: *PhaseKeyBuilder, bytes: []const u8) void {
        self.hasher.addBytes(7, bytes);
    }

    pub fn addDependency(self: *PhaseKeyBuilder, dependency: ArtifactKey) void {
        const digest = dependency.digest();
        self.hasher.addDigest(8, &digest);
    }

    pub fn finish(self: *PhaseKeyBuilder) ArtifactKey {
        return ArtifactKey.fromDigest(self.hasher.finish());
    }
};

pub const PhaseFingerprints = struct {
    frontend: H256,
    ir: H256,
    optimizer: H256,
    metadata: H256,
    link: H256,
    projection: H256,

    pub fn initAlloc(
        allocator: std.mem.Allocator,
        options: *const CompilationOptions,
    ) std.mem.Allocator.Error!PhaseFingerprints {
        return .{
            .frontend = frontendFingerprint(options),
            .ir = fingerprintIr(options),
            .optimizer = fingerprintOptimizer(options),
            .metadata = fingerprintMetadata(options),
            .link = fingerprintLink(options),
            .projection = try fingerprintProjection(allocator, options),
        };
    }
};

/// Semantic settings consumed before IR generation. Source contents and
/// output projection remain separate invalidation dimensions.
pub fn frontendFingerprint(options: *const CompilationOptions) FrontendFingerprint {
    var hasher = KeyHasher.init("settings.frontend", 1);
    hasher.addBytes(1, options.frontend.evm_version.name());
    hasher.addU64(2, @intCast(options.frontend.remappings.items.len));
    for (options.frontend.remappings.items) |remapping| {
        hasher.addBytes(3, remapping.context);
        hasher.addBytes(4, remapping.prefix);
        hasher.addBytes(5, remapping.target);
    }
    hasher.addBool(6, options.frontend.experimental);
    hasher.addBool(7, options.frontend.has_smt_responses);
    hasher.addBool(8, options.frontend.stop_after_parsing);
    hasher.addBool(9, options.frontend.evm_version_deprecation_warning);
    // The Solidity syntax checker rejects `msize` in inline assembly when the
    // Yul optimizer is active, so this optimizer setting also belongs to the
    // frontend invalidation domain.
    hasher.addBool(10, options.optimizer.settings.run_yul_optimiser);
    return hasher.finish();
}

fn fingerprintIr(options: *const CompilationOptions) H256 {
    var hasher = KeyHasher.init("settings.ir", 1);
    hasher.addBool(1, options.ir.debug_info.location);
    hasher.addBool(2, options.ir.debug_info.snippet);
    hasher.addBool(3, options.ir.debug_info.ast_id);
    hasher.addBool(4, options.ir.debug_info.ethdebug);
    hasher.addBytes(5, options.ir.revert_strings.toString());
    hasher.addBool(6, options.ir.via_ir);
    hasher.addBool(7, options.ir.via_ir_explicit);
    hasher.addBool(8, options.ir.via_ssa_cfg);
    return hasher.finish();
}

fn fingerprintOptimizer(options: *const CompilationOptions) H256 {
    const settings = options.optimizer.settings;
    var hasher = KeyHasher.init("settings.optimizer", 1);
    hasher.addBool(1, settings.run_order_literals);
    hasher.addBool(2, settings.run_inliner);
    hasher.addBool(3, settings.run_jumpdest_remover);
    hasher.addBool(4, settings.run_peephole);
    hasher.addBool(5, settings.run_deduplicate);
    hasher.addBool(6, settings.run_cse);
    hasher.addBool(7, settings.run_constant_optimiser);
    hasher.addBool(8, settings.simple_counter_for_loop_unchecked_increment);
    hasher.addBool(9, settings.optimize_stack_allocation);
    hasher.addBool(10, settings.run_yul_optimiser);
    hasher.addBytes(11, settings.yul_optimiser_steps);
    hasher.addBytes(12, settings.yul_optimiser_cleanup_steps);
    hasher.addU64(13, settings.expected_executions_per_deployment);
    return hasher.finish();
}

fn fingerprintMetadata(options: *const CompilationOptions) H256 {
    var hasher = KeyHasher.init("settings.metadata", 1);
    hasher.addBytes(1, options.metadata.hash.name());
    hasher.addBool(2, options.metadata.append_cbor);
    hasher.addBool(3, options.metadata.literal_sources);
    return hasher.finish();
}

fn fingerprintLink(options: *const CompilationOptions) H256 {
    var hasher = KeyHasher.init("settings.link", 1);
    hasher.addU64(1, @intCast(options.link.libraries.items.len));
    for (options.link.libraries.items) |library| {
        hasher.addBytes(2, library.name);
        hasher.addBytes(3, library.address.bytes());
    }
    return hasher.finish();
}

fn fingerprintProjection(
    allocator: std.mem.Allocator,
    options: *const CompilationOptions,
) std.mem.Allocator.Error!H256 {
    const selection = &options.projection.output_selection;
    const rules = try selection.canonicalRulesAlloc(allocator);
    defer allocator.free(rules);

    var hasher = KeyHasher.init("settings.projection", 1);
    hasher.addBool(1, selection.was_specified);
    hasher.addBool(2, selection.binary_requested);
    hasher.addBool(3, selection.only_frontend_artifacts);
    hasher.addBool(4, selection.solidity_evm_output_requested);
    hasher.addU64(5, @intCast(rules.len));
    for (rules) |rule| {
        hasher.addBytes(6, rule.file);
        hasher.addBytes(7, rule.contract);
        hasher.addBytes(8, rule.artifact);
    }
    return hasher.finish();
}

test "phase keys separate artifact kinds, compilers, framing, and order" {
    const compiler = CompilerFingerprint.init("compiler-a");
    const source = SourceKey.init("A.sol");
    const contract = ContractKey.init(source, "A");

    var first_builder = PhaseKeyBuilder.init(.optimized_yul, compiler);
    first_builder.addSource(source);
    first_builder.addContract(contract);
    first_builder.addInputBytes("ab");
    first_builder.addInputBytes("c");
    const first = first_builder.finish();

    var same_builder = PhaseKeyBuilder.init(.optimized_yul, compiler);
    same_builder.addSource(source);
    same_builder.addContract(contract);
    same_builder.addInputBytes("ab");
    same_builder.addInputBytes("c");
    const same = same_builder.finish();
    try std.testing.expect(first.eql(&same));

    var framed_builder = PhaseKeyBuilder.init(.optimized_yul, compiler);
    framed_builder.addSource(source);
    framed_builder.addContract(contract);
    framed_builder.addInputBytes("a");
    framed_builder.addInputBytes("bc");
    const framed = framed_builder.finish();
    try std.testing.expect(!first.eql(&framed));

    var kind_builder = PhaseKeyBuilder.init(.solidity_ir, compiler);
    kind_builder.addSource(source);
    kind_builder.addContract(contract);
    kind_builder.addInputBytes("ab");
    kind_builder.addInputBytes("c");
    const other_kind = kind_builder.finish();
    try std.testing.expect(!first.eql(&other_kind));

    var compiler_builder = PhaseKeyBuilder.init(
        .optimized_yul,
        CompilerFingerprint.init("compiler-b"),
    );
    compiler_builder.addSource(source);
    compiler_builder.addContract(contract);
    compiler_builder.addInputBytes("ab");
    compiler_builder.addInputBytes("c");
    const other_compiler = compiler_builder.finish();
    try std.testing.expect(!first.eql(&other_compiler));
}

test "only identified compiler fingerprints permit persistent reuse" {
    try std.testing.expect(CompilerFingerprint.init("known-build").isPersistentSafe());
    try std.testing.expect(!CompilerFingerprint.unidentified().isPersistentSafe());
}

test "option fingerprints invalidate only their phase group" {
    var first = CompilationOptions.init(std.testing.allocator);
    defer first.deinit();
    try first.addOutput("B.sol", "B", "abi");
    try first.addOutput("A.sol", "A", "evm.bytecode");

    var reordered = CompilationOptions.init(std.testing.allocator);
    defer reordered.deinit();
    try reordered.addOutput("A.sol", "A", "evm.bytecode");
    try reordered.addOutput("B.sol", "B", "abi");

    const first_fingerprints = try PhaseFingerprints.initAlloc(std.testing.allocator, &first);
    const reordered_fingerprints = try PhaseFingerprints.initAlloc(std.testing.allocator, &reordered);
    try std.testing.expect(first_fingerprints.projection.eql(&reordered_fingerprints.projection));

    reordered.metadata.append_cbor = false;
    const metadata_changed = try PhaseFingerprints.initAlloc(std.testing.allocator, &reordered);
    try std.testing.expect(!first_fingerprints.metadata.eql(&metadata_changed.metadata));
    try std.testing.expect(first_fingerprints.frontend.eql(&metadata_changed.frontend));
    try std.testing.expect(first_fingerprints.ir.eql(&metadata_changed.ir));
    try std.testing.expect(first_fingerprints.optimizer.eql(&metadata_changed.optimizer));
    try std.testing.expect(first_fingerprints.link.eql(&metadata_changed.link));
    try std.testing.expect(first_fingerprints.projection.eql(&metadata_changed.projection));

    reordered.optimizer.settings.expected_executions_per_deployment += 1;
    const optimizer_changed = try PhaseFingerprints.initAlloc(std.testing.allocator, &reordered);
    try std.testing.expect(!metadata_changed.optimizer.eql(&optimizer_changed.optimizer));
    try std.testing.expect(metadata_changed.metadata.eql(&optimizer_changed.metadata));

    reordered.optimizer.settings.run_yul_optimiser = true;
    const yul_optimizer_changed = try PhaseFingerprints.initAlloc(
        std.testing.allocator,
        &reordered,
    );
    try std.testing.expect(
        !optimizer_changed.frontend.eql(&yul_optimizer_changed.frontend),
    );
    try std.testing.expect(
        !optimizer_changed.optimizer.eql(&yul_optimizer_changed.optimizer),
    );
}
