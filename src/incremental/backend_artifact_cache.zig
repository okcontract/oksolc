// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Long-lived cache for metadata-free assembly blueprints, complete unlinked
//! machine artifacts, and separately linked bytecode.

const std = @import("std");
const Artifact = @import("backend_artifact.zig");
const ArtifactStoreModule = @import("artifact_store.zig");
const AssemblyModule = @import("../libevmasm/assembly.zig");
const KeyHasher = @import("key_hasher.zig").KeyHasher;
const H256 = @import("key_hasher.zig").H256;
const LinkerObjectModule = @import("../libevmasm/linker_object.zig");
const PhaseKey = @import("phase_key.zig");
const SynchronizedAllocator = @import("../libsolutil/synchronized_allocator.zig").SynchronizedAllocator;
const YulStackModule = @import("../libyul/yul_stack.zig");

const ArtifactRef = ArtifactStoreModule.ArtifactRef;
const ArtifactStore = ArtifactStoreModule.ArtifactStore;
const MemoryArtifactStore = ArtifactStoreModule.MemoryArtifactStore;
const shard_count = 64;

pub const default_memory_limits: ArtifactStoreModule.CacheLimits = .{
    .max_entries = 64 * 1024,
    .max_bytes = 2 * 1024 * 1024 * 1024,
};

pub const Statistics = struct {
    blueprint_hits: u64,
    blueprint_misses: u64,
    machine_hits: u64,
    machine_misses: u64,
    link_hits: u64,
    link_misses: u64,
    lowering_runs: u64,
    bytecode_assembly_runs: u64,
    memory_hits: u64,
    memory_misses: u64,
    persistent_hits: u64,
    persistent_misses: u64,
    cache_failures: u64,
    flight_entries: u64,
    memory: ArtifactStoreModule.MemoryStoreStatistics,
};

pub const AssemblyResult = struct {
    pair: YulStackModule.MachineAssemblyPair,
    blueprint_reference: ArtifactRef,
    metadata_reference: ArtifactRef,
    creation_reference: ArtifactRef,
    deployed_reference: ArtifactRef,

    pub fn deinit(self: *AssemblyResult) void {
        self.pair.deinit();
        self.* = undefined;
    }
};

const ArtifactRefContext = struct {
    pub fn hash(_: ArtifactRefContext, reference: ArtifactRef) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(&.{@intFromEnum(reference.kind)});
        hasher.update(reference.key.bytes());
        return hasher.final();
    }

    pub fn eql(_: ArtifactRefContext, left: ArtifactRef, right: ArtifactRef) bool {
        return left.eql(right);
    }
};

const FlightGate = struct {
    mutex: std.Io.Mutex = .init,
    /// Protected by the owning shard mutex. Counts active and waiting leases;
    /// the map itself does not retain an idle gate.
    lease_count: usize = 0,
};

const FlightMap = std.HashMapUnmanaged(
    ArtifactRef,
    *FlightGate,
    ArtifactRefContext,
    80,
);

const FlightShard = struct {
    /// Protects only the gate map. Artifact reads, decoding, lowering, and
    /// writes run under the per-key gate and never under this shard mutex.
    mutex: std.Io.Mutex = .init,
    gates: FlightMap = .empty,
};

const GateLease = struct {
    owner: *BackendArtifactCache,
    reference: ArtifactRef,
    gate: *FlightGate,

    fn release(self: *GateLease) void {
        std.Io.Threaded.mutexUnlock(&self.gate.mutex);
        self.owner.releaseGate(self.reference, self.gate);
        self.* = undefined;
    }
};

const References = struct {
    core: ArtifactRef,
    blueprint: ArtifactRef,
    metadata: ArtifactRef,
    creation: ArtifactRef,
    deployed: ArtifactRef,
};

pub const BackendArtifactCache = struct {
    storage_allocator_state: SynchronizedAllocator,
    compiler_fingerprint: PhaseKey.CompilerFingerprint,
    backing_store: ?ArtifactStore = null,
    memory_store: ?MemoryArtifactStore = null,
    memory_limits: ArtifactStoreModule.CacheLimits,
    memory_store_mutex: std.Io.Mutex = .init,
    flight_shards: [shard_count]FlightShard = [_]FlightShard{.{}} ** shard_count,
    blueprint_hit_count: std.atomic.Value(u64) = .init(0),
    blueprint_miss_count: std.atomic.Value(u64) = .init(0),
    machine_hit_count: std.atomic.Value(u64) = .init(0),
    machine_miss_count: std.atomic.Value(u64) = .init(0),
    link_hit_count: std.atomic.Value(u64) = .init(0),
    link_miss_count: std.atomic.Value(u64) = .init(0),
    lowering_run_count: std.atomic.Value(u64) = .init(0),
    bytecode_assembly_run_count: std.atomic.Value(u64) = .init(0),
    memory_hit_count: std.atomic.Value(u64) = .init(0),
    memory_miss_count: std.atomic.Value(u64) = .init(0),
    persistent_hit_count: std.atomic.Value(u64) = .init(0),
    persistent_miss_count: std.atomic.Value(u64) = .init(0),
    cache_failure_count: std.atomic.Value(u64) = .init(0),
    flight_entry_count: std.atomic.Value(u64) = .init(0),

    pub fn init(allocator: std.mem.Allocator) BackendArtifactCache {
        return initWithFingerprint(allocator, PhaseKey.CompilerFingerprint.current());
    }

    pub fn initWithFingerprint(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
    ) BackendArtifactCache {
        return initWithFingerprintAndLimits(
            allocator,
            compiler_fingerprint,
            default_memory_limits,
        );
    }

    pub fn initWithFingerprintAndLimits(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
        memory_limits: ArtifactStoreModule.CacheLimits,
    ) BackendArtifactCache {
        return .{
            .storage_allocator_state = SynchronizedAllocator.init(allocator),
            .compiler_fingerprint = compiler_fingerprint,
            .memory_limits = memory_limits,
        };
    }

    pub fn initWithBackingStore(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
        backing_store: ArtifactStore,
    ) PhaseKey.PersistentFingerprintError!BackendArtifactCache {
        return initWithBackingStoreAndLimits(
            allocator,
            compiler_fingerprint,
            backing_store,
            default_memory_limits,
        );
    }

    pub fn initWithBackingStoreAndLimits(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
        backing_store: ArtifactStore,
        memory_limits: ArtifactStoreModule.CacheLimits,
    ) PhaseKey.PersistentFingerprintError!BackendArtifactCache {
        if (!compiler_fingerprint.isPersistentSafe())
            return error.UnidentifiedCompilerBuild;
        var result = initWithFingerprintAndLimits(
            allocator,
            compiler_fingerprint,
            memory_limits,
        );
        result.backing_store = backing_store;
        return result;
    }

    /// All concurrent cache calls must finish before destruction.
    pub fn deinit(self: *BackendArtifactCache) void {
        if (self.memory_store) |*store| store.deinit();
        const allocator = self.storageAllocator();
        for (&self.flight_shards) |*shard| {
            var gates = shard.gates.valueIterator();
            while (gates.next()) |gate| allocator.destroy(gate.*);
            shard.gates.deinit(allocator);
        }
        self.* = undefined;
    }

    pub fn statistics(self: *BackendArtifactCache) Statistics {
        std.Io.Threaded.mutexLock(&self.memory_store_mutex);
        defer std.Io.Threaded.mutexUnlock(&self.memory_store_mutex);
        return .{
            .blueprint_hits = self.blueprint_hit_count.load(.monotonic),
            .blueprint_misses = self.blueprint_miss_count.load(.monotonic),
            .machine_hits = self.machine_hit_count.load(.monotonic),
            .machine_misses = self.machine_miss_count.load(.monotonic),
            .link_hits = self.link_hit_count.load(.monotonic),
            .link_misses = self.link_miss_count.load(.monotonic),
            .lowering_runs = self.lowering_run_count.load(.monotonic),
            .bytecode_assembly_runs = self.bytecode_assembly_run_count.load(.monotonic),
            .memory_hits = self.memory_hit_count.load(.monotonic),
            .memory_misses = self.memory_miss_count.load(.monotonic),
            .persistent_hits = self.persistent_hit_count.load(.monotonic),
            .persistent_misses = self.persistent_miss_count.load(.monotonic),
            .cache_failures = self.cache_failure_count.load(.monotonic),
            .flight_entries = self.flight_entry_count.load(.monotonic),
            .memory = if (self.memory_store) |*store|
                store.statistics()
            else
                .{},
        };
    }

    pub fn assemble(
        self: *BackendArtifactCache,
        stack: *YulStackModule.YulStack,
        deploy_name: ?[]const u8,
        via_ssa_cfg: bool,
        source_indices: []const AssemblyModule.SourceIndex,
    ) !AssemblyResult {
        const allocator = stack.artifactAllocator();
        const core_yul = try stack.printWithoutMetadata();
        defer allocator.free(core_yul);
        const object = try stack.parserResult();
        const metadata_payload = try Artifact.encodeMetadataAlloc(allocator, object);
        defer allocator.free(metadata_payload);
        const artifact_refs = self.makeReferences(
            stack,
            deploy_name,
            via_ssa_cfg,
            source_indices,
            core_yul,
            metadata_payload,
        );

        var machine_gate = try self.acquireGate(artifact_refs.creation);
        defer machine_gate.release();
        if (try self.loadMachinePair(allocator, artifact_refs, stack.evmVersion())) |pair| {
            _ = self.machine_hit_count.fetchAdd(1, .monotonic);
            return resultFor(pair, artifact_refs);
        }
        _ = self.machine_miss_count.fetchAdd(1, .monotonic);

        var assemblies = try self.loadOrLowerBlueprint(
            allocator,
            stack,
            deploy_name,
            via_ssa_cfg,
            source_indices,
            core_yul,
            artifact_refs,
        );
        defer assemblies.deinit();
        try Artifact.applyMetadata(object, assemblies.creation.get() orelse
            return error.MissingAssembly);
        _ = self.bytecode_assembly_run_count.fetchAdd(1, .monotonic);
        var pair = try stack.materializeAssemblyPair(&assemblies);
        errdefer pair.deinit();

        self.storeArtifact(artifact_refs.metadata, metadata_payload, &.{});
        self.storeMachinePair(allocator, &pair, source_indices, artifact_refs, stack.evmVersion());
        return resultFor(pair, artifact_refs);
    }

    /// Applies library addresses after the unlinked machine cache. Different
    /// address maps therefore reuse optimization, lowering, metadata, and
    /// bytecode assembly.
    pub fn link(
        self: *BackendArtifactCache,
        result: *AssemblyResult,
        libraries: []const LinkerObjectModule.LibraryAddress,
    ) !void {
        try self.linkObject(
            &result.pair.creation,
            result.creation_reference,
            .linked_creation,
            libraries,
        );
        try self.linkObject(
            &result.pair.deployed,
            result.deployed_reference,
            .linked_deployed,
            libraries,
        );
    }

    fn loadOrLowerBlueprint(
        self: *BackendArtifactCache,
        allocator: std.mem.Allocator,
        stack: *YulStackModule.YulStack,
        deploy_name: ?[]const u8,
        via_ssa_cfg: bool,
        source_indices: []const AssemblyModule.SourceIndex,
        core_yul: []const u8,
        references: References,
    ) !YulStackModule.AssemblyPair {
        var gate = try self.acquireGate(references.blueprint);
        defer gate.release();
        if (try self.loadArtifact(allocator, references.blueprint)) |cached_value| {
            var cached = cached_value;
            defer cached.deinit();
            if (hasDependency(cached.dependencies, references.core)) {
                const decoded = Artifact.decodeBlueprintAlloc(
                    allocator,
                    cached.payload,
                    stack.evmVersion(),
                ) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => null,
                };
                if (decoded) |pair| {
                    _ = self.blueprint_hit_count.fetchAdd(1, .monotonic);
                    return pair;
                }
            }
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
        }
        _ = self.blueprint_miss_count.fetchAdd(1, .monotonic);
        _ = self.lowering_run_count.fetchAdd(1, .monotonic);
        var assemblies = try stack.lowerToAssemblyWithDeployed(deploy_name, via_ssa_cfg);
        errdefer assemblies.deinit();
        try Artifact.stripMetadata(
            try stack.parserResult(),
            assemblies.creation.get() orelse return error.MissingAssembly,
        );
        const payload = Artifact.encodeBlueprintAlloc(
            allocator,
            &assemblies,
            source_indices,
            stack.evmVersion(),
        ) catch {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            return assemblies;
        };
        defer allocator.free(payload);
        self.storeArtifact(references.core, core_yul, &.{});
        self.storeArtifact(references.blueprint, payload, &.{references.core});
        return assemblies;
    }

    fn loadMachinePair(
        self: *BackendArtifactCache,
        allocator: std.mem.Allocator,
        references: References,
        evm_version: @import("../liblangutil/evm_version.zig").EVMVersion,
    ) !?YulStackModule.MachineAssemblyPair {
        var creation = (try self.loadArtifact(allocator, references.creation)) orelse
            return null;
        defer creation.deinit();
        if (!hasDependency(creation.dependencies, references.blueprint) or
            !hasDependency(creation.dependencies, references.metadata))
        {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            return null;
        }
        const has_deployed = Artifact.creationHasDeployed(
            creation.payload,
            evm_version,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => {
                _ = self.cache_failure_count.fetchAdd(1, .monotonic);
                return null;
            },
        };
        var deployed: ?ArtifactStoreModule.Artifact = null;
        defer if (deployed) |*artifact| artifact.deinit();
        if (has_deployed) {
            deployed = (try self.loadArtifact(allocator, references.deployed)) orelse
                return null;
            if (!hasDependency(deployed.?.dependencies, references.blueprint) or
                !hasDependency(deployed.?.dependencies, references.metadata))
            {
                _ = self.cache_failure_count.fetchAdd(1, .monotonic);
                return null;
            }
        }
        return Artifact.decodeMachinePairAlloc(
            allocator,
            creation.payload,
            if (deployed) |artifact| artifact.payload else null,
            evm_version,
        ) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => {
                _ = self.cache_failure_count.fetchAdd(1, .monotonic);
                return null;
            },
        };
    }

    fn storeMachinePair(
        self: *BackendArtifactCache,
        allocator: std.mem.Allocator,
        pair: *const YulStackModule.MachineAssemblyPair,
        source_indices: []const AssemblyModule.SourceIndex,
        references: References,
        evm_version: @import("../liblangutil/evm_version.zig").EVMVersion,
    ) void {
        const dependencies = [_]ArtifactRef{ references.blueprint, references.metadata };
        const creation = Artifact.encodeCreationAlloc(
            allocator,
            pair,
            source_indices,
            evm_version,
        ) catch {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            return;
        };
        defer allocator.free(creation);
        self.storeArtifact(references.creation, creation, &dependencies);
        if (pair.deployed.bytecode == null) return;
        const deployed = Artifact.encodeDeployedAlloc(
            allocator,
            &pair.deployed,
            evm_version,
        ) catch {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            return;
        };
        defer allocator.free(deployed);
        self.storeArtifact(references.deployed, deployed, &dependencies);
    }

    fn linkObject(
        self: *BackendArtifactCache,
        machine_object: *YulStackModule.MachineAssemblyObject,
        machine_reference: ArtifactRef,
        kind: PhaseKey.ArtifactKind,
        libraries: []const LinkerObjectModule.LibraryAddress,
    ) !void {
        const bytecode = if (machine_object.bytecode) |*object| object else return;
        const allocator = machine_object.allocator orelse
            return error.MissingMachineObjectAllocator;
        const settings = try linkSettingsFingerprintAlloc(
            allocator,
            bytecode.link_references.items,
            libraries,
        ) orelse return;
        var key_builder = PhaseKey.PhaseKeyBuilder.init(kind, self.compiler_fingerprint);
        key_builder.addSettings(settings);
        key_builder.addDependency(machine_reference.key);
        const reference: ArtifactRef = .{ .kind = kind, .key = key_builder.finish() };
        var gate = try self.acquireGate(reference);
        defer gate.release();

        if (try self.loadArtifact(allocator, reference)) |cached_value| {
            var cached = cached_value;
            defer cached.deinit();
            if (hasDependency(cached.dependencies, machine_reference)) {
                var decoded = Artifact.decodeLinkerObjectAlloc(
                    allocator,
                    cached.payload,
                ) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    else => null,
                };
                if (decoded) |*linked| {
                    bytecode.deinit(allocator);
                    bytecode.* = linked.take();
                    _ = self.link_hit_count.fetchAdd(1, .monotonic);
                    return;
                }
            }
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
        }
        _ = self.link_miss_count.fetchAdd(1, .monotonic);
        try bytecode.link(allocator, libraries);
        const encoded = Artifact.encodeLinkerObjectAlloc(allocator, bytecode) catch {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            return;
        };
        defer allocator.free(encoded);
        self.storeArtifact(reference, encoded, &.{machine_reference});
    }

    fn makeReferences(
        self: *BackendArtifactCache,
        stack: *const YulStackModule.YulStack,
        deploy_name: ?[]const u8,
        via_ssa_cfg: bool,
        source_indices: []const AssemblyModule.SourceIndex,
        core_yul: []const u8,
        metadata_payload: []const u8,
    ) References {
        var core_builder = PhaseKey.PhaseKeyBuilder.init(
            .optimized_yul,
            self.compiler_fingerprint,
        );
        core_builder.addInputBytes(core_yul);
        const core: ArtifactRef = .{ .kind = .optimized_yul, .key = core_builder.finish() };

        var blueprint_builder = PhaseKey.PhaseKeyBuilder.init(
            .assembly_blueprint,
            self.compiler_fingerprint,
        );
        blueprint_builder.addSettings(backendSettingsFingerprint(
            stack,
            deploy_name,
            via_ssa_cfg,
            source_indices,
        ));
        blueprint_builder.addDependency(core.key);
        const blueprint: ArtifactRef = .{
            .kind = .assembly_blueprint,
            .key = blueprint_builder.finish(),
        };

        var metadata_builder = PhaseKey.PhaseKeyBuilder.init(
            .metadata,
            self.compiler_fingerprint,
        );
        metadata_builder.addInputBytes(metadata_payload);
        const metadata: ArtifactRef = .{
            .kind = .metadata,
            .key = metadata_builder.finish(),
        };

        var creation_builder = PhaseKey.PhaseKeyBuilder.init(
            .creation_machine,
            self.compiler_fingerprint,
        );
        creation_builder.addDependency(blueprint.key);
        creation_builder.addDependency(metadata.key);
        const creation: ArtifactRef = .{
            .kind = .creation_machine,
            .key = creation_builder.finish(),
        };

        var deployed_builder = PhaseKey.PhaseKeyBuilder.init(
            .deployed_machine,
            self.compiler_fingerprint,
        );
        deployed_builder.addDependency(blueprint.key);
        deployed_builder.addDependency(metadata.key);
        const deployed: ArtifactRef = .{
            .kind = .deployed_machine,
            .key = deployed_builder.finish(),
        };
        return .{
            .core = core,
            .blueprint = blueprint,
            .metadata = metadata,
            .creation = creation,
            .deployed = deployed,
        };
    }

    fn loadArtifact(
        self: *BackendArtifactCache,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) !?ArtifactStoreModule.Artifact {
        const memory = self.memoryStore();
        const memory_value = memory.getAlloc(allocator, reference) catch blk: {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            break :blk null;
        };
        if (memory_value) |artifact| {
            _ = self.memory_hit_count.fetchAdd(1, .monotonic);
            return artifact;
        }
        _ = self.memory_miss_count.fetchAdd(1, .monotonic);
        const backing = self.backing_store orelse return null;
        const persistent_value = backing.getAlloc(allocator, reference) catch {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            return null;
        };
        if (persistent_value) |artifact| {
            _ = self.persistent_hit_count.fetchAdd(1, .monotonic);
            memory.put(reference, artifact.payload, artifact.dependencies) catch {
                _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            };
            return artifact;
        }
        _ = self.persistent_miss_count.fetchAdd(1, .monotonic);
        return null;
    }

    fn storeArtifact(
        self: *BackendArtifactCache,
        reference: ArtifactRef,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) void {
        self.memoryStore().put(reference, payload, dependencies) catch {
            _ = self.cache_failure_count.fetchAdd(1, .monotonic);
        };
        if (self.backing_store) |backing|
            backing.put(reference, payload, dependencies) catch {
                _ = self.cache_failure_count.fetchAdd(1, .monotonic);
            };
    }

    fn memoryStore(self: *BackendArtifactCache) *MemoryArtifactStore {
        std.Io.Threaded.mutexLock(&self.memory_store_mutex);
        defer std.Io.Threaded.mutexUnlock(&self.memory_store_mutex);
        if (self.memory_store == null)
            self.memory_store = MemoryArtifactStore.initWithLimits(
                self.storageAllocator(),
                self.memory_limits,
            );
        return &self.memory_store.?;
    }

    fn acquireGate(
        self: *BackendArtifactCache,
        reference: ArtifactRef,
    ) std.mem.Allocator.Error!GateLease {
        const shard = &self.flight_shards[shardIndex(reference)];
        std.Io.Threaded.mutexLock(&shard.mutex);
        const gate = gate: {
            if (shard.gates.get(reference)) |existing| {
                existing.lease_count += 1;
                break :gate existing;
            }
            const allocator = self.storageAllocator();
            const created = allocator.create(FlightGate) catch |err| {
                std.Io.Threaded.mutexUnlock(&shard.mutex);
                return err;
            };
            created.* = .{ .lease_count = 1 };
            shard.gates.put(allocator, reference, created) catch |err| {
                allocator.destroy(created);
                std.Io.Threaded.mutexUnlock(&shard.mutex);
                return err;
            };
            _ = self.flight_entry_count.fetchAdd(1, .monotonic);
            break :gate created;
        };
        std.Io.Threaded.mutexUnlock(&shard.mutex);
        std.Io.Threaded.mutexLock(&gate.mutex);
        return .{ .owner = self, .reference = reference, .gate = gate };
    }

    fn releaseGate(
        self: *BackendArtifactCache,
        reference: ArtifactRef,
        gate: *FlightGate,
    ) void {
        const shard = &self.flight_shards[shardIndex(reference)];
        var destroy = false;
        std.Io.Threaded.mutexLock(&shard.mutex);
        const current = shard.gates.get(reference).?;
        std.debug.assert(current == gate);
        std.debug.assert(gate.lease_count != 0);
        gate.lease_count -= 1;
        if (gate.lease_count == 0) {
            const removed = shard.gates.fetchRemove(reference).?;
            std.debug.assert(removed.value == gate);
            destroy = true;
            _ = self.flight_entry_count.fetchSub(1, .monotonic);
        }
        std.Io.Threaded.mutexUnlock(&shard.mutex);
        if (destroy) self.storageAllocator().destroy(gate);
    }

    fn storageAllocator(self: *BackendArtifactCache) std.mem.Allocator {
        return self.storage_allocator_state.allocator();
    }
};

fn resultFor(pair: YulStackModule.MachineAssemblyPair, references: References) AssemblyResult {
    return .{
        .pair = pair,
        .blueprint_reference = references.blueprint,
        .metadata_reference = references.metadata,
        .creation_reference = references.creation,
        .deployed_reference = references.deployed,
    };
}

fn backendSettingsFingerprint(
    stack: *const YulStackModule.YulStack,
    deploy_name: ?[]const u8,
    via_ssa_cfg: bool,
    source_indices: []const AssemblyModule.SourceIndex,
) H256 {
    const settings = stack.optimiserSettings();
    var hasher = KeyHasher.init("settings.backend-assembly", 1);
    hasher.addBytes(1, stack.evmVersion().name());
    hasher.addBool(2, via_ssa_cfg);
    hasher.addBytes(3, deploy_name orelse "");
    hasher.addBool(4, deploy_name != null);
    hasher.addBool(5, settings.optimize_stack_allocation);
    hasher.addBool(6, settings.run_yul_optimiser);
    hasher.addBool(7, settings.run_inliner);
    hasher.addBool(8, settings.run_jumpdest_remover);
    hasher.addBool(9, settings.run_peephole);
    hasher.addBool(10, settings.run_deduplicate);
    hasher.addBool(11, settings.run_cse);
    hasher.addBool(12, settings.run_constant_optimiser);
    hasher.addU64(13, settings.expected_executions_per_deployment);
    hasher.addU64(14, @intCast(source_indices.len));
    for (source_indices) |source| {
        hasher.addBytes(15, source.source_name);
        hasher.addU64(16, source.index);
    }
    return hasher.finish();
}

fn linkSettingsFingerprintAlloc(
    allocator: std.mem.Allocator,
    references: []const LinkerObjectModule.LinkReference,
    libraries: []const LinkerObjectModule.LibraryAddress,
) !?H256 {
    var relevant: std.ArrayList(LinkerObjectModule.LibraryAddress) = .empty;
    defer relevant.deinit(allocator);
    for (libraries) |library| {
        for (references) |reference| {
            if (!std.mem.eql(u8, reference.library_name, library.name)) continue;
            try relevant.append(allocator, library);
            break;
        }
    }
    if (relevant.items.len == 0) return null;
    std.mem.sort(
        LinkerObjectModule.LibraryAddress,
        relevant.items,
        {},
        libraryAddressLessThan,
    );
    for (relevant.items[1..], relevant.items[0 .. relevant.items.len - 1]) |current, previous|
        if (std.mem.eql(u8, current.name, previous.name))
            return error.DuplicateLibraryAddress;

    var hasher = KeyHasher.init("settings.backend-link", 1);
    hasher.addU64(1, @intCast(relevant.items.len));
    for (relevant.items) |library| {
        hasher.addBytes(2, library.name);
        hasher.addBytes(3, library.address.bytes());
    }
    return hasher.finish();
}

fn libraryAddressLessThan(
    _: void,
    left: LinkerObjectModule.LibraryAddress,
    right: LinkerObjectModule.LibraryAddress,
) bool {
    const name_order = std.mem.order(u8, left.name, right.name);
    if (name_order != .eq) return name_order == .lt;
    return std.mem.order(u8, left.address.bytes(), right.address.bytes()) == .lt;
}

fn hasDependency(dependencies: []const ArtifactRef, expected: ArtifactRef) bool {
    for (dependencies) |dependency|
        if (dependency.eql(expected)) return true;
    return false;
}

fn shardIndex(reference: ArtifactRef) usize {
    const prefix = std.mem.readInt(
        u64,
        reference.key.bytes()[0..@sizeOf(u64)],
        .little,
    );
    return @intCast(prefix & (shard_count - 1));
}

test "backend cache releases completed single-flight gates" {
    var cache = BackendArtifactCache.initWithFingerprint(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("backend-gate-lifetime-test"),
    );
    defer cache.deinit();
    var builder = PhaseKey.PhaseKeyBuilder.init(
        .assembly_blueprint,
        PhaseKey.CompilerFingerprint.init("backend-gate-lifetime-test"),
    );
    builder.addInputBytes("artifact");
    const reference: ArtifactRef = .{
        .kind = .assembly_blueprint,
        .key = builder.finish(),
    };

    var lease = try cache.acquireGate(reference);
    try std.testing.expectEqual(@as(u64, 1), cache.statistics().flight_entries);
    lease.release();
    try std.testing.expectEqual(@as(u64, 0), cache.statistics().flight_entries);
}

test "backend cache splits metadata, machine, linking, and projection inputs" {
    const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
    const OptimiserSettings = @import("../libsolidity/interface/optimiser_settings.zig").OptimiserSettings;

    const allocator = std.testing.allocator;
    var cache = BackendArtifactCache.initWithFingerprint(
        allocator,
        PhaseKey.CompilerFingerprint.init("backend-cache-test"),
    );
    defer cache.deinit();
    const first_source =
        \\object "A" {
        \\  code { datacopy(0, dataoffset("A_deployed"), datasize("A_deployed")) return(0, datasize("A_deployed")) }
        \\  object "A_deployed" { code { mstore(0, 1) return(0, 32) } data ".metadata" hex"aabb" }
        \\}
    ;
    const second_source =
        \\object "A" {
        \\  code { datacopy(0, dataoffset("A_deployed"), datasize("A_deployed")) return(0, datasize("A_deployed")) }
        \\  object "A_deployed" { code { mstore(0, 1) return(0, 32) } data ".metadata" hex"ccdd" }
        \\}
    ;
    const sources = [_]AssemblyModule.SourceIndex{.{ .source_name = "A.yul", .index = 0 }};

    var first_stack = try YulStackModule.YulStack.init(
        allocator,
        EVMVersion.init(.Cancun),
        OptimiserSettings.none(),
        .{},
        null,
        null,
    );
    defer first_stack.deinit();
    try std.testing.expect(try first_stack.parseAndAnalyze("A.yul", first_source));
    try first_stack.optimize();
    var first = try cache.assemble(
        &first_stack,
        "A_deployed",
        false,
        &sources,
    );
    defer first.deinit();
    try cache.link(&first, &.{});
    const first_bytes = try allocator.dupe(
        u8,
        first.pair.creation.bytecode.?.bytecode.items,
    );
    defer allocator.free(first_bytes);

    var second_stack = try YulStackModule.YulStack.init(
        allocator,
        EVMVersion.init(.Cancun),
        OptimiserSettings.none(),
        .{},
        null,
        null,
    );
    defer second_stack.deinit();
    try std.testing.expect(try second_stack.parseAndAnalyze("A.yul", second_source));
    try second_stack.optimize();
    var second = try cache.assemble(
        &second_stack,
        "A_deployed",
        false,
        &sources,
    );
    defer second.deinit();
    try cache.link(&second, &.{});
    try std.testing.expect(!std.mem.eql(
        u8,
        first_bytes,
        second.pair.creation.bytecode.?.bytecode.items,
    ));

    var third_stack = try YulStackModule.YulStack.init(
        allocator,
        EVMVersion.init(.Cancun),
        OptimiserSettings.none(),
        .{},
        null,
        null,
    );
    defer third_stack.deinit();
    try std.testing.expect(try third_stack.parseAndAnalyze("A.yul", second_source));
    try third_stack.optimize();
    var third = try cache.assemble(
        &third_stack,
        "A_deployed",
        false,
        &sources,
    );
    defer third.deinit();
    try cache.link(&third, &.{});
    try std.testing.expectEqualSlices(
        u8,
        second.pair.creation.bytecode.?.bytecode.items,
        third.pair.creation.bytecode.?.bytecode.items,
    );

    const statistics = cache.statistics();
    try std.testing.expectEqual(@as(u64, 1), statistics.lowering_runs);
    try std.testing.expectEqual(@as(u64, 1), statistics.blueprint_hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.machine_hits);
    try std.testing.expectEqual(@as(u64, 2), statistics.bytecode_assembly_runs);
    try std.testing.expectEqual(@as(u64, 0), statistics.link_hits);
    try std.testing.expectEqual(@as(u64, 0), statistics.link_misses);
}
