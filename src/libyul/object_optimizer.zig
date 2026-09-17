// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Recursive Yul optimization with sharded, portable, persistent caching.

const std = @import("std");
const AST = @import("ast.zig");
const AsmAnalysis = @import("asm_analysis.zig");
const AsmParser = @import("asm_parser.zig");
const AsmPrinter = @import("asm_printer.zig").AsmPrinter;
const DebugInfoSelection = @import("../liblangutil/debug_info_selection.zig").DebugInfoSelection;
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const EVMDialectModule = @import("backends/evm/evm_dialect.zig");
const EVMMetrics = @import("backends/evm/evm_metrics.zig");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const FixedHash = @import("../libsolutil/fixed_hash.zig");
const Keccak = @import("../libsolutil/keccak256.zig");
const Profiler = @import("../libsolutil/profiler.zig").Profiler;
const SynchronizedAllocator = @import("../libsolutil/synchronized_allocator.zig").SynchronizedAllocator;
const ArtifactStoreModule = @import("../incremental/artifact_store.zig");
const PhaseKey = @import("../incremental/phase_key.zig");
const ObjectModule = @import("object.zig");
const OptimiserSuite = @import("optimiser/suite.zig").OptimiserSuite;

pub const Settings = struct {
    evm_version: EVMVersion,
    optimize_stack_allocation: bool,
    yul_optimiser_steps: []const u8,
    yul_optimiser_cleanup_steps: []const u8,
    expected_executions_per_deployment: u64,
    profiler: ?*Profiler = null,
};

const CacheKey = FixedHash.H256;
const shard_count = 64;
const not_ready_size = std.math.maxInt(u64);

pub const default_memory_limits: ArtifactStoreModule.CacheLimits = .{
    .max_entries = 16 * 1024,
    .max_bytes = 512 * 1024 * 1024,
};

pub const Statistics = struct {
    memory_hits: u64,
    memory_misses: u64,
    persistent_hits: u64,
    persistent_misses: u64,
    persistent_failures: u64,
    optimization_runs: u64,
    single_flight_waits: u64,
    entries: u64,
    resident_bytes: u64,
    evictions: u64,
    bytes_evicted: u64,
    admission_rejections: u64,
};

const CacheKeyContext = struct {
    pub fn hash(_: CacheKeyContext, key: CacheKey) u64 {
        return std.hash.Wyhash.hash(0, key.bytes());
    }

    pub fn eql(_: CacheKeyContext, left: CacheKey, right: CacheKey) bool {
        return left.eql(&right);
    }
};

const EntryState = union(enum) {
    loading,
    ready: []u8,
    failed: anyerror,
};

const CacheEntry = struct {
    /// The first producer holds this gate while loading or optimizing. A
    /// duplicate producer waits here, never while holding a shard lock.
    gate: std.Io.Mutex = .init,
    state: EntryState = .loading,
    /// One reference belongs to the shard map. Every producer, reader, or
    /// waiter retains another reference before releasing the shard lock.
    reference_count: std.atomic.Value(usize) = .init(1),
    retired: std.atomic.Value(bool) = .init(false),
    last_used_epoch: std.atomic.Value(u64) = .init(0),
    ready_size: std.atomic.Value(u64) = .init(not_ready_size),

    fn deinit(self: *CacheEntry, allocator: std.mem.Allocator) void {
        switch (self.state) {
            .ready => |bytes| allocator.free(bytes),
            .loading, .failed => {},
        }
        self.* = undefined;
    }
};

const EntryMap = std.HashMapUnmanaged(
    CacheKey,
    *CacheEntry,
    CacheKeyContext,
    80,
);

const Shard = struct {
    /// Protects only `entries`. Per-key gates protect entry state; no parsing,
    /// optimization, callback, or persistent I/O runs under this lock.
    mutex: std.Io.Mutex = .init,
    entries: EntryMap = .empty,
};

const EntryLease = struct {
    cache: *ObjectOptimizer,
    entry: *CacheEntry,
    owner: bool,
    gate_locked: bool = true,

    fn unlockGate(self: *EntryLease) void {
        std.debug.assert(self.gate_locked);
        std.Io.Threaded.mutexUnlock(&self.entry.gate);
        self.gate_locked = false;
    }

    fn release(self: *EntryLease) void {
        if (self.gate_locked) self.unlockGate();
        self.cache.releaseEntryReference(self.entry);
        self.* = undefined;
    }
};

const EvictionCandidate = struct {
    key: CacheKey,
    entry: *CacheEntry,
    epoch: u64,

    fn precedes(self: EvictionCandidate, other: EvictionCandidate) bool {
        if (self.epoch != other.epoch) return self.epoch < other.epoch;
        return self.key.lessThan(&other.key);
    }
};

pub const ObjectOptimizer = struct {
    storage_allocator_state: SynchronizedAllocator,
    compiler_fingerprint: PhaseKey.CompilerFingerprint,
    backing_store: ?ArtifactStoreModule.ArtifactStore = null,
    memory_limits: ArtifactStoreModule.CacheLimits,
    shards: [shard_count]Shard = [_]Shard{.{}} ** shard_count,
    eviction_mutex: std.Io.Mutex = .init,
    access_epoch: std.atomic.Value(u64) = .init(0),
    memory_hit_count: std.atomic.Value(u64) = .init(0),
    memory_miss_count: std.atomic.Value(u64) = .init(0),
    persistent_hit_count: std.atomic.Value(u64) = .init(0),
    persistent_miss_count: std.atomic.Value(u64) = .init(0),
    persistent_failure_count: std.atomic.Value(u64) = .init(0),
    optimization_run_count: std.atomic.Value(u64) = .init(0),
    single_flight_wait_count: std.atomic.Value(u64) = .init(0),
    entry_count: std.atomic.Value(u64) = .init(0),
    resident_byte_count: std.atomic.Value(u64) = .init(0),
    eviction_count: std.atomic.Value(u64) = .init(0),
    evicted_byte_count: std.atomic.Value(u64) = .init(0),
    admission_rejection_count: std.atomic.Value(u64) = .init(0),

    pub fn init(allocator: std.mem.Allocator) ObjectOptimizer {
        return initWithFingerprint(allocator, PhaseKey.CompilerFingerprint.current());
    }

    pub fn initWithFingerprint(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
    ) ObjectOptimizer {
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
    ) ObjectOptimizer {
        return .{
            .storage_allocator_state = SynchronizedAllocator.init(allocator),
            .compiler_fingerprint = compiler_fingerprint,
            .memory_limits = memory_limits,
        };
    }

    pub fn initWithBackingStore(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
        backing_store: ArtifactStoreModule.ArtifactStore,
    ) PhaseKey.PersistentFingerprintError!ObjectOptimizer {
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
        backing_store: ArtifactStoreModule.ArtifactStore,
        memory_limits: ArtifactStoreModule.CacheLimits,
    ) PhaseKey.PersistentFingerprintError!ObjectOptimizer {
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

    /// All concurrent `optimize` calls must finish before destruction.
    pub fn deinit(self: *ObjectOptimizer) void {
        const allocator = self.storageAllocator();
        for (&self.shards) |*shard| {
            var entries = shard.entries.valueIterator();
            while (entries.next()) |entry| {
                std.debug.assert(entry.*.reference_count.load(.monotonic) == 1);
                entry.*.deinit(allocator);
                allocator.destroy(entry.*);
            }
            shard.entries.deinit(allocator);
        }
        self.* = undefined;
    }

    pub fn size(self: *const ObjectOptimizer) usize {
        return std.math.cast(usize, self.entry_count.load(.monotonic)) orelse
            std.math.maxInt(usize);
    }

    pub fn statistics(self: *const ObjectOptimizer) Statistics {
        return .{
            .memory_hits = self.memory_hit_count.load(.monotonic),
            .memory_misses = self.memory_miss_count.load(.monotonic),
            .persistent_hits = self.persistent_hit_count.load(.monotonic),
            .persistent_misses = self.persistent_miss_count.load(.monotonic),
            .persistent_failures = self.persistent_failure_count.load(.monotonic),
            .optimization_runs = self.optimization_run_count.load(.monotonic),
            .single_flight_waits = self.single_flight_wait_count.load(.monotonic),
            .entries = self.entry_count.load(.monotonic),
            .resident_bytes = self.resident_byte_count.load(.monotonic),
            .evictions = self.eviction_count.load(.monotonic),
            .bytes_evicted = self.evicted_byte_count.load(.monotonic),
            .admission_rejections = self.admission_rejection_count.load(.monotonic),
        };
    }

    pub fn optimize(
        self: *ObjectOptimizer,
        object: *ObjectModule.Object,
        settings: Settings,
    ) !void {
        if (!object.sub_id.empty()) return error.TopLevelObjectRequired;
        try self.optimizeRecursive(object, settings, true);
    }

    fn optimizeRecursive(
        self: *ObjectOptimizer,
        object: *ObjectModule.Object,
        settings: Settings,
        is_creation: bool,
    ) anyerror!void {
        if (!object.hasCode()) return error.MissingObjectCode;
        const debug_data = if (object.debug_data) |*data| data else return error.MissingObjectDebugData;

        for (object.sub_objects.items) |*node| switch (node.*) {
            .object => |child| try self.optimizeRecursive(
                child,
                settings,
                !std.mem.endsWith(u8, child.name, "_deployed"),
            ),
            .data => {},
        };

        const dialect = try EVMDialectModule.strictAssemblyForEVMObjects(settings.evm_version);
        var meter = EVMMetrics.GasMeter.initUnsigned(
            dialect,
            is_creation,
            settings.expected_executions_per_deployment,
        );
        defer meter.deinit();
        const cache_key = try self.calculateCacheKey(
            object.code().?.root(),
            debug_data,
            settings,
            is_creation,
        );
        var lease = try self.acquireEntry(cache_key);
        if (!lease.owner) {
            // The ready state is immutable, so release the single-flight gate
            // while retaining the entry reference through parsing. Eviction
            // may remove the map reference concurrently, but cannot free the
            // payload until this lease is released.
            lease.unlockGate();
            defer lease.release();
            return switch (lease.entry.state) {
                .ready => |optimized_yul| {
                    _ = self.memory_hit_count.fetchAdd(1, .monotonic);
                    try overwriteWithOptimizedYul(object, optimized_yul, dialect.dialect());
                },
                .failed => |err| err,
                .loading => unreachable,
            };
        }

        const optimized_yul = self.populateEntry(
            cache_key,
            object,
            settings,
            is_creation,
            dialect.dialect(),
            &meter,
        ) catch |err| {
            lease.entry.state = .{ .failed = err };
            self.retireEntry(cache_key, lease.entry, false);
            lease.release();
            return err;
        };
        lease.entry.state = .{ .ready = optimized_yul };
        _ = self.resident_byte_count.fetchAdd(optimized_yul.len, .monotonic);
        lease.entry.ready_size.store(@intCast(optimized_yul.len), .release);
        if (self.memory_limits.max_bytes == 0 or
            optimized_yul.len > self.memory_limits.max_bytes or
            self.memory_limits.max_entries == 0)
        {
            _ = self.admission_rejection_count.fetchAdd(1, .monotonic);
            self.retireEntry(cache_key, lease.entry, false);
        }
        lease.release();
        self.evictToLimits();
    }

    fn populateEntry(
        self: *ObjectOptimizer,
        cache_key: CacheKey,
        object: *ObjectModule.Object,
        settings: Settings,
        is_creation: bool,
        dialect: AST.Dialect,
        meter: *EVMMetrics.GasMeter,
    ) anyerror![]u8 {
        const reference = self.artifactReference(cache_key);
        const allocator = self.storageAllocator();
        if (self.backing_store) |backing_store| {
            var persisted = backing_store.getAlloc(allocator, reference) catch blk: {
                _ = self.persistent_failure_count.fetchAdd(1, .monotonic);
                break :blk null;
            };
            if (persisted) |*artifact| {
                if (artifact.dependencies.len == 0 and
                    std.unicode.utf8ValidateSlice(artifact.payload))
                {
                    overwriteWithOptimizedYul(
                        object,
                        artifact.payload,
                        dialect,
                    ) catch |err| switch (err) {
                        error.OutOfMemory => {
                            artifact.deinit();
                            return error.OutOfMemory;
                        },
                        else => {
                            _ = self.persistent_failure_count.fetchAdd(1, .monotonic);
                            artifact.deinit();
                            persisted = null;
                        },
                    };
                    if (persisted != null) {
                        _ = self.persistent_hit_count.fetchAdd(1, .monotonic);
                        return artifact.takePayload();
                    }
                } else {
                    _ = self.persistent_failure_count.fetchAdd(1, .monotonic);
                    artifact.deinit();
                }
            } else {
                _ = self.persistent_miss_count.fetchAdd(1, .monotonic);
            }
        }

        _ = self.optimization_run_count.fetchAdd(1, .monotonic);
        try OptimiserSuite.runProfiled(
            meter,
            object,
            settings.optimize_stack_allocation,
            settings.yul_optimiser_steps,
            settings.yul_optimiser_cleanup_steps,
            if (is_creation) null else settings.expected_executions_per_deployment,
            null,
            settings.profiler,
        );
        const optimized_yul = try renderOptimizedYulAlloc(allocator, object, dialect);
        errdefer allocator.free(optimized_yul);
        if (self.backing_store) |backing_store|
            backing_store.put(reference, optimized_yul, &.{}) catch {
                _ = self.persistent_failure_count.fetchAdd(1, .monotonic);
            };
        return optimized_yul;
    }

    fn acquireEntry(
        self: *ObjectOptimizer,
        cache_key: CacheKey,
    ) std.mem.Allocator.Error!EntryLease {
        const shard = &self.shards[shardIndex(cache_key)];
        std.Io.Threaded.mutexLock(&shard.mutex);
        const existing = shard.entries.get(cache_key);
        if (existing) |entry| {
            _ = entry.reference_count.fetchAdd(1, .monotonic);
            std.Io.Threaded.mutexUnlock(&shard.mutex);
            return self.acquireExisting(entry);
        }
        std.Io.Threaded.mutexUnlock(&shard.mutex);

        _ = self.memory_miss_count.fetchAdd(1, .monotonic);
        const allocator = self.storageAllocator();
        const candidate = try allocator.create(CacheEntry);
        candidate.* = .{};
        candidate.reference_count.store(2, .monotonic);
        candidate.last_used_epoch.store(self.nextAccessEpoch(), .monotonic);
        std.Io.Threaded.mutexLock(&candidate.gate);
        errdefer {
            std.Io.Threaded.mutexUnlock(&candidate.gate);
            allocator.destroy(candidate);
        }

        const race_winner = winner: {
            std.Io.Threaded.mutexLock(&shard.mutex);
            defer std.Io.Threaded.mutexUnlock(&shard.mutex);
            const result = try shard.entries.getOrPut(allocator, cache_key);
            if (result.found_existing) {
                _ = result.value_ptr.*.reference_count.fetchAdd(1, .monotonic);
                break :winner result.value_ptr.*;
            }
            result.value_ptr.* = candidate;
            _ = self.entry_count.fetchAdd(1, .monotonic);
            return .{ .cache = self, .entry = candidate, .owner = true };
        };

        std.Io.Threaded.mutexUnlock(&candidate.gate);
        allocator.destroy(candidate);
        return self.acquireExisting(race_winner);
    }

    fn acquireExisting(self: *ObjectOptimizer, entry: *CacheEntry) EntryLease {
        if (!entry.gate.tryLock()) {
            _ = self.single_flight_wait_count.fetchAdd(1, .monotonic);
            std.Io.Threaded.mutexLock(&entry.gate);
        }
        entry.last_used_epoch.store(self.nextAccessEpoch(), .monotonic);
        return .{ .cache = self, .entry = entry, .owner = false };
    }

    fn nextAccessEpoch(self: *ObjectOptimizer) u64 {
        return self.access_epoch.fetchAdd(1, .monotonic) +% 1;
    }

    fn releaseEntryReference(self: *ObjectOptimizer, entry: *CacheEntry) void {
        const previous = entry.reference_count.fetchSub(1, .acq_rel);
        std.debug.assert(previous != 0);
        if (previous != 1) return;
        std.debug.assert(entry.retired.load(.acquire));
        const allocator = self.storageAllocator();
        entry.deinit(allocator);
        allocator.destroy(entry);
    }

    fn retireEntry(
        self: *ObjectOptimizer,
        cache_key: CacheKey,
        expected: *CacheEntry,
        count_eviction: bool,
    ) void {
        const shard = &self.shards[shardIndex(cache_key)];
        var retired = false;
        var ready_size: u64 = not_ready_size;
        std.Io.Threaded.mutexLock(&shard.mutex);
        if (shard.entries.get(cache_key)) |current| {
            if (current == expected) {
                const removed = shard.entries.fetchRemove(cache_key).?;
                std.debug.assert(removed.value == expected);
                ready_size = expected.ready_size.load(.acquire);
                expected.retired.store(true, .release);
                _ = self.entry_count.fetchSub(1, .monotonic);
                if (ready_size != not_ready_size)
                    _ = self.resident_byte_count.fetchSub(ready_size, .monotonic);
                retired = true;
            }
        }
        std.Io.Threaded.mutexUnlock(&shard.mutex);
        if (!retired) return;
        if (count_eviction) {
            _ = self.eviction_count.fetchAdd(1, .monotonic);
            if (ready_size != not_ready_size)
                _ = self.evicted_byte_count.fetchAdd(ready_size, .monotonic);
        }
        self.releaseEntryReference(expected);
    }

    fn evictToLimits(self: *ObjectOptimizer) void {
        if (self.entry_count.load(.monotonic) <= self.memory_limits.max_entries and
            self.resident_byte_count.load(.monotonic) <= self.memory_limits.max_bytes)
        {
            return;
        }
        std.Io.Threaded.mutexLock(&self.eviction_mutex);
        defer std.Io.Threaded.mutexUnlock(&self.eviction_mutex);
        while (self.entry_count.load(.monotonic) > self.memory_limits.max_entries or
            self.resident_byte_count.load(.monotonic) > self.memory_limits.max_bytes)
        {
            const candidate = self.selectEvictionCandidate() orelse break;
            self.retireEntry(candidate.key, candidate.entry, true);
            self.releaseEntryReference(candidate.entry);
        }
    }

    /// Retains the exact ready entry selected while its shard map reference is
    /// stable. The caller must release the returned reference. A key may be
    /// removed and reused after its shard is unlocked, so the pointer is part
    /// of the eviction identity.
    fn selectEvictionCandidate(self: *ObjectOptimizer) ?EvictionCandidate {
        var oldest: ?EvictionCandidate = null;
        for (&self.shards) |*shard| {
            var shard_oldest: ?EvictionCandidate = null;
            std.Io.Threaded.mutexLock(&shard.mutex);
            var iterator = shard.entries.iterator();
            while (iterator.next()) |item| {
                const entry = item.value_ptr.*;
                if (entry.ready_size.load(.acquire) == not_ready_size) continue;
                const candidate: EvictionCandidate = .{
                    .key = item.key_ptr.*,
                    .entry = entry,
                    .epoch = entry.last_used_epoch.load(.monotonic),
                };
                if (shard_oldest == null or candidate.precedes(shard_oldest.?))
                    shard_oldest = candidate;
            }
            if (shard_oldest) |candidate|
                _ = candidate.entry.reference_count.fetchAdd(1, .monotonic);
            std.Io.Threaded.mutexUnlock(&shard.mutex);

            const candidate = shard_oldest orelse continue;
            if (oldest == null or candidate.precedes(oldest.?)) {
                if (oldest) |previous| self.releaseEntryReference(previous.entry);
                oldest = candidate;
            } else {
                self.releaseEntryReference(candidate.entry);
            }
        }
        return oldest;
    }

    fn artifactReference(
        self: *const ObjectOptimizer,
        cache_key: CacheKey,
    ) ArtifactStoreModule.ArtifactRef {
        var builder = PhaseKey.PhaseKeyBuilder.init(
            .optimized_yul,
            self.compiler_fingerprint,
        );
        builder.addInputDigest(cache_key);
        return .{ .kind = .optimized_yul, .key = builder.finish() };
    }

    fn storageAllocator(self: *ObjectOptimizer) std.mem.Allocator {
        return self.storage_allocator_state.allocator();
    }

    pub fn calculateCacheKey(
        self: *ObjectOptimizer,
        ast: *const AST.Block,
        debug_data: *const ObjectModule.ObjectDebugData,
        settings: Settings,
        is_creation: bool,
    ) !CacheKey {
        const dialect = try EVMDialectModule.strictAssemblyForEVMObjects(settings.evm_version);
        const source_names = if (debug_data.source_names) |*names|
            try names.printerEntriesAlloc(self.storageAllocator())
        else
            try self.storageAllocator().alloc(@import("asm_printer.zig").SourceIndexName, 0);
        defer self.storageAllocator().free(source_names);
        var printer = AsmPrinter.init(
            self.storageAllocator(),
            dialect.dialect(),
            source_names,
            DebugInfoSelection.allValue(true),
            null,
        );
        const rendered_ast = try printer.renderBlock(ast);
        defer self.storageAllocator().free(rendered_ast);
        const use_src_comment = try debug_data.formatUseSrcCommentAlloc(self.storageAllocator());
        defer self.storageAllocator().free(use_src_comment);

        var raw_key: [194]u8 = undefined;
        var cursor: usize = 0;
        appendHash(&raw_key, &cursor, Keccak.keccak256(rendered_ast));
        appendHash(&raw_key, &cursor, Keccak.keccak256(use_src_comment));
        raw_key[cursor] = @intFromBool(settings.optimize_stack_allocation);
        cursor += 1;
        var execution_count: [32]u8 = undefined;
        std.mem.writeInt(
            u256,
            &execution_count,
            settings.expected_executions_per_deployment,
            .big,
        );
        @memcpy(raw_key[cursor..][0..execution_count.len], &execution_count);
        cursor += execution_count.len;
        raw_key[cursor] = @intFromBool(is_creation);
        cursor += 1;
        appendHash(&raw_key, &cursor, Keccak.keccak256(settings.evm_version.name()));
        appendHash(&raw_key, &cursor, Keccak.keccak256(settings.yul_optimiser_steps));
        appendHash(&raw_key, &cursor, Keccak.keccak256(settings.yul_optimiser_cleanup_steps));
        std.debug.assert(cursor == raw_key.len);
        return Keccak.keccak256(&raw_key);
    }
};

fn shardIndex(cache_key: CacheKey) usize {
    const prefix = std.mem.readInt(u64, cache_key.storage[0..@sizeOf(u64)], .little);
    return @intCast(prefix & (shard_count - 1));
}

fn renderOptimizedYulAlloc(
    allocator: std.mem.Allocator,
    object: *const ObjectModule.Object,
    dialect: AST.Dialect,
) ![]u8 {
    const debug_data = if (object.debug_data) |*data| data else return error.MissingObjectDebugData;
    const source_names = if (debug_data.source_names) |*names|
        try names.printerEntriesAlloc(allocator)
    else
        try allocator.alloc(@import("asm_printer.zig").SourceIndexName, 0);
    defer allocator.free(source_names);
    var printer = AsmPrinter.init(
        allocator,
        dialect,
        source_names,
        DebugInfoSelection.allValue(true),
        null,
    );
    return printer.renderBlock((object.code() orelse return error.MissingObjectCode).root());
}

fn overwriteWithOptimizedYul(
    object: *ObjectModule.Object,
    optimized_yul: []const u8,
    dialect: AST.Dialect,
) !void {
    const evm_dialect = EVMDialectModule.fromDialect(dialect) orelse
        return error.CachedEVMDialectRequired;
    const debug_data = if (object.debug_data) |*data| data else return error.MissingObjectDebugData;
    const source_names = if (debug_data.source_names) |*names|
        try names.parserEntriesAlloc(object.allocator)
    else
        null;
    defer if (source_names) |names| object.allocator.free(names);

    var reporter = Diagnostics.ErrorReporter.init(object.allocator);
    defer reporter.deinit();
    var replacement = (try AsmParser.Parser.parseSource(
        object.allocator,
        optimized_yul,
        object.name,
        &reporter,
        dialect,
        .{ .source_names = source_names },
    )) orelse return error.InvalidOptimizedYulCacheEntry;
    errdefer replacement.deinit();
    if (reporter.hasErrors()) return error.InvalidOptimizedYulCacheEntry;

    var structure = try object.summarizeStructure();
    defer structure.deinit();
    var analysis = try AsmAnalysis.analyzeStrictBlock(
        object.allocator,
        dialect,
        replacement.root(),
        &structure,
        AsmAnalysis.instructionValidatorForEVMDialect(evm_dialect),
    );
    errdefer analysis.deinit();
    object.replaceCode(replacement, analysis);
}

fn appendHash(output: *[194]u8, cursor: *usize, hash: CacheKey) void {
    @memcpy(output[cursor.*..][0..hash.storage.len], &hash.storage);
    cursor.* += hash.storage.len;
}

test "object optimizer reuses portable optimized Yul and rebuilds analysis" {
    const Parser = @import("asm_parser.zig").Parser;

    const Helper = struct {
        fn makeObject(
            allocator: std.mem.Allocator,
            dialect: *const EVMDialectModule.EVMDialect,
        ) !*ObjectModule.Object {
            var reporter = Diagnostics.ErrorReporter.init(allocator);
            defer reporter.deinit();
            const parsed = (try Parser.parseSource(
                allocator,
                "{ mstore(0x40, memoryguard(0x80)) let x := add(1, 2) pop(x) }",
                "cache.yul",
                &reporter,
                dialect.dialect(),
                .{},
            )).?;
            const object = try ObjectModule.Object.create(allocator, "");
            errdefer object.destroy();
            object.debug_data = .{};
            object.setCode(parsed, null);
            var structure = try object.summarizeStructure();
            defer structure.deinit();
            object.analysis_info = try AsmAnalysis.analyzeStrictBlock(
                allocator,
                dialect.dialect(),
                object.code().?.root(),
                &structure,
                AsmAnalysis.instructionValidatorForEVMDialect(dialect),
            );
            return object;
        }
    };

    const allocator = std.testing.allocator;
    const evm_version = EVMVersion.current();
    const dialect = try EVMDialectModule.strictAssemblyForEVMObjects(evm_version);
    const first = try Helper.makeObject(allocator, dialect);
    defer first.destroy();
    const second = try Helper.makeObject(allocator, dialect);
    defer second.destroy();
    const settings: Settings = .{
        .evm_version = evm_version,
        .optimize_stack_allocation = false,
        .yul_optimiser_steps = "u",
        .yul_optimiser_cleanup_steps = "",
        .expected_executions_per_deployment = 200,
    };
    var optimizer = ObjectOptimizer.init(allocator);
    defer optimizer.deinit();
    try optimizer.optimize(first, settings);
    try std.testing.expectEqual(@as(usize, 1), optimizer.size());
    try optimizer.optimize(second, settings);
    try std.testing.expectEqual(@as(usize, 1), optimizer.size());
    try std.testing.expect(second.analysis_info != null);
    const statistics = optimizer.statistics();
    try std.testing.expectEqual(@as(u64, 1), statistics.memory_hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory_misses);
    try std.testing.expectEqual(@as(u64, 1), statistics.optimization_runs);
    try std.testing.expect(statistics.resident_bytes != 0);
    var first_printer = AsmPrinter.init(allocator, first.dialect().?.*, &.{}, .{}, null);
    const first_text = try first_printer.renderBlock(first.code().?.root());
    defer allocator.free(first_text);
    var second_printer = AsmPrinter.init(allocator, second.dialect().?.*, &.{}, .{}, null);
    const second_text = try second_printer.renderBlock(second.code().?.root());
    defer allocator.free(second_text);
    try std.testing.expectEqualStrings(first_text, second_text);

    const rejected = try Helper.makeObject(allocator, dialect);
    defer rejected.destroy();
    var disabled_cache = ObjectOptimizer.initWithFingerprintAndLimits(
        allocator,
        PhaseKey.CompilerFingerprint.init("optimizer-admission-test"),
        .{ .max_entries = 0, .max_bytes = 0 },
    );
    defer disabled_cache.deinit();
    try disabled_cache.optimize(rejected, settings);
    const rejected_statistics = disabled_cache.statistics();
    try std.testing.expectEqual(@as(u64, 0), rejected_statistics.entries);
    try std.testing.expectEqual(@as(u64, 0), rejected_statistics.resident_bytes);
    try std.testing.expectEqual(@as(u64, 0), rejected_statistics.evictions);
    try std.testing.expectEqual(@as(u64, 0), rejected_statistics.bytes_evicted);
    try std.testing.expectEqual(@as(u64, 1), rejected_statistics.admission_rejections);
}

test "object optimizer single-flight gate suppresses a duplicate producer" {
    const Waiter = struct {
        optimizer: *ObjectOptimizer,
        key: CacheKey,
        acquired_ready: std.atomic.Value(bool) = .init(false),
        failed: std.atomic.Value(bool) = .init(false),

        fn run(self: *@This()) void {
            var lease = self.optimizer.acquireEntry(self.key) catch {
                self.failed.store(true, .release);
                return;
            };
            defer lease.release();
            switch (lease.entry.state) {
                .ready => |payload| self.acquired_ready.store(
                    std.mem.eql(u8, payload, "optimized"),
                    .release,
                ),
                .loading, .failed => self.failed.store(true, .release),
            }
        }
    };

    var optimizer = ObjectOptimizer.initWithFingerprint(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("single-flight-test"),
    );
    defer optimizer.deinit();
    const key = Keccak.keccak256("same optimizer input");
    var owner = try optimizer.acquireEntry(key);
    try std.testing.expect(owner.owner);
    const payload = try optimizer.storageAllocator().dupe(u8, "optimized");

    var threaded = std.Io.Threaded.init(std.testing.allocator, .{
        .async_limit = .limited(1),
    });
    defer threaded.deinit();
    const io = threaded.io();
    var waiter: Waiter = .{ .optimizer = &optimizer, .key = key };
    var group: std.Io.Group = .init;
    group.async(io, Waiter.run, .{&waiter});
    while (optimizer.single_flight_wait_count.load(.acquire) == 0)
        std.atomic.spinLoopHint();

    owner.entry.state = .{ .ready = payload };
    _ = optimizer.resident_byte_count.fetchAdd(payload.len, .monotonic);
    owner.entry.ready_size.store(@intCast(payload.len), .release);
    owner.release();
    try group.await(io);
    try std.testing.expect(!waiter.failed.load(.acquire));
    try std.testing.expect(waiter.acquired_ready.load(.acquire));
    try std.testing.expectEqual(@as(u64, 1), optimizer.statistics().single_flight_waits);
}

test "object optimizer evicts least recently used ready entries" {
    const Helper = struct {
        fn insertReady(
            optimizer: *ObjectOptimizer,
            key: CacheKey,
            payload: []const u8,
            epoch: u64,
        ) !void {
            const allocator = optimizer.storageAllocator();
            const entry = try allocator.create(CacheEntry);
            errdefer allocator.destroy(entry);
            const owned = try allocator.dupe(u8, payload);
            errdefer allocator.free(owned);
            entry.* = .{ .state = .{ .ready = owned } };
            entry.ready_size.store(@intCast(owned.len), .monotonic);
            entry.last_used_epoch.store(epoch, .monotonic);
            const shard = &optimizer.shards[shardIndex(key)];
            std.Io.Threaded.mutexLock(&shard.mutex);
            defer std.Io.Threaded.mutexUnlock(&shard.mutex);
            try shard.entries.put(allocator, key, entry);
            _ = optimizer.entry_count.fetchAdd(1, .monotonic);
            _ = optimizer.resident_byte_count.fetchAdd(owned.len, .monotonic);
        }

        fn contains(optimizer: *ObjectOptimizer, key: CacheKey) bool {
            const shard = &optimizer.shards[shardIndex(key)];
            std.Io.Threaded.mutexLock(&shard.mutex);
            defer std.Io.Threaded.mutexUnlock(&shard.mutex);
            return shard.entries.contains(key);
        }
    };

    var optimizer = ObjectOptimizer.initWithFingerprintAndLimits(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("optimizer-lru-test"),
        .{ .max_entries = 2, .max_bytes = 6 },
    );
    defer optimizer.deinit();
    const first = Keccak.keccak256("first");
    const second = Keccak.keccak256("second");
    const third = Keccak.keccak256("third");
    try Helper.insertReady(&optimizer, first, "aaa", 3);
    try Helper.insertReady(&optimizer, second, "bbb", 2);
    try Helper.insertReady(&optimizer, third, "ccc", 4);
    optimizer.evictToLimits();

    try std.testing.expect(Helper.contains(&optimizer, first));
    try std.testing.expect(!Helper.contains(&optimizer, second));
    try std.testing.expect(Helper.contains(&optimizer, third));
    const statistics = optimizer.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.entries);
    try std.testing.expectEqual(@as(u64, 6), statistics.resident_bytes);
    try std.testing.expectEqual(@as(u64, 1), statistics.evictions);
    try std.testing.expectEqual(@as(u64, 3), statistics.bytes_evicted);
}

test "object optimizer eviction cannot retire a replacement entry" {
    const Worker = struct {
        optimizer: *ObjectOptimizer,

        fn run(self: *@This()) void {
            self.optimizer.evictToLimits();
        }
    };
    const Helper = struct {
        fn insertReady(
            optimizer: *ObjectOptimizer,
            key: CacheKey,
            payload: []const u8,
        ) !*CacheEntry {
            const allocator = optimizer.storageAllocator();
            const entry = try allocator.create(CacheEntry);
            errdefer allocator.destroy(entry);
            const owned = try allocator.dupe(u8, payload);
            errdefer allocator.free(owned);
            entry.* = .{ .state = .{ .ready = owned } };
            entry.ready_size.store(@intCast(owned.len), .monotonic);
            const shard = &optimizer.shards[shardIndex(key)];
            std.Io.Threaded.mutexLock(&shard.mutex);
            defer std.Io.Threaded.mutexUnlock(&shard.mutex);
            try shard.entries.put(allocator, key, entry);
            _ = optimizer.entry_count.fetchAdd(1, .monotonic);
            _ = optimizer.resident_byte_count.fetchAdd(owned.len, .monotonic);
            return entry;
        }

        fn mappedEntry(optimizer: *ObjectOptimizer, key: CacheKey) ?*CacheEntry {
            const shard = &optimizer.shards[shardIndex(key)];
            std.Io.Threaded.mutexLock(&shard.mutex);
            defer std.Io.Threaded.mutexUnlock(&shard.mutex);
            return shard.entries.get(key);
        }
    };

    var optimizer = ObjectOptimizer.initWithFingerprintAndLimits(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("optimizer-replacement-race-test"),
        .{ .max_entries = 0, .max_bytes = std.math.maxInt(u64) },
    );
    defer optimizer.deinit();
    const key = CacheKey.init();
    const original = try Helper.insertReady(&optimizer, key, "old");
    const replacement_payload = try optimizer.storageAllocator().dupe(u8, "replacement");
    var replacement_payload_owned = true;
    defer if (replacement_payload_owned)
        optimizer.storageAllocator().free(replacement_payload);

    var threaded = std.Io.Threaded.init(std.testing.allocator, .{
        .async_limit = .limited(1),
    });
    defer threaded.deinit();
    const io = threaded.io();
    var group: std.Io.Group = .init;
    const final_shard = &optimizer.shards[shard_count - 1];
    std.Io.Threaded.mutexLock(&final_shard.mutex);
    var final_shard_locked = true;
    var group_pending = true;
    defer {
        if (final_shard_locked)
            std.Io.Threaded.mutexUnlock(&final_shard.mutex);
        if (group_pending) group.cancel(io);
    }
    var worker: Worker = .{ .optimizer = &optimizer };
    group.async(io, Worker.run, .{&worker});

    // The eviction worker retains the selected entry before reaching the
    // deliberately blocked final shard. Replace that key while its scan is
    // paused, reproducing the key-reuse window deterministically.
    while (original.reference_count.load(.acquire) == 1)
        std.atomic.spinLoopHint();
    optimizer.retireEntry(key, original, false);
    var replacement: ?EntryLease = try optimizer.acquireEntry(key);
    defer if (replacement) |*lease| {
        lease.entry.state = .{ .failed = error.TestUnexpectedResult };
        optimizer.retireEntry(key, lease.entry, false);
        lease.release();
    };
    try std.testing.expect(replacement.?.owner);
    try std.testing.expect(replacement.?.entry != original);

    std.Io.Threaded.mutexUnlock(&final_shard.mutex);
    final_shard_locked = false;
    try group.await(io);
    group_pending = false;

    try std.testing.expect(!replacement.?.entry.retired.load(.acquire));
    try std.testing.expect(Helper.mappedEntry(&optimizer, key) == replacement.?.entry);
    replacement.?.entry.state = .{ .ready = replacement_payload };
    replacement_payload_owned = false;
    _ = optimizer.resident_byte_count.fetchAdd(replacement_payload.len, .monotonic);
    replacement.?.entry.ready_size.store(@intCast(replacement_payload.len), .release);
    replacement.?.release();
    replacement = null;

    const statistics = optimizer.statistics();
    try std.testing.expectEqual(@as(u64, 1), statistics.entries);
    try std.testing.expectEqual(@as(u64, replacement_payload.len), statistics.resident_bytes);
    try std.testing.expectEqual(@as(u64, 0), statistics.evictions);
}
