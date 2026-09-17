// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Artifact-store interface and ownership-safe in-memory implementation.

const std = @import("std");
const PhaseKey = @import("phase_key.zig");

pub const ArtifactKind = PhaseKey.ArtifactKind;
pub const ArtifactKey = PhaseKey.ArtifactKey;

pub const ArtifactRef = struct {
    kind: ArtifactKind,
    key: ArtifactKey,

    pub fn eql(left: ArtifactRef, right: ArtifactRef) bool {
        return left.kind == right.kind and left.key.eql(&right.key);
    }

    pub fn lessThan(_: void, left: ArtifactRef, right: ArtifactRef) bool {
        const left_kind = @intFromEnum(left.kind);
        const right_kind = @intFromEnum(right.kind);
        if (left_kind != right_kind) return left_kind < right_kind;
        return left.key.lessThan(&right.key);
    }
};

/// One allocator-owned artifact read. Persistent representations must decode
/// into this portable shape rather than exposing native-layout storage.
pub const Artifact = struct {
    allocator: std.mem.Allocator,
    payload: []u8,
    dependencies: []ArtifactRef,

    pub fn deinit(self: *Artifact) void {
        self.allocator.free(self.dependencies);
        self.allocator.free(self.payload);
        self.* = undefined;
    }

    /// Transfers the payload and releases the dependency list. The caller
    /// becomes responsible for freeing the returned bytes with `allocator`.
    pub fn takePayload(self: *Artifact) []u8 {
        const result = self.payload;
        self.allocator.free(self.dependencies);
        self.* = undefined;
        return result;
    }
};

pub const StoreError = std.mem.Allocator.Error || error{
    AuthenticationFailed,
    ArtifactTooLarge,
    Unavailable,
    Corrupt,
    IncompatibleSchema,
};

/// Logical cache limits. Byte accounting covers artifact payloads; allocator
/// and dependency-index overhead remains implementation-specific. A zero
/// limit disables retention for that dimension without making cache writes an
/// error.
pub const CacheLimits = struct {
    max_entries: u64 = std.math.maxInt(u64),
    max_bytes: u64 = std.math.maxInt(u64),

    pub const unlimited: CacheLimits = .{};
};

pub const default_memory_limits: CacheLimits = .{
    .max_entries = 16 * 1024,
    .max_bytes = 512 * 1024 * 1024,
};

/// Type-erased artifact store. Reads return independent owned copies, so an
/// implementation may safely mutate, shard, evict, or close internal state.
pub const ArtifactStore = struct {
    context: *anyopaque,
    contains_fn: *const fn (
        context: *anyopaque,
        reference: ArtifactRef,
    ) StoreError!bool,
    get_alloc_fn: *const fn (
        context: *anyopaque,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError!?Artifact,
    put_fn: *const fn (
        context: *anyopaque,
        reference: ArtifactRef,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) StoreError!void,

    /// Probes key presence without allocating or reading the artifact payload.
    /// Presence is advisory: callers must still handle a subsequent miss,
    /// replacement, corruption, or eviction from `getAlloc`.
    pub fn contains(self: ArtifactStore, reference: ArtifactRef) StoreError!bool {
        return self.contains_fn(self.context, reference);
    }

    pub fn getAlloc(
        self: ArtifactStore,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError!?Artifact {
        return self.get_alloc_fn(self.context, allocator, reference);
    }

    pub fn put(
        self: ArtifactStore,
        reference: ArtifactRef,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) StoreError!void {
        return self.put_fn(self.context, reference, payload, dependencies);
    }
};

pub const MemoryStoreStatistics = struct {
    hits: u64 = 0,
    misses: u64 = 0,
    puts: u64 = 0,
    replacements: u64 = 0,
    bytes_read: u64 = 0,
    bytes_written: u64 = 0,
    resident_bytes: u64 = 0,
    entries: u64 = 0,
    evictions: u64 = 0,
    bytes_evicted: u64 = 0,
    admission_rejections: u64 = 0,
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

const Entry = struct {
    payload: []u8,
    dependencies: []ArtifactRef,
    last_used_epoch: u64 = 0,

    fn cloneAlloc(
        allocator: std.mem.Allocator,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) std.mem.Allocator.Error!Entry {
        const owned_payload = try allocator.dupe(u8, payload);
        errdefer allocator.free(owned_payload);
        const owned_dependencies = try canonicalDependenciesAlloc(allocator, dependencies);
        return .{
            .payload = owned_payload,
            .dependencies = owned_dependencies,
        };
    }

    fn deinit(self: *Entry, allocator: std.mem.Allocator) void {
        allocator.free(self.dependencies);
        allocator.free(self.payload);
        self.* = undefined;
    }
};

const EntryMap = std.HashMapUnmanaged(
    ArtifactRef,
    Entry,
    ArtifactRefContext,
    80,
);

/// Process-local content-addressed artifact cache. All map state and counters
/// are protected by `mutex`; callers must finish concurrent operations before
/// `deinit`.
pub const MemoryArtifactStore = struct {
    allocator: std.mem.Allocator,
    entries: EntryMap = .empty,
    mutex: std.Io.Mutex = .init,
    statistics_value: MemoryStoreStatistics = .{},
    limits: CacheLimits,
    epoch: u64 = 0,

    pub fn init(allocator: std.mem.Allocator) MemoryArtifactStore {
        return initWithLimits(allocator, default_memory_limits);
    }

    pub fn initWithLimits(
        allocator: std.mem.Allocator,
        limits: CacheLimits,
    ) MemoryArtifactStore {
        return .{ .allocator = allocator, .limits = limits };
    }

    pub fn deinit(self: *MemoryArtifactStore) void {
        var iterator = self.entries.valueIterator();
        while (iterator.next()) |entry| entry.deinit(self.allocator);
        self.entries.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn artifactStore(self: *MemoryArtifactStore) ArtifactStore {
        return .{
            .context = self,
            .contains_fn = containsErased,
            .get_alloc_fn = getAllocErased,
            .put_fn = putErased,
        };
    }

    pub fn contains(self: *MemoryArtifactStore, reference: ArtifactRef) bool {
        self.lock();
        defer self.unlock();
        return self.entries.contains(reference);
    }

    pub fn getAlloc(
        self: *MemoryArtifactStore,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) std.mem.Allocator.Error!?Artifact {
        self.lock();
        const entry = self.entries.getPtr(reference) orelse {
            self.statistics_value.misses += 1;
            self.unlock();
            return null;
        };
        entry.last_used_epoch = self.nextEpoch();
        const payload = allocator.dupe(u8, entry.payload) catch |err| {
            self.unlock();
            return err;
        };
        const dependencies = allocator.dupe(ArtifactRef, entry.dependencies) catch |err| {
            allocator.free(payload);
            self.unlock();
            return err;
        };
        self.statistics_value.hits += 1;
        self.statistics_value.bytes_read += @intCast(entry.payload.len);
        self.unlock();
        return .{
            .allocator = allocator,
            .payload = payload,
            .dependencies = dependencies,
        };
    }

    pub fn put(
        self: *MemoryArtifactStore,
        reference: ArtifactRef,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) std.mem.Allocator.Error!void {
        const payload_size = std.math.cast(u64, payload.len) orelse
            std.math.maxInt(u64);
        if (self.limits.max_entries == 0 or self.limits.max_bytes == 0 or
            payload_size > self.limits.max_bytes)
        {
            self.lock();
            if (self.entries.fetchRemove(reference)) |removed| {
                var old_entry = removed.value;
                self.statistics_value.resident_bytes -= @intCast(old_entry.payload.len);
                self.statistics_value.entries = @intCast(self.entries.count());
                old_entry.deinit(self.allocator);
            }
            self.statistics_value.puts +|= 1;
            self.statistics_value.bytes_written +|= payload_size;
            self.statistics_value.admission_rejections +|= 1;
            self.unlock();
            return;
        }

        var replacement = try Entry.cloneAlloc(self.allocator, payload, dependencies);
        errdefer replacement.deinit(self.allocator);

        self.lock();
        replacement.last_used_epoch = self.nextEpoch();
        const result = self.entries.getOrPut(self.allocator, reference) catch |err| {
            self.unlock();
            return err;
        };
        var old_entry: ?Entry = null;
        if (result.found_existing) {
            old_entry = result.value_ptr.*;
            self.statistics_value.replacements += 1;
            self.statistics_value.resident_bytes -= @intCast(old_entry.?.payload.len);
        }
        result.value_ptr.* = replacement;
        replacement = undefined;
        self.statistics_value.puts +|= 1;
        self.statistics_value.bytes_written +|= payload_size;
        self.statistics_value.resident_bytes +|= payload_size;
        self.statistics_value.entries = @intCast(self.entries.count());
        self.evictToLimits();
        self.unlock();

        if (old_entry) |*entry| entry.deinit(self.allocator);
    }

    pub fn statistics(self: *MemoryArtifactStore) MemoryStoreStatistics {
        self.lock();
        defer self.unlock();
        return self.statistics_value;
    }

    fn getAllocErased(
        context: *anyopaque,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError!?Artifact {
        const self: *MemoryArtifactStore = @ptrCast(@alignCast(context));
        return self.getAlloc(allocator, reference);
    }

    fn containsErased(
        context: *anyopaque,
        reference: ArtifactRef,
    ) StoreError!bool {
        const self: *MemoryArtifactStore = @ptrCast(@alignCast(context));
        return self.contains(reference);
    }

    fn putErased(
        context: *anyopaque,
        reference: ArtifactRef,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) StoreError!void {
        const self: *MemoryArtifactStore = @ptrCast(@alignCast(context));
        return self.put(reference, payload, dependencies);
    }

    fn lock(self: *MemoryArtifactStore) void {
        std.Io.Threaded.mutexLock(&self.mutex);
    }

    fn unlock(self: *MemoryArtifactStore) void {
        std.Io.Threaded.mutexUnlock(&self.mutex);
    }

    /// Requires `mutex`. Saturation preserves a deterministic total ordering
    /// until the process has performed 2^64 cache accesses.
    fn nextEpoch(self: *MemoryArtifactStore) u64 {
        self.epoch +|= 1;
        return self.epoch;
    }

    /// Requires `mutex`. One insertion normally evicts only one old entry; the
    /// scan-based policy deliberately favors simple, bounded metadata over a
    /// second heap or linked-list allocation per artifact.
    fn evictToLimits(self: *MemoryArtifactStore) void {
        while (self.statistics_value.entries > self.limits.max_entries or
            self.statistics_value.resident_bytes > self.limits.max_bytes)
        {
            var oldest_reference: ?ArtifactRef = null;
            var oldest_epoch: u64 = std.math.maxInt(u64);
            var iterator = self.entries.iterator();
            while (iterator.next()) |item| {
                const entry_epoch = item.value_ptr.last_used_epoch;
                if (entry_epoch > oldest_epoch) continue;
                if (entry_epoch == oldest_epoch and oldest_reference != null and
                    !ArtifactRef.lessThan({}, item.key_ptr.*, oldest_reference.?))
                {
                    continue;
                }
                oldest_epoch = entry_epoch;
                oldest_reference = item.key_ptr.*;
            }
            const reference = oldest_reference orelse break;
            const removed = self.entries.fetchRemove(reference) orelse continue;
            var entry = removed.value;
            const size: u64 = @intCast(entry.payload.len);
            self.statistics_value.resident_bytes -= size;
            self.statistics_value.entries = @intCast(self.entries.count());
            self.statistics_value.evictions +|= 1;
            self.statistics_value.bytes_evicted +|= size;
            entry.deinit(self.allocator);
        }
    }
};

fn canonicalDependenciesAlloc(
    allocator: std.mem.Allocator,
    dependencies: []const ArtifactRef,
) std.mem.Allocator.Error![]ArtifactRef {
    const sorted = try allocator.dupe(ArtifactRef, dependencies);
    errdefer allocator.free(sorted);
    std.mem.sort(ArtifactRef, sorted, {}, ArtifactRef.lessThan);
    if (sorted.len < 2) return sorted;

    var unique_count: usize = 1;
    for (sorted[1..]) |dependency| {
        if (sorted[unique_count - 1].eql(dependency)) continue;
        sorted[unique_count] = dependency;
        unique_count += 1;
    }
    if (unique_count == sorted.len) return sorted;
    const canonical = try allocator.dupe(ArtifactRef, sorted[0..unique_count]);
    allocator.free(sorted);
    return canonical;
}

test "memory artifact store owns payloads and canonical dependency keys" {
    var store = MemoryArtifactStore.init(std.testing.allocator);
    defer store.deinit();

    const compiler = PhaseKey.CompilerFingerprint.init("store-test");
    var key_builder = PhaseKey.PhaseKeyBuilder.init(.optimized_yul, compiler);
    key_builder.addInputBytes("primary");
    const reference: ArtifactRef = .{
        .kind = .optimized_yul,
        .key = key_builder.finish(),
    };
    var dependency_builder = PhaseKey.PhaseKeyBuilder.init(.solidity_ir, compiler);
    dependency_builder.addInputBytes("dependency");
    const dependency: ArtifactRef = .{
        .kind = .solidity_ir,
        .key = dependency_builder.finish(),
    };

    try std.testing.expect(!store.contains(reference));
    var payload = [_]u8{ 'y', 'u', 'l' };
    var dependencies = [_]ArtifactRef{ dependency, dependency };
    try store.put(reference, &payload, &dependencies);
    try std.testing.expect(try store.artifactStore().contains(reference));
    @memset(&payload, 'x');
    dependencies[0] = reference;

    var artifact = (try store.getAlloc(std.testing.allocator, reference)).?;
    defer artifact.deinit();
    try std.testing.expectEqualStrings("yul", artifact.payload);
    try std.testing.expectEqual(@as(usize, 1), artifact.dependencies.len);
    try std.testing.expect(artifact.dependencies[0].eql(dependency));

    artifact.payload[0] = 'X';
    var second_read = (try store.artifactStore().getAlloc(
        std.testing.allocator,
        reference,
    )).?;
    defer second_read.deinit();
    try std.testing.expectEqualStrings("yul", second_read.payload);

    const statistics = store.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.puts);
    try std.testing.expectEqual(@as(u64, 3), statistics.resident_bytes);
    try std.testing.expectEqual(@as(u64, 1), statistics.entries);
}

test "memory artifact store atomically replaces an existing entry" {
    var store = MemoryArtifactStore.init(std.testing.allocator);
    defer store.deinit();

    var builder = PhaseKey.PhaseKeyBuilder.init(
        .exact_response,
        PhaseKey.CompilerFingerprint.init("replacement-test"),
    );
    builder.addInputBytes("request");
    const reference: ArtifactRef = .{
        .kind = .exact_response,
        .key = builder.finish(),
    };
    try store.put(reference, "old", &.{});
    try store.put(reference, "replacement", &.{});

    var artifact = (try store.getAlloc(std.testing.allocator, reference)).?;
    defer artifact.deinit();
    try std.testing.expectEqualStrings("replacement", artifact.payload);
    const statistics = store.statistics();
    try std.testing.expectEqual(@as(u64, 1), statistics.replacements);
    try std.testing.expectEqual(@as(u64, "replacement".len), statistics.resident_bytes);
    try std.testing.expectEqual(@as(u64, 1), statistics.entries);
}

test "memory artifact store evicts the least recently used entry within limits" {
    var store = MemoryArtifactStore.initWithLimits(std.testing.allocator, .{
        .max_entries = 2,
        .max_bytes = 6,
    });
    defer store.deinit();

    const compiler = PhaseKey.CompilerFingerprint.init("memory-lru-test");
    var references: [3]ArtifactRef = undefined;
    for (&references, 0..) |*reference, index| {
        var builder = PhaseKey.PhaseKeyBuilder.init(.exact_response, compiler);
        builder.addInputBytes(&.{@intCast(index)});
        reference.* = .{ .kind = .exact_response, .key = builder.finish() };
    }

    try store.put(references[0], "aaa", &.{});
    try store.put(references[1], "bbb", &.{});
    var first = (try store.getAlloc(std.testing.allocator, references[0])).?;
    first.deinit();
    try store.put(references[2], "ccc", &.{});

    try std.testing.expect(store.contains(references[0]));
    try std.testing.expect(!store.contains(references[1]));
    try std.testing.expect(store.contains(references[2]));
    const statistics = store.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.entries);
    try std.testing.expectEqual(@as(u64, 6), statistics.resident_bytes);
    try std.testing.expectEqual(@as(u64, 1), statistics.evictions);
    try std.testing.expectEqual(@as(u64, 3), statistics.bytes_evicted);
}

test "memory artifact store rejects oversized entries and removes stale replacements" {
    var store = MemoryArtifactStore.initWithLimits(std.testing.allocator, .{
        .max_entries = 2,
        .max_bytes = 3,
    });
    defer store.deinit();

    var builder = PhaseKey.PhaseKeyBuilder.init(
        .exact_response,
        PhaseKey.CompilerFingerprint.init("memory-admission-test"),
    );
    builder.addInputBytes("request");
    const reference: ArtifactRef = .{
        .kind = .exact_response,
        .key = builder.finish(),
    };
    try store.put(reference, "old", &.{});
    try store.put(reference, "oversized", &.{});
    try std.testing.expect(!store.contains(reference));
    const statistics = store.statistics();
    try std.testing.expectEqual(@as(u64, 0), statistics.entries);
    try std.testing.expectEqual(@as(u64, 0), statistics.resident_bytes);
    try std.testing.expectEqual(@as(u64, 1), statistics.admission_rejections);
}

test "memory artifact store zero byte limit disables zero-length retention" {
    var store = MemoryArtifactStore.initWithLimits(std.testing.allocator, .{
        .max_entries = 1,
        .max_bytes = 0,
    });
    defer store.deinit();

    var builder = PhaseKey.PhaseKeyBuilder.init(
        .exact_response,
        PhaseKey.CompilerFingerprint.init("memory-zero-limit-test"),
    );
    builder.addInputBytes("request");
    const reference: ArtifactRef = .{
        .kind = .exact_response,
        .key = builder.finish(),
    };
    try store.put(reference, "", &.{});
    try std.testing.expect(!store.contains(reference));
    try std.testing.expectEqual(
        @as(u64, 1),
        store.statistics().admission_rejections,
    );
}
