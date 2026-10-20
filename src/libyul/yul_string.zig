// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Interned Yul strings with deterministic FNV hashes.
//!
//! Handles borrow process-global repository storage and become invalid after
//! `reset`, matching the lifetime contract of the C++ repository. Configure
//! sharding before starting workers; reset only after all handle users stop.

const std = @import("std");

const Entry = struct {
    string: []u8,
};

pub const Handle = struct {
    entry: ?*const Entry,
    hash: u64,
};

const StringKey = struct {
    hash_value: u64,
    string: []const u8,
};

const StringKeyContext = struct {
    pub fn hash(_: @This(), key: StringKey) u64 {
        return key.hash_value;
    }

    pub fn eql(_: @This(), left: StringKey, right: StringKey) bool {
        return left.hash_value == right.hash_value and
            std.mem.eql(u8, left.string, right.string);
    }
};

const StringIndex = std.HashMapUnmanaged(StringKey, *const Entry, StringKeyContext, 80);

pub const Repository = struct {
    allocator: std.mem.Allocator,
    entry_pool: std.heap.MemoryPool(Entry) = .empty,
    entries: std.ArrayList(*Entry) = .empty,
    index: StringIndex = .empty,

    pub fn init(allocator: std.mem.Allocator) std.mem.Allocator.Error!Repository {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Repository) void {
        self.index.deinit(self.allocator);
        for (self.entries.items) |entry| {
            self.allocator.free(entry.string);
        }
        self.entries.deinit(self.allocator);
        self.entry_pool.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn stringToHandle(
        self: *Repository,
        string: []const u8,
    ) std.mem.Allocator.Error!Handle {
        if (string.len == 0) return emptyHandle();
        return self.stringToHandleHashed(string, hash(string));
    }

    fn stringToHandleHashed(
        self: *Repository,
        string: []const u8,
        string_hash: u64,
    ) std.mem.Allocator.Error!Handle {
        const lookup: StringKey = .{ .hash_value = string_hash, .string = string };
        if (self.index.get(lookup)) |entry| return .{ .entry = entry, .hash = string_hash };

        const owned = try self.allocator.dupe(u8, string);
        errdefer self.allocator.free(owned);
        return self.insertOwned(owned, string_hash);
    }

    /// Consumes nonempty bytes allocated by this repository's allocator,
    /// including on insertion failure or when an existing entry is found.
    fn stringToHandleOwnedHashed(
        self: *Repository,
        owned: []u8,
        string_hash: u64,
    ) std.mem.Allocator.Error!Handle {
        errdefer self.allocator.free(owned);
        const lookup: StringKey = .{ .hash_value = string_hash, .string = owned };
        if (self.index.get(lookup)) |entry| {
            self.allocator.free(owned);
            return .{ .entry = entry, .hash = string_hash };
        }
        return self.insertOwned(owned, string_hash);
    }

    pub fn generatedHandle(
        self: *Repository,
        base: Handle,
        counter: usize,
    ) std.mem.Allocator.Error!Handle {
        const owned = try self.allocator.print("{s}_{d}", .{ handleString(base), counter });
        return self.stringToHandleOwnedHashed(owned, hash(owned));
    }

    fn insertOwned(
        self: *Repository,
        owned: []u8,
        string_hash: u64,
    ) std.mem.Allocator.Error!Handle {
        const entry = try self.entry_pool.create(self.allocator);
        errdefer self.entry_pool.destroy(entry);
        entry.* = .{ .string = owned };
        try self.entries.append(self.allocator, entry);
        errdefer _ = self.entries.pop();
        try self.index.putNoClobber(
            self.allocator,
            .{ .hash_value = string_hash, .string = owned },
            entry,
        );
        return .{ .entry = entry, .hash = string_hash };
    }
};

fn emptyHandle() Handle {
    return .{ .entry = null, .hash = emptyHash() };
}

fn handleString(handle: Handle) []const u8 {
    return if (handle.entry) |entry| entry.string else "";
}

pub fn emptyHash() u64 {
    return 14_695_981_039_346_656_037;
}

pub fn hash(value: []const u8) u64 {
    var result = emptyHash();
    for (value) |byte| {
        result *%= 1_099_511_628_211;
        const signed_character: i8 = @bitCast(byte);
        const promoted: i64 = signed_character;
        result ^= @bitCast(promoted);
    }
    return result;
}

pub const ResetCallback = struct {
    context: ?*anyopaque = null,
    function: *const fn (context: ?*anyopaque) void,

    pub fn register(self: ResetCallback) std.mem.Allocator.Error!void {
        lockGlobal();
        defer unlockGlobal();
        try reset_callbacks.append(std.heap.page_allocator, self);
    }
};

var global_mutex: std.Io.Mutex = .init;
var reset_callbacks: std.ArrayList(ResetCallback) = .empty;

/// Each shard is an independent repository with its own lock. Serial
/// compilation uses only the first shard; parallel compilation spreads strings
/// over all of them so workers rarely wait for each other.
// Probe executables specialize this constant without adding runtime options to
// the compiler. Normal compiler roots retain the fixed 64-shard configuration.
const shard_count: usize = if (@hasDecl(@import("root"), "yul_interner_shards"))
    @import("root").yul_interner_shards
else
    64;
comptime {
    if (shard_count == 0 or shard_count > 64 or !std.math.isPowerOfTwo(shard_count))
        @compileError("Yul interner shard count must be a power of two from 1 through 64");
}
const Shard = struct {
    mutex: std.Io.Mutex align(std.atomic.cache_line) = .init,
    repository: ?Repository = null,

    fn repositoryLocked(self: *Shard) std.mem.Allocator.Error!*Repository {
        if (self.repository == null) {
            // Interning creates many small, process-lifetime allocations. Giving each
            // one directly to the page allocator amplifies the repository's RSS.
            self.repository = try Repository.init(std.heap.smp_allocator);
        }
        return &self.repository.?;
    }
};
var shards: [shard_count]Shard = @splat(.{});
var shard_mask: u64 = 0;

/// Use all shards (parallel compilation) or one (serial). Equal strings must
/// always reach the same shard. Call at startup before any compilation thread
/// exists, or after `reset` with all users quiescent. An initialized repository
/// returns `InternerAlreadyInitialized` without changing the routing mode,
/// even when the requested mode is unchanged.
pub fn setSharded(sharded: bool) error{InternerAlreadyInitialized}!void {
    for (&shards) |*shard| if (shard.repository != null) return error.InternerAlreadyInitialized;
    shard_mask = if (sharded) shard_count - 1 else 0;
}

fn shardIndex(string_hash: u64, mask: u64) usize {
    if (mask == 0) return 0;
    // Shards bucket their own tables on the low hash bits, so route on a
    // remixed hash to keep each shard's table evenly filled.
    return @intCast(std.hash.Wyhash.hash(0, std.mem.asBytes(&string_hash)) & mask);
}

/// Invalidates every outstanding handle and cached dialect. All users must be
/// quiescent: shard locks do not extend the lifetime of returned string slices.
pub fn reset() std.mem.Allocator.Error!void {
    lockGlobal();
    const callbacks = std.heap.page_allocator.dupe(ResetCallback, reset_callbacks.items) catch |err| { // zlinter-disable-current-line no_hidden_allocations - copying callbacks avoids invoking user code while holding the global lock
        unlockGlobal();
        return err;
    };
    unlockGlobal();
    defer std.heap.page_allocator.free(callbacks); // zlinter-disable-current-line no_hidden_allocations - copying callbacks avoids invoking user code while holding the global lock

    for (callbacks) |callback| callback.function(callback.context);

    lockGlobal();
    defer unlockGlobal();
    for (&shards) |*shard| std.Io.Threaded.mutexLockUncancelable(&shard.mutex);
    defer for (&shards) |*shard| std.Io.Threaded.mutexUnlock(&shard.mutex);
    for (&shards) |*shard| {
        if (shard.repository) |*repository| repository.deinit();
        shard.repository = null;
    }
}

pub const YulString = struct {
    handle: Handle = emptyHandle(),

    pub fn init(string: []const u8) std.mem.Allocator.Error!YulString {
        if (string.len == 0) return .{};
        const string_hash = hash(string);
        const shard = &shards[shardIndex(string_hash, shard_mask)];
        std.Io.Threaded.mutexLockUncancelable(&shard.mutex);
        defer std.Io.Threaded.mutexUnlock(&shard.mutex);
        return .{ .handle = try (try shard.repositoryLocked()).stringToHandleHashed(string, string_hash) };
    }

    pub fn initGenerated(base: YulString, counter: usize) std.mem.Allocator.Error!YulString {
        var buffer: [256]u8 = undefined;
        const generated = std.mem.print(
            &buffer,
            "{s}_{d}",
            .{ handleString(base.handle), counter },
        ) catch {
            const long = try std.heap.smp_allocator.print("{s}_{d}", .{ handleString(base.handle), counter });
            return initOwned(long);
        };
        return init(generated);
    }

    fn initOwned(owned: []u8) std.mem.Allocator.Error!YulString {
        const string_hash = hash(owned);
        const shard = &shards[shardIndex(string_hash, shard_mask)];
        std.Io.Threaded.mutexLockUncancelable(&shard.mutex);
        defer std.Io.Threaded.mutexUnlock(&shard.mutex);
        const repository = shard.repositoryLocked() catch |err| {
            std.heap.smp_allocator.free(owned);
            return err;
        };
        return .{ .handle = try repository.stringToHandleOwnedHashed(owned, string_hash) };
    }

    pub fn empty(self: YulString) bool {
        return self.handle.entry == null;
    }

    pub fn str(self: YulString) error{InvalidYulStringHandle}![]const u8 {
        return handleString(self.handle);
    }

    pub fn hashValue(self: YulString) u64 {
        return self.handle.hash;
    }

    pub fn eql(self: YulString, other: YulString) bool {
        return self.handle.entry == other.handle.entry;
    }

    pub fn lessThan(self: YulString, other: YulString) bool {
        if (self.handle.hash != other.handle.hash) return self.handle.hash < other.handle.hash;
        if (self.handle.entry == other.handle.entry) return false;
        return std.mem.order(u8, handleString(self.handle), handleString(other.handle)) == .lt;
    }
};

fn lockGlobal() void {
    std.Io.Threaded.mutexLockUncancelable(&global_mutex);
}

fn unlockGlobal() void {
    std.Io.Threaded.mutexUnlock(&global_mutex);
}

test "Yul strings intern, hash, order, and reset" {
    try reset();
    const empty = try YulString.init("");
    const alpha = try YulString.init("alpha");
    const beta = try YulString.init("beta");
    const alpha_again = try YulString.init("alpha");
    try std.testing.expect(empty.empty());
    try std.testing.expect(alpha.eql(alpha_again));
    try std.testing.expect(!alpha.eql(beta));
    try std.testing.expectEqualStrings("alpha", try alpha.str());
    try std.testing.expectEqual(hash("alpha"), alpha.hashValue());
    try std.testing.expectEqual(alpha.hashValue() < beta.hashValue(), alpha.lessThan(beta));
    try reset();
}

test "repository hash index returns stable handles" {
    var repository = try Repository.init(std.testing.allocator);
    defer repository.deinit();

    var name_buffer: [64]u8 = undefined;
    for (0..4096) |index| {
        const name = try std.mem.print(&name_buffer, "generated_name_{d}", .{index});
        const inserted = try repository.stringToHandle(name);
        try std.testing.expect(inserted.entry != null);
        const repeated = try repository.stringToHandle(name);
        try std.testing.expectEqual(inserted, repeated);
    }
}

test "owned Yul names transfer storage without another allocation" {
    var tracking = std.testing.FailingAllocator.init(std.testing.allocator, .{});
    const allocator = tracking.allocator();
    var repository = try Repository.init(allocator);
    defer repository.deinit();
    _ = try repository.stringToHandle("reserve repository storage");

    const base: [255]u8 = @splat('x');
    const owned = try allocator.print("{s}_0", .{base});
    const address = owned.ptr;
    const allocations = tracking.allocations;
    const inserted = try repository.stringToHandleOwnedHashed(owned, hash(owned));
    try std.testing.expectEqual(address, inserted.entry.?.string.ptr);
    try std.testing.expectEqual(allocations, tracking.allocations);

    const repeated = try allocator.dupe(u8, handleString(inserted));
    const deallocations = tracking.deallocations;
    const found = try repository.stringToHandleOwnedHashed(repeated, hash(repeated));
    try std.testing.expectEqual(inserted, found);
    try std.testing.expectEqual(deallocations + 1, tracking.deallocations);
    try std.testing.expectEqual(@as(usize, 2), repository.entries.items.len);
}

test "owned Yul name insertion rolls back every allocation failure" {
    const Check = struct {
        fn run(allocator: std.mem.Allocator) !void {
            var repository = try Repository.init(allocator);
            defer repository.deinit();
            const base: [4096]u8 = @splat('x');
            for (0..12) |i| {
                const owned = try allocator.print("{s}_{d}", .{ base, i });
                const address = owned.ptr;
                const inserted = repository.stringToHandleOwnedHashed(owned, hash(owned)) catch |err| {
                    try std.testing.expectEqual(i, repository.entries.items.len);
                    try std.testing.expectEqual(i, repository.index.count());
                    for (repository.entries.items) |entry| {
                        try std.testing.expectEqual(entry, repository.index.get(.{ .hash_value = hash(entry.string), .string = entry.string }).?);
                    }
                    return err;
                };
                try std.testing.expectEqual(address, inserted.entry.?.string.ptr);
                const repeated = try allocator.dupe(u8, handleString(inserted));
                try std.testing.expectEqual(inserted, try repository.stringToHandleOwnedHashed(repeated, hash(repeated)));
            }
        }
    };
    var deterministic = std.testing.FailingAllocator.init(std.testing.allocator, .{ .resize_fail_index = 0 });
    try std.testing.checkAllAllocationFailures(deterministic.allocator(), Check.run, .{});
}

test "generated Yul name boundaries share ordinary handles in both modes" {
    for ([_]bool{ false, true }) |sharded| {
        try reset();
        try setSharded(sharded);
        defer {
            reset() catch unreachable;
            setSharded(false) catch unreachable;
        }
        const base_bytes: [4094]u8 = @splat('x');
        var expected_buffer: [4096]u8 = undefined;
        for ([_]usize{ 255, 256, 257, 4096 }) |length| {
            const base = try YulString.init(base_bytes[0 .. length - 2]);
            const generated = try YulString.initGenerated(base, 0);
            const expected = try std.mem.print(&expected_buffer, "{s}_0", .{try base.str()});
            try std.testing.expectEqual(length, expected.len);
            try std.testing.expectEqualStrings(expected, try generated.str());
            try std.testing.expect(generated.eql(try YulString.init(expected)));
            try std.testing.expect(generated.eql(try YulString.initGenerated(base, 0)));
            try std.testing.expectEqual(hash(expected), generated.hashValue());
            try std.testing.expect(!generated.eql(try YulString.initGenerated(base, 1)));
        }
    }
}

test "Yul shard configuration rejects initialized repositories until reset" {
    try reset();
    defer {
        reset() catch unreachable;
        setSharded(false) catch unreachable;
    }
    for ([_]bool{ false, true }) |sharded| {
        try setSharded(!sharded);
        const empty = try YulString.init("");
        try std.testing.expect(empty.empty());
        try setSharded(sharded);
        const configured_mask = shard_mask;
        const first = try YulString.init("configured");
        try std.testing.expectError(error.InternerAlreadyInitialized, setSharded(!sharded));
        try std.testing.expectError(error.InternerAlreadyInitialized, setSharded(sharded));
        try std.testing.expectEqual(configured_mask, shard_mask);
        try std.testing.expect(first.eql(try YulString.init("configured")));
        try reset();
    }
    try setSharded(false);
    const reused = try YulString.init("after reset");
    try std.testing.expect(reused.eql(try YulString.init("after reset")));
}

test "Yul repositories reset and reuse in both modes" {
    try reset();
    defer {
        reset() catch unreachable;
        setSharded(false) catch unreachable;
    }
    for ([_]bool{ false, true }) |sharded| {
        try setSharded(sharded);
        for (0..3) |_| {
            const base = try YulString.init("session");
            const generated = try YulString.initGenerated(base, 42);
            try std.testing.expect(generated.eql(try YulString.init("session_42")));
            try reset();
            for (&shards) |*shard| try std.testing.expect(shard.repository == null);
            try setSharded(sharded);
        }
    }
}

test "Yul strings shard routing keeps shard tables evenly filled" {
    // Routing on the raw low bits would put every string of a shard into the
    // same 1/64 of that shard's buckets: only 256 (shard, bucket) pairs here.
    var seen: [shard_count][256]bool = @splat(@splat(false));
    var occupied: usize = 0;
    var buffer: [64]u8 = undefined;
    for (0..4096) |i| {
        const value_hash = hash(try std.mem.print(&buffer, "name_{d}", .{i}));
        const slot = &seen[shardIndex(value_hash, shard_count - 1)][@intCast(value_hash & 255)];
        if (!slot.*) occupied += 1;
        slot.* = true;
    }
    try std.testing.expect(occupied > 2048);
}

test "Yul strings stay canonical when sharded across threads" {
    try reset();
    try setSharded(true);
    defer {
        reset() catch unreachable;
        setSharded(false) catch unreachable;
    }
    const workers = 12;
    const count = 1024;
    const long_count = 32;
    const Context = struct {
        start: std.atomic.Value(bool) = .init(false),
        failed: std.atomic.Value(bool) = .init(false),
        shared: [workers][count]YulString = undefined,
        generated: [workers][count]YulString = undefined,
        long_generated: [workers][long_count]YulString = undefined,

        fn run(self: *@This(), worker: usize) void {
            while (!self.start.load(.acquire)) std.atomic.spinLoopHint();
            self.fill(worker) catch self.failed.store(true, .release);
        }

        fn fill(self: *@This(), worker: usize) !void {
            var buffer: [64]u8 = undefined;
            const base = try YulString.init("shared_base");
            for (0..count) |i| {
                self.shared[worker][i] = try YulString.init(try std.mem.print(&buffer, "shared_{d}", .{i}));
                self.generated[worker][i] = try YulString.initGenerated(base, i);
                const ordinary = try YulString.init(try std.mem.print(&buffer, "shared_base_{d}", .{i}));
                if (!self.generated[worker][i].eql(ordinary)) return error.NonCanonicalYulString;
                _ = try YulString.init(try std.mem.print(&buffer, "worker_{d}_{d}", .{ worker, i }));
            }
            const long_bytes: [300]u8 = @splat('x');
            const long_base = try YulString.init(&long_bytes);
            var long_buffer: [384]u8 = undefined;
            for (0..long_count) |i| {
                const formatted = try std.mem.print(&long_buffer, "{s}_{d}", .{ long_bytes, i });
                const first = if (worker % 2 == 0) try YulString.initGenerated(long_base, i) else try YulString.init(formatted);
                const second = if (worker % 2 == 0) try YulString.init(formatted) else try YulString.initGenerated(long_base, i);
                if (!first.eql(second)) return error.NonCanonicalYulString;
                self.long_generated[worker][i] = second;
            }
        }
    };
    var context: Context = .{};
    try runTestWorkers(Context, &context, workers, null);
    try std.testing.expect(!context.failed.load(.acquire));
    for (1..workers) |worker| for (0..count) |i| {
        try std.testing.expect(context.shared[0][i].eql(context.shared[worker][i]));
        try std.testing.expect(context.generated[0][i].eql(context.generated[worker][i]));
    };
    for (1..workers) |worker| for (0..long_count) |i| {
        try std.testing.expect(context.long_generated[0][i].eql(context.long_generated[worker][i]));
    };
    for (1..count) |i| {
        try std.testing.expect(!context.shared[0][i - 1].eql(context.shared[0][i]));
        try std.testing.expect(!context.generated[0][i - 1].eql(context.generated[0][i]));
    }
    var populated_shards: usize = 0;
    for (&shards) |*shard| if (shard.repository) |*repository| {
        if (repository.entries.items.len != 0) populated_shards += 1;
    };
    try std.testing.expect(populated_shards > 1);
}

fn runTestWorkers(comptime Context: type, context: *Context, comptime workers: usize, fail_after: ?usize) !void {
    var threads: [workers]std.Thread = undefined;
    var spawned: usize = 0;
    defer {
        context.start.store(true, .release);
        for (threads[0..spawned]) |thread| thread.join();
    }
    for (&threads, 0..) |*thread, i| {
        if (fail_after == i) return error.InjectedSpawnFailure;
        thread.* = try std.Thread.spawn(.{}, Context.run, .{ context, i });
        spawned += 1;
    }
}

test "Yul string workers are joined after partial startup failure" {
    const Context = struct {
        start: std.atomic.Value(bool) = .init(false),
        finished: std.atomic.Value(usize) = .init(0),

        fn run(self: *@This(), _: usize) void {
            while (!self.start.load(.acquire)) std.atomic.spinLoopHint();
            _ = self.finished.fetchAdd(1, .release);
        }
    };
    const workers = 6;
    for (0..workers) |fail_after| {
        var context: Context = .{};
        try std.testing.expectError(error.InjectedSpawnFailure, runTestWorkers(Context, &context, workers, fail_after));
        try std.testing.expect(context.start.load(.acquire));
        try std.testing.expectEqual(fail_after, context.finished.load(.acquire));
    }
    var context: Context = .{};
    try runTestWorkers(Context, &context, workers, null);
    try std.testing.expectEqual(@as(usize, workers), context.finished.load(.acquire));
}
