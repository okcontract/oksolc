// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Interned Yul strings with deterministic FNV hashes.
//!
//! Handles borrow process-global repository storage and become invalid after
//! `reset`, matching the lifetime contract of the C++ repository.

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
        const string_hash = hash(string);
        const lookup: StringKey = .{ .hash_value = string_hash, .string = string };
        if (self.index.get(lookup)) |entry| return .{ .entry = entry, .hash = string_hash };

        const owned = try self.allocator.dupe(u8, string);
        errdefer self.allocator.free(owned);
        return self.insertOwned(owned, string_hash);
    }

    pub fn generatedHandle(
        self: *Repository,
        base: Handle,
        counter: usize,
    ) std.mem.Allocator.Error!Handle {
        const owned = try std.fmt.allocPrint(
            self.allocator,
            "{s}_{d}",
            .{ handleString(base), counter },
        );
        errdefer self.allocator.free(owned);
        const string_hash = hash(owned);
        const lookup: StringKey = .{ .hash_value = string_hash, .string = owned };
        if (self.index.get(lookup)) |entry| {
            self.allocator.free(owned);
            return .{ .entry = entry, .hash = string_hash };
        }
        return self.insertOwned(owned, string_hash);
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
var global_repository: ?Repository = null;
var reset_callbacks: std.ArrayList(ResetCallback) = .empty;

fn repositoryLocked() std.mem.Allocator.Error!*Repository {
    if (global_repository == null) {
        // Interning creates many small, process-lifetime allocations. Giving each
        // one directly to the page allocator amplifies the repository's RSS.
        global_repository = try Repository.init(std.heap.smp_allocator);
    }
    return &global_repository.?;
}

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
    if (global_repository) |*repository| repository.deinit();
    global_repository = null;
}

pub const YulString = struct {
    handle: Handle = emptyHandle(),

    pub fn init(string: []const u8) std.mem.Allocator.Error!YulString {
        lockGlobal();
        defer unlockGlobal();
        return .{ .handle = try (try repositoryLocked()).stringToHandle(string) };
    }

    pub fn initGenerated(base: YulString, counter: usize) std.mem.Allocator.Error!YulString {
        var buffer: [256]u8 = undefined;
        const generated = std.fmt.bufPrint(
            &buffer,
            "{s}_{d}",
            .{ handleString(base.handle), counter },
        ) catch {
            lockGlobal();
            defer unlockGlobal();
            return .{ .handle = try (try repositoryLocked()).generatedHandle(base.handle, counter) };
        };
        return init(generated);
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
    std.Io.Threaded.mutexLock(&global_mutex);
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
        const name = try std.fmt.bufPrint(&name_buffer, "generated_name_{d}", .{index});
        const inserted = try repository.stringToHandle(name);
        try std.testing.expect(inserted.entry != null);
        const repeated = try repository.stringToHandle(name);
        try std.testing.expectEqual(inserted, repeated);
    }
}
