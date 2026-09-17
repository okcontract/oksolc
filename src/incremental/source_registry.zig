// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Stable source-name interning with transactional revision replacement.
//!
//! A registry owns canonical names and committed source contents for its
//! lifetime. A revision is first assembled in isolated candidate storage, so
//! allocation or compilation failure can abort without changing stable IDs or
//! the preceding revision. Historical tombstones retain only their identity;
//! active-source work never scans the full ID history.

const std = @import("std");
const FixedHash = @import("../libsolutil/fixed_hash.zig");
const Identity = @import("identity.zig");
const Keccak256 = @import("../libsolutil/keccak256.zig");

const H256 = FixedHash.H256;
pub const SourceId = Identity.SourceId;
pub const SourceKey = Identity.SourceKey;

pub const Change = enum { none, added, unchanged, modified, removed };

pub const SourceRecord = struct {
    id: SourceId,
    key: SourceKey,
    /// Owned by `SourceRegistry` and stable until `deinit`.
    name: []const u8,
    /// Owned by `SourceRegistry` while active. Empty for a tombstone.
    content: []const u8,
    content_digest: H256,
    last_seen_revision: u64,
    last_parse_revision: u64,
    last_change_revision: u64,
    active: bool,
    change: Change,
};

pub const UpsertResult = struct { id: SourceId, change: Change };

pub const RevisionSummary = struct {
    revision: u64,
    active_sources: usize,
    added: usize,
    unchanged: usize,
    modified: usize,
    removed: usize,
};

const PendingRecord = struct {
    record: SourceRecord,
    is_new: bool,
    owns_content: bool,
};

const RevisionCandidate = struct {
    revision: u64,
    records: std.ArrayList(PendingRecord) = .empty,
    record_indices: std.AutoHashMapUnmanaged(SourceId, usize) = .empty,
    ids_by_name: std.StringHashMapUnmanaged(SourceId) = .empty,
    active_ids: std.ArrayList(SourceId) = .empty,
    parse_order: std.ArrayList(SourceId) = .empty,
    changed_ids: std.ArrayList(SourceId) = .empty,
    new_source_count: usize = 0,
    finished: bool = false,

    fn deinit(self: *RevisionCandidate, allocator: std.mem.Allocator) void {
        for (self.records.items) |pending| {
            if (pending.owns_content) allocator.free(pending.record.content);
            if (pending.is_new) allocator.free(pending.record.name);
        }
        self.changed_ids.deinit(allocator);
        self.parse_order.deinit(allocator);
        self.active_ids.deinit(allocator);
        self.ids_by_name.deinit(allocator);
        self.record_indices.deinit(allocator);
        self.records.deinit(allocator);
        self.* = undefined;
    }
};

pub const SourceRegistry = struct {
    allocator: std.mem.Allocator,
    records: std.ArrayList(SourceRecord) = .empty,
    ids_by_name: std.StringHashMapUnmanaged(SourceId) = .empty,
    active_ids: std.ArrayList(SourceId) = .empty,
    parse_order: std.ArrayList(SourceId) = .empty,
    changed_ids: std.ArrayList(SourceId) = .empty,
    revision: u64 = 0,
    candidate: ?RevisionCandidate = null,

    pub fn init(allocator: std.mem.Allocator) SourceRegistry {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *SourceRegistry) void {
        self.abortRevision();
        for (self.records.items) |entry| {
            if (entry.active) self.allocator.free(entry.content);
            self.allocator.free(entry.name);
        }
        self.changed_ids.deinit(self.allocator);
        self.parse_order.deinit(self.allocator);
        self.active_ids.deinit(self.allocator);
        self.ids_by_name.deinit(self.allocator);
        self.records.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn beginRevision(self: *SourceRegistry) error{
        RevisionAlreadyOpen,
        RevisionOverflow,
    }!u64 {
        if (self.candidate != null) return error.RevisionAlreadyOpen;
        if (self.revision == std.math.maxInt(u64)) return error.RevisionOverflow;
        const next_revision = self.revision + 1;
        self.candidate = .{ .revision = next_revision };
        return next_revision;
    }

    /// Completes candidate bookkeeping and reserves every allocation needed by
    /// `commitRevision`, which is consequently infallible.
    pub fn finishRevision(
        self: *SourceRegistry,
    ) (std.mem.Allocator.Error || error{
        RevisionAlreadyFinished,
        RevisionNotOpen,
        SourceIdOverflow,
    })!RevisionSummary {
        const candidate = self.candidatePtr() orelse return error.RevisionNotOpen;
        if (candidate.finished) return error.RevisionAlreadyFinished;

        try candidate.changed_ids.ensureUnusedCapacity(
            self.allocator,
            self.active_ids.items.len,
        );
        try self.records.ensureUnusedCapacity(
            self.allocator,
            candidate.new_source_count,
        );
        try self.ids_by_name.ensureUnusedCapacity(
            self.allocator,
            std.math.cast(u32, candidate.new_source_count) orelse
                return error.SourceIdOverflow,
        );

        var summary: RevisionSummary = .{
            .revision = candidate.revision,
            .active_sources = candidate.active_ids.items.len,
            .added = 0,
            .unchanged = 0,
            .modified = 0,
            .removed = 0,
        };
        for (candidate.records.items) |pending| switch (pending.record.change) {
            .none, .removed => unreachable,
            .added => summary.added += 1,
            .unchanged => summary.unchanged += 1,
            .modified => summary.modified += 1,
        };
        for (self.active_ids.items) |id| {
            if (!candidate.record_indices.contains(id)) {
                candidate.changed_ids.appendAssumeCapacity(id);
                summary.removed += 1;
            }
        }
        candidate.finished = true;
        return summary;
    }

    /// Atomically replaces the committed revision. `finishRevision` reserves
    /// all required storage, so no error can expose a partially committed view.
    pub fn commitRevision(self: *SourceRegistry) void {
        const candidate = self.candidatePtr().?;
        std.debug.assert(candidate.finished);

        for (self.active_ids.items) |id| {
            const entry = self.recordKnownMutable(id).?;
            const pending_index = candidate.record_indices.get(id);
            const content_is_reused = if (pending_index) |index|
                !candidate.records.items[index].owns_content
            else
                false;
            if (!content_is_reused) self.allocator.free(entry.content);
            entry.active = false;
            entry.content = "";
            entry.change = .removed;
            entry.last_change_revision = candidate.revision;
        }

        for (candidate.records.items) |*pending| {
            const entry = pending.record;
            if (pending.is_new) {
                std.debug.assert(entry.id.index() == self.records.items.len);
                self.records.appendAssumeCapacity(entry);
                self.ids_by_name.putAssumeCapacityNoClobber(entry.name, entry.id);
                pending.is_new = false;
            } else {
                self.recordKnownMutable(entry.id).?.* = entry;
            }
            pending.owns_content = false;
        }

        self.active_ids.deinit(self.allocator);
        self.active_ids = candidate.active_ids;
        candidate.active_ids = .empty;
        self.parse_order.deinit(self.allocator);
        self.parse_order = candidate.parse_order;
        candidate.parse_order = .empty;
        self.changed_ids.deinit(self.allocator);
        self.changed_ids = candidate.changed_ids;
        candidate.changed_ids = .empty;
        self.revision = candidate.revision;

        candidate.deinit(self.allocator);
        self.candidate = null;
    }

    /// Discards a candidate and preserves the committed revision byte-for-byte.
    pub fn abortRevision(self: *SourceRegistry) void {
        if (self.candidate) |*candidate| candidate.deinit(self.allocator);
        self.candidate = null;
    }

    /// Registers source contents from the candidate revision. Changed contents
    /// are copied into registry ownership; unchanged buffers are safely reused.
    pub fn upsert(
        self: *SourceRegistry,
        name: []const u8,
        content: []const u8,
    ) (std.mem.Allocator.Error || error{
        ConflictingSourceContent,
        RevisionFinished,
        RevisionNotOpen,
        SourceIdOverflow,
    })!UpsertResult {
        const candidate = self.candidatePtr() orelse return error.RevisionNotOpen;
        if (candidate.finished) return error.RevisionFinished;
        const digest = Keccak256.keccak256(content);
        if (candidate.ids_by_name.get(name)) |id| {
            const pending = &candidate.records.items[candidate.record_indices.get(id).?];
            if (!pending.record.content_digest.eql(&digest) or
                !std.mem.eql(u8, pending.record.content, content))
                return error.ConflictingSourceContent;
            return .{ .id = id, .change = pending.record.change };
        }

        const known_id = self.ids_by_name.get(name);
        const is_new = known_id == null;
        const id = known_id orelse blk: {
            const raw_id = self.records.items.len + candidate.new_source_count;
            if (raw_id > std.math.maxInt(u32)) return error.SourceIdOverflow;
            break :blk SourceId.init(@intCast(raw_id));
        };
        const previous = if (known_id != null) self.recordKnown(id).? else null;
        const unchanged = if (previous) |entry|
            entry.active and entry.content_digest.eql(&digest) and
                std.mem.eql(u8, entry.content, content)
        else
            false;
        const change: Change = if (is_new or (previous != null and !previous.?.active))
            .added
        else if (unchanged)
            .unchanged
        else
            .modified;

        const owned_name = if (is_new) try self.allocator.dupe(u8, name) else null;
        errdefer if (owned_name) |value| self.allocator.free(value);
        const stable_name = owned_name orelse previous.?.name;
        const owned_content = if (unchanged) null else try self.allocator.dupe(u8, content);
        errdefer if (owned_content) |value| self.allocator.free(value);
        const stable_content = owned_content orelse previous.?.content;

        try candidate.records.ensureUnusedCapacity(self.allocator, 1);
        try candidate.record_indices.ensureUnusedCapacity(self.allocator, 1);
        try candidate.ids_by_name.ensureUnusedCapacity(self.allocator, 1);
        try candidate.active_ids.ensureUnusedCapacity(self.allocator, 1);
        if (change != .unchanged)
            try candidate.changed_ids.ensureUnusedCapacity(self.allocator, 1);

        const record_index = candidate.records.items.len;
        candidate.records.appendAssumeCapacity(.{
            .record = .{
                .id = id,
                .key = SourceKey.init(stable_name),
                .name = stable_name,
                .content = stable_content,
                .content_digest = digest,
                .last_seen_revision = candidate.revision,
                .last_parse_revision = 0,
                .last_change_revision = if (change == .unchanged)
                    previous.?.last_change_revision
                else
                    candidate.revision,
                .active = true,
                .change = change,
            },
            .is_new = is_new,
            .owns_content = owned_content != null,
        });
        candidate.record_indices.putAssumeCapacityNoClobber(id, record_index);
        candidate.ids_by_name.putAssumeCapacityNoClobber(stable_name, id);
        candidate.active_ids.appendAssumeCapacity(id);
        if (change != .unchanged) candidate.changed_ids.appendAssumeCapacity(id);
        if (is_new) candidate.new_source_count += 1;
        return .{ .id = id, .change = change };
    }

    pub fn appendParseOrder(
        self: *SourceRegistry,
        id: SourceId,
    ) (std.mem.Allocator.Error || error{
        DuplicateParseOrder,
        InactiveSource,
        RevisionFinished,
        RevisionNotOpen,
        UnknownSource,
    })!void {
        const candidate = self.candidatePtr() orelse return error.RevisionNotOpen;
        if (candidate.finished) return error.RevisionFinished;
        const record_index = candidate.record_indices.get(id) orelse
            return if (self.recordKnown(id) == null) error.UnknownSource else error.InactiveSource;
        const entry = &candidate.records.items[record_index].record;
        if (entry.last_parse_revision == candidate.revision)
            return error.DuplicateParseOrder;
        try candidate.parse_order.append(self.allocator, id);
        entry.last_parse_revision = candidate.revision;
    }

    pub fn idForName(self: *const SourceRegistry, name: []const u8) ?SourceId {
        if (self.candidateConst()) |candidate| return candidate.ids_by_name.get(name);
        const id = self.ids_by_name.get(name) orelse return null;
        return if (self.recordKnown(id).?.active) id else null;
    }

    /// Includes inactive tombstones and names staged by the open candidate.
    pub fn knownIdForName(self: *const SourceRegistry, name: []const u8) ?SourceId {
        if (self.candidateConst()) |candidate|
            if (candidate.ids_by_name.get(name)) |id| return id;
        return self.ids_by_name.get(name);
    }

    pub fn record(self: *const SourceRegistry, id: SourceId) ?*const SourceRecord {
        if (self.candidateConst()) |candidate| {
            const index = candidate.record_indices.get(id) orelse return null;
            return &candidate.records.items[index].record;
        }
        const result = self.recordKnown(id) orelse return null;
        return if (result.active) result else null;
    }

    pub fn parseOrder(self: *const SourceRegistry) []const SourceId {
        if (self.candidateConst()) |candidate| return candidate.parse_order.items;
        return self.parse_order.items;
    }

    pub fn activeIds(self: *const SourceRegistry) []const SourceId {
        if (self.candidateConst()) |candidate| return candidate.active_ids.items;
        return self.active_ids.items;
    }

    /// IDs changed by the candidate/last committed revision, including removals.
    pub fn changedIds(self: *const SourceRegistry) []const SourceId {
        if (self.candidateConst()) |candidate| return candidate.changed_ids.items;
        return self.changed_ids.items;
    }

    pub fn changeForId(self: *const SourceRegistry, id: SourceId) ?Change {
        if (self.candidateConst()) |candidate| {
            if (candidate.record_indices.get(id)) |index|
                return candidate.records.items[index].record.change;
            const previous = self.recordKnown(id) orelse return null;
            return if (candidate.finished and previous.active) .removed else .none;
        }
        const entry = self.recordKnown(id) orelse return null;
        if (entry.active) return entry.change;
        return if (entry.last_change_revision == self.revision) .removed else .none;
    }

    pub fn sortedActiveIdsAlloc(
        self: *const SourceRegistry,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error![]SourceId {
        const result = try allocator.dupe(SourceId, self.activeIds());
        std.mem.sort(SourceId, result, self, struct {
            fn lessThan(registry: *const SourceRegistry, left: SourceId, right: SourceId) bool {
                return std.mem.order(
                    u8,
                    registry.record(left).?.name,
                    registry.record(right).?.name,
                ) == .lt;
            }
        }.lessThan);
        return result;
    }

    pub fn count(self: *const SourceRegistry) usize {
        return self.activeIds().len;
    }

    pub fn knownCount(self: *const SourceRegistry) usize {
        const pending_count = if (self.candidateConst()) |candidate|
            candidate.new_source_count
        else
            0;
        return self.records.items.len + pending_count;
    }

    pub fn currentRevision(self: *const SourceRegistry) u64 {
        return if (self.candidateConst()) |candidate| candidate.revision else self.revision;
    }

    pub fn hasOpenRevision(self: *const SourceRegistry) bool {
        return self.candidate != null;
    }

    fn candidatePtr(self: *SourceRegistry) ?*RevisionCandidate {
        if (self.candidate) |*candidate| return candidate;
        return null;
    }

    fn candidateConst(self: *const SourceRegistry) ?*const RevisionCandidate {
        if (self.candidate) |*candidate| return candidate;
        return null;
    }

    fn recordKnown(self: *const SourceRegistry, id: SourceId) ?*const SourceRecord {
        const index: usize = @intCast(id.index());
        if (index >= self.records.items.len) return null;
        return &self.records.items[index];
    }

    fn recordKnownMutable(self: *SourceRegistry, id: SourceId) ?*SourceRecord {
        const index: usize = @intCast(id.index());
        if (index >= self.records.items.len) return null;
        return &self.records.items[index];
    }
};

test "source IDs survive edits, removal, and resurrection without reuse" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();

    _ = try registry.beginRevision();
    const first = try registry.upsert("A.sol", "contract A {}");
    const second = try registry.upsert("B.sol", "contract B {}");
    try std.testing.expectEqual(Change.added, first.change);
    try std.testing.expectEqual(Change.added, second.change);
    try std.testing.expectEqual(@as(u32, 0), first.id.index());
    try std.testing.expectEqual(@as(u32, 1), second.id.index());
    const initial = try registry.finishRevision();
    try std.testing.expectEqual(@as(usize, 2), initial.added);
    registry.commitRevision();

    _ = try registry.beginRevision();
    const unchanged = try registry.upsert("A.sol", "contract A {}");
    try std.testing.expectEqual(Change.unchanged, unchanged.change);
    const removed = try registry.finishRevision();
    try std.testing.expectEqual(@as(usize, 1), removed.removed);
    registry.commitRevision();
    try std.testing.expect(registry.idForName("B.sol") == null);
    try std.testing.expectEqual(second.id, registry.knownIdForName("B.sol").?);

    _ = try registry.beginRevision();
    const modified = try registry.upsert("A.sol", "contract A { uint x; }");
    const resurrected = try registry.upsert("B.sol", "contract B {}");
    const third = try registry.upsert("C.sol", "contract C {}");
    try std.testing.expectEqual(Change.modified, modified.change);
    try std.testing.expectEqual(Change.added, resurrected.change);
    try std.testing.expectEqual(second.id, resurrected.id);
    try std.testing.expectEqual(@as(u32, 2), third.id.index());
    _ = try registry.finishRevision();
    registry.commitRevision();
}

test "aborted revisions preserve committed contents, IDs, and revision" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const a = (try registry.upsert("A.sol", "first")).id;
    _ = try registry.finishRevision();
    registry.commitRevision();

    _ = try registry.beginRevision();
    _ = try registry.upsert("A.sol", "second");
    const staged = (try registry.upsert("Before.sol", "staged")).id;
    _ = try registry.finishRevision();
    registry.abortRevision();

    try std.testing.expectEqual(@as(u64, 1), registry.currentRevision());
    try std.testing.expectEqualStrings("first", registry.record(a).?.content);
    try std.testing.expect(registry.knownIdForName("Before.sol") == null);

    _ = try registry.beginRevision();
    const reused = (try registry.upsert("After.sol", "committed")).id;
    try std.testing.expectEqual(staged, reused);
    _ = try registry.finishRevision();
    registry.commitRevision();
}

test "parse order is explicit while sorted views are deterministic" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const z = (try registry.upsert("Z.sol", "z")).id;
    const a = (try registry.upsert("A.sol", "a")).id;
    const m = (try registry.upsert("M.sol", "m")).id;
    try registry.appendParseOrder(z);
    try registry.appendParseOrder(a);
    try registry.appendParseOrder(m);
    try std.testing.expectEqualSlices(SourceId, &.{ z, a, m }, registry.parseOrder());
    try std.testing.expectError(error.DuplicateParseOrder, registry.appendParseOrder(a));

    const sorted = try registry.sortedActiveIdsAlloc(std.testing.allocator);
    defer std.testing.allocator.free(sorted);
    try std.testing.expectEqualSlices(SourceId, &.{ a, m, z }, sorted);
    _ = try registry.finishRevision();
    registry.commitRevision();
}

test "a source name cannot resolve to different bytes within one revision" {
    var registry = SourceRegistry.init(std.testing.allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    _ = try registry.upsert("A.sol", "first");
    try std.testing.expectError(
        error.ConflictingSourceContent,
        registry.upsert("A.sol", "second"),
    );
}

fn exerciseAllocationFailures(allocator: std.mem.Allocator) !void {
    var registry = SourceRegistry.init(allocator);
    defer registry.deinit();
    _ = try registry.beginRevision();
    const first = (try registry.upsert("A.sol", "contract A {}")).id;
    try registry.appendParseOrder(first);
    const second = (try registry.upsert("B.sol", "contract B {}")).id;
    try registry.appendParseOrder(second);
    const sorted = try registry.sortedActiveIdsAlloc(allocator);
    defer allocator.free(sorted);
    _ = try registry.finishRevision();
    registry.commitRevision();

    _ = try registry.beginRevision();
    _ = try registry.upsert("A.sol", "contract A { uint x; }");
    _ = try registry.upsert("C.sol", "contract C {}");
    _ = try registry.finishRevision();
    registry.abortRevision();
}

test "source registry allocation failures release partial state" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        exerciseAllocationFailures,
        .{},
    );
}
