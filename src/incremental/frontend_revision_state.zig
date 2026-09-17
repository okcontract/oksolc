// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Session-owned, transactional Solidity frontend revision state.
//!
//! A revision holds the state mutex for the lifetime of a Solidity compile.
//! The registry, graph, and dirty set advance together only after compilation
//! has produced an owned response. Failures discard candidate storage and leave
//! the preceding committed revision available for the next request.

const std = @import("std");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const PhaseKey = @import("phase_key.zig");
const CompatibilityIds = @import("compatibility_ids.zig");
const SourceRegistryModule = @import("source_registry.zig");
const SourceGraphModule = @import("source_graph.zig");
const SyntaxRevisionModule = @import("syntax_revision.zig");
const SemanticRevisionModule = @import("semantic_revision.zig");
const SemanticFingerprint = @import("semantic_fingerprint.zig");

pub const SourceId = SourceRegistryModule.SourceId;
pub const SourceRegistry = SourceRegistryModule.SourceRegistry;
pub const SourceEdge = SourceGraphModule.SourceEdge;
pub const SourceGraph = SourceGraphModule.SourceGraph;
pub const DirtySourceSet = SourceGraphModule.DirtySourceSet;
pub const SyntaxRevision = SyntaxRevisionModule.SyntaxRevision;
pub const SyntaxSource = SyntaxRevisionModule.SyntaxSource;
pub const SemanticRevision = SemanticRevisionModule.SemanticRevision;
pub const SourceFingerprintEntry = SemanticFingerprint.SourceFingerprintEntry;
pub const ArtifactKey = PhaseKey.ArtifactKey;
pub const FrontendFingerprint = PhaseKey.FrontendFingerprint;

pub const Statistics = struct {
    revision: u64 = 0,
    active_sources: usize = 0,
    known_sources: usize = 0,
    graph_nodes: usize = 0,
    graph_edges: usize = 0,
    dirty_sources: usize = 0,
    parsed_syntax_sources: usize = 0,
    reused_syntax_sources: usize = 0,
    analyzed_semantic_sources: usize = 0,
    reused_semantic_sources: usize = 0,
    semantic_overlay_depth: usize = 0,
    retained_semantic_syntax_sources: usize = 0,
    fingerprinted_sources: usize = 0,
    semantic_dependency_edges: usize = 0,
    semantic_analyzed: bool = false,
};

pub const FrontendRevisionState = struct {
    allocator: std.mem.Allocator,
    mutex: std.Io.Mutex = .init,
    statistics_mutex: std.Io.Mutex = .init,
    statistics_value: Statistics = .{},
    registry: SourceRegistry,
    graph: ?SourceGraph = null,
    dirty: ?DirtySourceSet = null,
    spare_dirty: ?DirtySourceSet = null,
    syntax: ?SyntaxRevision = null,
    semantic: ?*SemanticRevision = null,
    fingerprints: ?SemanticFingerprint.FingerprintRevision = null,
    current_request_key: ?ArtifactKey = null,
    frontend_fingerprint: ?FrontendFingerprint = null,

    pub fn init(allocator: std.mem.Allocator) FrontendRevisionState {
        return .{ .allocator = allocator, .registry = SourceRegistry.init(allocator) };
    }

    /// No revision may remain active when the state is destroyed.
    pub fn deinit(self: *FrontendRevisionState) void {
        if (self.semantic) |semantic| semantic.destroy();
        if (self.syntax) |*syntax| syntax.deinit();
        if (self.fingerprints) |*fingerprints| fingerprints.deinit();
        if (self.spare_dirty) |*dirty| dirty.deinit();
        if (self.dirty) |*dirty| dirty.deinit();
        if (self.graph) |*graph| graph.deinit();
        self.registry.deinit();
        self.* = undefined;
    }

    pub fn beginRevision(
        self: *FrontendRevisionState,
        request_key: ?ArtifactKey,
    ) !Revision {
        self.lock();
        errdefer self.unlock();
        _ = try self.registry.beginRevision();
        return .{ .state = self, .request_key = request_key };
    }

    /// A response cache entry is coherent with retained frontend state only if
    /// it represents the state that is already committed. With no committed
    /// state (including a process restart), exact responses remain safe.
    pub fn lockExactResponse(
        self: *FrontendRevisionState,
        request_key: ArtifactKey,
    ) ExactResponseGuard {
        self.lock();
        const coherent = if (self.current_request_key) |*current|
            current.eql(&request_key)
        else
            true;
        return .{ .state = self, .coherent = coherent };
    }

    pub const ExactResponseGuard = struct {
        state: *FrontendRevisionState,
        coherent: bool,
        locked: bool = true,

        pub fn release(self: *ExactResponseGuard) void {
            if (!self.locked) return;
            self.locked = false;
            self.state.unlock();
        }
    };

    /// Returns the last committed snapshot without acquiring the revision
    /// mutex, so a compiler callback may safely observe session statistics.
    pub fn statistics(self: *FrontendRevisionState) Statistics {
        std.Io.Threaded.mutexLock(&self.statistics_mutex);
        defer std.Io.Threaded.mutexUnlock(&self.statistics_mutex);
        return self.statistics_value;
    }

    fn publishStatistics(self: *FrontendRevisionState) void {
        const value: Statistics = .{
            .revision = self.registry.currentRevision(),
            .active_sources = self.registry.count(),
            .known_sources = self.registry.knownCount(),
            .graph_nodes = if (self.graph) |*graph| graph.storageNodeCount() else 0,
            .graph_edges = if (self.graph) |*graph| graph.edgeCount() else 0,
            .dirty_sources = if (self.dirty) |*dirty| dirty.count() else 0,
            .parsed_syntax_sources = if (self.syntax) |*syntax|
                syntax.parsed_sources
            else
                0,
            .reused_syntax_sources = if (self.syntax) |*syntax|
                syntax.reused_sources
            else
                0,
            .analyzed_semantic_sources = if (self.semantic) |semantic|
                semantic.analyzed_sources
            else
                0,
            .reused_semantic_sources = if (self.semantic) |semantic|
                semantic.reused_sources
            else
                0,
            .semantic_overlay_depth = if (self.semantic) |semantic|
                semantic.overlayDepth()
            else
                0,
            .retained_semantic_syntax_sources = if (self.semantic) |semantic|
                semantic.retainedSyntaxSourceCount()
            else
                0,
            .fingerprinted_sources = if (self.fingerprints) |*fingerprints|
                countFingerprints(fingerprints)
            else
                0,
            .semantic_dependency_edges = if (self.semantic) |semantic|
                semantic.dependencyMasks().len
            else
                0,
            .semantic_analyzed = if (self.semantic) |semantic|
                semantic.completeness == .analyzed
            else
                false,
        };
        std.Io.Threaded.mutexLock(&self.statistics_mutex);
        defer std.Io.Threaded.mutexUnlock(&self.statistics_mutex);
        self.statistics_value = value;
    }

    /// Live-state queries acquire the revision mutex and are not reentrant from
    /// a callback in the same session. Callback code should use `statistics()`.
    pub fn sourceId(self: *FrontendRevisionState, name: []const u8) ?SourceId {
        self.lock();
        defer self.unlock();
        return self.registry.knownIdForName(name);
    }

    /// See `sourceId` for callback reentrancy constraints.
    pub fn sourceChange(
        self: *FrontendRevisionState,
        source: SourceId,
    ) ?SourceRegistryModule.Change {
        self.lock();
        defer self.unlock();
        return self.registry.changeForId(source);
    }

    /// See `sourceId` for callback reentrancy constraints.
    pub fn isDirty(self: *FrontendRevisionState, source: SourceId) bool {
        self.lock();
        defer self.unlock();
        return if (self.dirty) |*dirty| dirty.contains(source) else false;
    }

    fn lock(self: *FrontendRevisionState) void {
        std.Io.Threaded.mutexLock(&self.mutex);
    }

    fn unlock(self: *FrontendRevisionState) void {
        std.Io.Threaded.mutexUnlock(&self.mutex);
    }

    pub const Revision = struct {
        state: *FrontendRevisionState,
        request_key: ?ArtifactKey,
        candidate_graph: ?SourceGraph = null,
        candidate_dirty: ?DirtySourceSet = null,
        candidate_frontend_fingerprint: ?FrontendFingerprint = null,
        candidate_fingerprints: ?SemanticFingerprint.FingerprintRevision = null,
        candidate_syntax: ?SyntaxRevision = null,
        candidate_semantic: ?*SemanticRevision = null,
        finished: bool = false,
        closed: bool = false,

        pub fn registry(self: *Revision) *SourceRegistry {
            std.debug.assert(!self.closed);
            return &self.state.registry;
        }

        pub fn previousSyntax(
            self: *const Revision,
            source_id: SourceId,
        ) ?*SyntaxSource {
            std.debug.assert(!self.closed);
            const syntax = if (self.state.syntax) |*value| value else return null;
            return syntax.get(source_id);
        }

        pub fn createSemantic(
            self: *Revision,
            source_node_counts: []const CompatibilityIds.SourceNodeCount,
        ) (std.mem.Allocator.Error || error{
            ParentSemanticRevisionIncomplete,
            ParentSemanticRevisionNotReusable,
            RevisionNotFinished,
            SemanticAlreadyCreated,
        })!*SemanticRevision {
            std.debug.assert(!self.closed);
            if (self.candidate_semantic != null) return error.SemanticAlreadyCreated;
            if (!self.finished) return error.RevisionNotFinished;
            const graph = &self.candidate_graph.?;
            const dirty = &self.candidate_dirty.?;
            var active_dirty_sources: usize = 0;
            for (self.state.registry.activeIds()) |source|
                active_dirty_sources += @intFromBool(dirty.contains(source));
            const can_reuse = active_dirty_sources < graph.activeSourceCount() and
                if (self.state.semantic) |previous|
                    previous.reusableAsParent() and
                        previous.compatibilityIdsMatch(source_node_counts)
                else
                    false;
            const semantic = if (can_reuse) reuse: {
                const masked_sources = try dirty.sortedIdsAlloc(self.state.allocator);
                defer self.state.allocator.free(masked_sources);
                break :reuse try SemanticRevision.createChild(
                    self.state.allocator,
                    self.state.semantic.?,
                    self.state.registry.knownCount(),
                    masked_sources,
                );
            } else try SemanticRevision.create(
                self.state.allocator,
                @enumFromInt(self.state.registry.currentRevision()),
            );
            self.candidate_semantic = semantic;
            return semantic;
        }

        pub fn sourceIsDirty(self: *const Revision, source: SourceId) bool {
            std.debug.assert(!self.closed);
            std.debug.assert(self.finished);
            return self.candidate_dirty.?.contains(source);
        }

        /// Transfers a complete candidate's syntax references into this
        /// transaction. Commit and abort are infallible from this point.
        pub fn adoptSyntax(
            self: *Revision,
            syntax: *SyntaxRevision,
        ) error{ SyntaxAlreadyAdopted, InvalidSyntaxCapacity }!void {
            std.debug.assert(!self.closed);
            if (self.candidate_syntax != null) return error.SyntaxAlreadyAdopted;
            if (syntax.sources.len != self.state.registry.knownCount())
                return error.InvalidSyntaxCapacity;
            self.candidate_syntax = syntax.*;
            syntax.* = undefined;
        }

        pub fn finish(
            self: *Revision,
            edges: []const SourceEdge,
            frontend_fingerprint: FrontendFingerprint,
            fingerprint_entries: []const SourceFingerprintEntry,
        ) !*const SourceGraph {
            std.debug.assert(!self.closed);
            if (self.finished) return error.RevisionAlreadyFinished;
            _ = try self.state.registry.finishRevision();

            var graph = try SourceGraph.initAlloc(
                self.state.allocator,
                &self.state.registry,
                edges,
            );
            errdefer graph.deinit();
            var fingerprints = try SemanticFingerprint.FingerprintRevision.initAlloc(
                self.state.allocator,
                self.state.registry.knownCount(),
                fingerprint_entries,
            );
            errdefer fingerprints.deinit();
            var dirty = if (self.state.spare_dirty) |reusable| reuse: {
                self.state.spare_dirty = null;
                var value = reusable;
                value.beginEpoch();
                value.ensureSourceCapacity(self.state.registry.knownCount()) catch |err| {
                    self.state.spare_dirty = value;
                    return err;
                };
                break :reuse value;
            } else try DirtySourceSet.init(
                self.state.allocator,
                self.state.registry.knownCount(),
            );
            errdefer dirty.deinit();

            const settings_changed = if (self.state.frontend_fingerprint) |*committed|
                !committed.eql(&frontend_fingerprint)
            else
                true;
            if (settings_changed) {
                if (self.state.graph) |*previous_graph|
                    try dirty.markAll(previous_graph);
                try dirty.markAll(&graph);
            } else {
                var previous_seeds: std.ArrayList(DirtySourceSet.ChangedSource) = .empty;
                defer previous_seeds.deinit(self.state.allocator);
                var candidate_seeds: std.ArrayList(DirtySourceSet.ChangedSource) = .empty;
                defer candidate_seeds.deinit(self.state.allocator);
                try previous_seeds.ensureTotalCapacity(
                    self.state.allocator,
                    self.state.registry.changedIds().len,
                );
                try candidate_seeds.ensureTotalCapacity(
                    self.state.allocator,
                    self.state.registry.changedIds().len,
                );
                for (self.state.registry.changedIds()) |source| {
                    switch (self.state.registry.changeForId(source).?) {
                        .added => candidate_seeds.appendAssumeCapacity(.{
                            .source = source,
                            .categories = .all,
                        }),
                        .modified => {
                            const categories = changedCategories(
                                if (self.state.fingerprints) |*committed|
                                    committed.get(source)
                                else
                                    null,
                                fingerprints.get(source),
                            );
                            previous_seeds.appendAssumeCapacity(.{
                                .source = source,
                                .categories = categories,
                            });
                            candidate_seeds.appendAssumeCapacity(.{
                                .source = source,
                                .categories = categories,
                            });
                        },
                        .removed => previous_seeds.appendAssumeCapacity(.{
                            .source = source,
                            .categories = .all,
                        }),
                        .none, .unchanged => unreachable,
                    }
                }
                const dependency_masks = if (self.state.semantic) |semantic|
                    semantic.dependencyMasks()
                else
                    &.{};
                if (self.state.graph) |*previous_graph| {
                    try dirty.markSelectiveClosure(
                        previous_graph,
                        previous_seeds.items,
                        dependency_masks,
                    );
                } else std.debug.assert(previous_seeds.items.len == 0);
                try dirty.markSelectiveClosure(
                    &graph,
                    candidate_seeds.items,
                    dependency_masks,
                );
            }

            self.candidate_graph = graph;
            self.candidate_dirty = dirty;
            self.candidate_frontend_fingerprint = frontend_fingerprint;
            self.candidate_fingerprints = fingerprints;
            self.finished = true;
            return &self.candidate_graph.?;
        }

        /// Commits a graph-complete revision; a successful early diagnostic
        /// response that never assembled a graph leaves frontend state intact.
        pub fn commitCompleted(self: *Revision) void {
            if (self.closed) return;
            if (!self.finished) {
                self.abort();
                return;
            }
            self.state.registry.commitRevision();
            std.debug.assert(self.state.spare_dirty == null);
            self.state.spare_dirty = self.state.dirty;
            if (self.state.graph) |*graph| graph.deinit();
            self.state.graph = self.candidate_graph;
            self.candidate_graph = null;
            self.state.dirty = self.candidate_dirty;
            self.candidate_dirty = null;
            self.state.frontend_fingerprint = self.candidate_frontend_fingerprint;
            self.candidate_frontend_fingerprint = null;
            if (self.candidate_fingerprints) |fingerprints| {
                if (self.state.fingerprints) |*previous| previous.deinit();
                self.state.fingerprints = fingerprints;
                self.candidate_fingerprints = null;
            }
            self.state.current_request_key = self.request_key;
            if (self.candidate_semantic) |semantic| {
                if (self.state.semantic) |previous| previous.destroy();
                self.state.semantic = semantic;
                self.candidate_semantic = null;
            }
            if (self.candidate_syntax) |syntax| {
                if (self.state.syntax) |*previous| previous.deinit();
                self.state.syntax = syntax;
                self.candidate_syntax = null;
            }
            self.state.publishStatistics();
            self.closed = true;
            self.state.unlock();
        }

        pub fn abort(self: *Revision) void {
            if (self.closed) return;
            if (self.state.semantic) |previous_semantic|
                if (self.state.syntax) |*previous_syntax|
                    for (previous_syntax.sources) |source|
                        if (source) |value|
                            previous_semantic.bindTreeAssumeCapacity(&value.parsed.tree);
            if (self.candidate_semantic) |semantic| semantic.discard();
            self.candidate_semantic = null;
            if (self.candidate_syntax) |*syntax| syntax.deinit();
            self.candidate_syntax = null;
            if (self.candidate_dirty) |dirty| {
                std.debug.assert(self.state.spare_dirty == null);
                self.state.spare_dirty = dirty;
                self.candidate_dirty = null;
            }
            if (self.candidate_graph) |*graph| graph.deinit();
            if (self.candidate_fingerprints) |*fingerprints| fingerprints.deinit();
            self.candidate_fingerprints = null;
            self.state.registry.abortRevision();
            self.closed = true;
            self.state.unlock();
        }
    };
};

fn countFingerprints(
    fingerprints: *const SemanticFingerprint.FingerprintRevision,
) usize {
    var count: usize = 0;
    for (fingerprints.values) |value| count += @intFromBool(value != null);
    return count;
}

fn changedCategories(
    previous: ?*const SemanticFingerprint.SourceFingerprints,
    candidate: ?*const SemanticFingerprint.SourceFingerprints,
) SemanticFingerprint.CategoryMask {
    const before = previous orelse return .all;
    const after = candidate orelse return .all;
    return before.changedCategories(after);
}

test "frontend revisions commit registry graph and dirty state together" {
    var state = FrontendRevisionState.init(std.testing.allocator);
    defer state.deinit();

    var first = try state.beginRevision(null);
    defer first.abort();
    const b = (try first.registry().upsert("B.sol", "b")).id;
    const a = (try first.registry().upsert("A.sol", "a")).id;
    _ = try first.finish(&.{.{ .importer = b, .imported = a }}, testFingerprint(1), &.{});
    first.commitCompleted();

    var second = try state.beginRevision(null);
    defer second.abort();
    const before = (try second.registry().upsert("0.sol", "before")).id;
    const stable_a = (try second.registry().upsert("A.sol", "changed")).id;
    _ = try second.finish(&.{}, testFingerprint(1), &.{});
    second.commitCompleted();

    try std.testing.expectEqual(a, stable_a);
    try std.testing.expectEqual(@as(u32, 2), before.index());
    try std.testing.expectEqual(SourceRegistryModule.Change.modified, state.sourceChange(a).?);
    try std.testing.expectEqual(SourceRegistryModule.Change.removed, state.sourceChange(b).?);
    try std.testing.expect(state.isDirty(a));
    try std.testing.expect(state.isDirty(b));
    const statistics = state.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.revision);
    try std.testing.expectEqual(@as(usize, 2), statistics.active_sources);
    try std.testing.expectEqual(@as(usize, 3), statistics.known_sources);
    try std.testing.expectEqual(@as(usize, 2), statistics.graph_nodes);
}

test "failed frontend revision restores the preceding graph and ID assignment" {
    var state = FrontendRevisionState.init(std.testing.allocator);
    defer state.deinit();

    var first = try state.beginRevision(null);
    defer first.abort();
    const a = (try first.registry().upsert("A.sol", "a")).id;
    _ = try first.finish(&.{}, testFingerprint(1), &.{});
    first.commitCompleted();

    var failed = try state.beginRevision(null);
    _ = try failed.registry().upsert("A.sol", "failed edit");
    const staged = (try failed.registry().upsert("B.sol", "b")).id;
    _ = try failed.finish(&.{}, testFingerprint(2), &.{});
    failed.abort();

    try std.testing.expectEqual(@as(u64, 1), state.statistics().revision);
    try std.testing.expectEqual(SourceRegistryModule.Change.added, state.sourceChange(a).?);
    try std.testing.expect(state.sourceId("B.sol") == null);

    var retry = try state.beginRevision(null);
    defer retry.abort();
    const reused = (try retry.registry().upsert("C.sol", "c")).id;
    try std.testing.expectEqual(staged, reused);
}

test "frontend setting changes transactionally dirty both graph revisions" {
    var state = FrontendRevisionState.init(std.testing.allocator);
    defer state.deinit();

    var first = try state.beginRevision(null);
    defer first.abort();
    const dependency = (try first.registry().upsert("Dependency.sol", "dependency")).id;
    const importer = (try first.registry().upsert("Importer.sol", "importer")).id;
    _ = try first.finish(
        &.{.{ .importer = importer, .imported = dependency }},
        testFingerprint(1),
        &.{},
    );
    first.commitCompleted();

    var aborted = try state.beginRevision(null);
    _ = try aborted.registry().upsert("Dependency.sol", "dependency");
    _ = try aborted.registry().upsert("Importer.sol", "importer");
    _ = try aborted.finish(
        &.{.{ .importer = importer, .imported = dependency }},
        testFingerprint(2),
        &.{},
    );
    aborted.abort();

    var unchanged = try state.beginRevision(null);
    defer unchanged.abort();
    _ = try unchanged.registry().upsert("Dependency.sol", "dependency");
    _ = try unchanged.registry().upsert("Importer.sol", "importer");
    _ = try unchanged.finish(
        &.{.{ .importer = importer, .imported = dependency }},
        testFingerprint(1),
        &.{},
    );
    unchanged.commitCompleted();
    try std.testing.expect(!state.isDirty(dependency));
    try std.testing.expect(!state.isDirty(importer));

    var settings_changed = try state.beginRevision(null);
    defer settings_changed.abort();
    _ = try settings_changed.registry().upsert("Dependency.sol", "dependency");
    _ = try settings_changed.registry().upsert("Importer.sol", "importer");
    _ = try settings_changed.finish(
        &.{.{ .importer = importer, .imported = dependency }},
        testFingerprint(2),
        &.{},
    );
    settings_changed.commitCompleted();
    try std.testing.expect(state.isDirty(dependency));
    try std.testing.expect(state.isDirty(importer));
}

test "aborted semantic candidates force a fresh domain" {
    var state = FrontendRevisionState.init(std.testing.allocator);
    defer state.deinit();

    var first = try state.beginRevision(null);
    defer first.abort();
    const source = (try first.registry().upsert("A.sol", "contract A {}")).id;
    _ = try first.finish(&.{}, testFingerprint(1), &.{});
    const source_node_counts = [_]CompatibilityIds.SourceNodeCount{.{
        .source = source,
        .node_count = 1,
    }};
    const first_semantic = try first.createSemantic(&source_node_counts);
    _ = try first_semantic.buildCompatibilityIds(&source_node_counts);
    try first_semantic.beginAnalysis(EVMVersion.current());
    first_semantic.markAnalyzed();
    first.commitCompleted();

    var aborted = try state.beginRevision(null);
    _ = try aborted.registry().upsert("A.sol", "contract A {}");
    _ = try aborted.finish(&.{}, testFingerprint(1), &.{});
    const child = try aborted.createSemantic(&source_node_counts);
    try std.testing.expect(child.reusesPriorState());
    aborted.abort();
    try std.testing.expect(!state.semantic.?.reusableAsParent());

    var retry = try state.beginRevision(null);
    defer retry.abort();
    _ = try retry.registry().upsert("A.sol", "contract A {}");
    _ = try retry.finish(&.{}, testFingerprint(1), &.{});
    const fresh = try retry.createSemantic(&source_node_counts);
    try std.testing.expect(!fresh.reusesPriorState());
}

fn testFingerprint(byte: u8) FrontendFingerprint {
    return FrontendFingerprint.fromArray([_]u8{byte} ** FrontendFingerprint.size);
}
