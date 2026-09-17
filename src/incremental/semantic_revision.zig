// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit ownership for one generation of Solidity semantic state.

const std = @import("std");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const AST = @import("../libsolidity/ast/ast.zig");
const ASTAnnotations = @import("../libsolidity/ast/ast_annotations.zig");
const TypeProviderModule = @import("../libsolidity/ast/type_provider.zig");
const GlobalContextModule = @import("../libsolidity/analysis/global_context.zig");
const CallGraph = @import("../libsolidity/ast/call_graph.zig").CallGraph;
const SynchronizedAllocator = @import("../libsolutil/synchronized_allocator.zig").SynchronizedAllocator;
const CompatibilityIds = @import("compatibility_ids.zig");
const CompatibilityIdResolver = @import("../libsolidity/ast/compatibility_id_resolver.zig").CompatibilityIdResolver;
const SyntaxRevisionModule = @import("syntax_revision.zig");
const SourceGraph = @import("source_graph.zig").SourceGraph;
const SemanticFingerprint = @import("semantic_fingerprint.zig");

pub const TypeGenerationId = enum(u64) { _ };

/// Rebase periodically instead of allowing annotation lookup, destruction,
/// type-provider storage, and retained syntax to grow with session age.
pub const max_overlay_depth: usize = 32;

pub const SemanticCompleteness = enum {
    parsed,
    analyzing,
    analyzed,
    failed,
};

pub const DiagnosticPhase = enum {
    syntax,
    doc_string_parse,
    references,
    declaration_types,
    doc_string_type_validation,
    contract_level,
    type_check,
    doc_string_analysis,
    post_type,
    post_type_contract,
};

const StoredDiagnostic = struct {
    phase: DiagnosticPhase,
    source: AST.SourceId,
    diagnostic: Diagnostics.Diagnostic,
};

pub const ContractCallGraphs = struct {
    creation: CallGraph,
    deployed: CallGraph,

    fn destroy(self: *ContractCallGraphs, allocator: std.mem.Allocator) void {
        self.deployed.deinit();
        self.creation.deinit();
        allocator.destroy(self);
    }
};

/// A retained type-identity domain shared by copy-on-write semantic revisions.
/// The provider and global pseudo-declarations are append-only after
/// initialization, so every child revision observes one coherent pointer
/// generation while revision-local annotations remain transactional.
pub const SemanticDomain = struct {
    backing_allocator: std.mem.Allocator,
    synchronized_allocator: SynchronizedAllocator,
    reference_count: usize = 1,
    generation: TypeGenerationId,
    reuse_allowed: bool = true,
    evm_version: ?EVMVersion = null,
    type_provider: ?TypeProviderModule.TypeProvider = null,
    global_context: ?GlobalContextModule.GlobalContext = null,
    retained_syntax: std.ArrayList(*SyntaxRevisionModule.SyntaxSource) = .empty,

    fn create(
        allocator: std.mem.Allocator,
        generation: TypeGenerationId,
    ) std.mem.Allocator.Error!*SemanticDomain {
        const result = try allocator.create(SemanticDomain);
        result.* = .{
            .backing_allocator = allocator,
            .synchronized_allocator = SynchronizedAllocator.init(allocator),
            .generation = generation,
        };
        return result;
    }

    fn retain(self: *SemanticDomain) void {
        std.debug.assert(self.reference_count != std.math.maxInt(usize));
        self.reference_count += 1;
    }

    fn release(self: *SemanticDomain) void {
        std.debug.assert(self.reference_count != 0);
        self.reference_count -= 1;
        if (self.reference_count != 0) return;
        if (self.global_context) |*context| context.deinit();
        if (self.type_provider) |*provider| provider.deinit();
        for (self.retained_syntax.items) |source| source.release();
        self.retained_syntax.deinit(self.domainAllocator());
        self.backing_allocator.destroy(self);
    }

    fn domainAllocator(self: *SemanticDomain) std.mem.Allocator {
        return self.synchronized_allocator.allocator();
    }

    fn ensureAnalysis(
        self: *SemanticDomain,
        evm_version: EVMVersion,
    ) (TypeProviderModule.ProviderError || GlobalContextModule.GlobalContextError || error{
        IncompatibleSemanticDomain,
    })!void {
        if (self.evm_version) |initialized| {
            if (!initialized.eql(evm_version)) return error.IncompatibleSemanticDomain;
            std.debug.assert(self.type_provider != null);
            std.debug.assert(self.global_context != null);
            return;
        }
        const allocator = self.domainAllocator();
        self.type_provider = try TypeProviderModule.TypeProvider.init(allocator);
        errdefer {
            self.type_provider.?.deinit();
            self.type_provider = null;
        }
        self.global_context = try GlobalContextModule.GlobalContext.init(
            allocator,
            &self.type_provider.?,
            evm_version,
        );
        self.evm_version = evm_version;
    }

    fn retainSyntaxSource(
        self: *SemanticDomain,
        source: *SyntaxRevisionModule.SyntaxSource,
    ) std.mem.Allocator.Error!void {
        for (self.retained_syntax.items) |retained|
            if (retained == source) return;
        try self.retained_syntax.append(self.domainAllocator(), source);
        source.retain();
    }
};

/// All type pointers and annotation values in a semantic revision belong to
/// the same nominal generation. They are never mixed with another provider.
pub const SemanticRevision = struct {
    backing_allocator: std.mem.Allocator,
    synchronized_allocator: SynchronizedAllocator,
    reference_count: usize = 1,
    parent: ?*SemanticRevision = null,
    domain: *SemanticDomain,
    generation: TypeGenerationId,
    completeness: SemanticCompleteness = .parsed,
    analyzed_sources: usize = 0,
    reused_sources: usize = 0,
    overlay_depth: usize = 0,
    annotations: *ASTAnnotations.AnnotationTable,
    call_graphs: std.ArrayList(*ContractCallGraphs) = .empty,
    diagnostics: std.ArrayList(StoredDiagnostic) = .empty,
    dependency_masks: std.ArrayList(SemanticFingerprint.DependencyMaskEntry) = .empty,
    compatibility_ids: ?CompatibilityIds.CompatibilityIdProjection = null,

    pub fn create(
        allocator: std.mem.Allocator,
        generation: TypeGenerationId,
    ) std.mem.Allocator.Error!*SemanticRevision {
        const domain = try SemanticDomain.create(allocator, generation);
        errdefer domain.release();
        return createWithDomain(
            allocator,
            domain,
            null,
            0,
            &.{},
        );
    }

    pub fn createChild(
        allocator: std.mem.Allocator,
        parent: *SemanticRevision,
        source_capacity: usize,
        masked_sources: []const AST.SourceId,
    ) (std.mem.Allocator.Error || error{
        ParentSemanticRevisionIncomplete,
        ParentSemanticRevisionNotReusable,
    })!*SemanticRevision {
        if (parent.completeness != .analyzed)
            return error.ParentSemanticRevisionIncomplete;
        if (!parent.domain.reuse_allowed or parent.overlay_depth >= max_overlay_depth)
            return error.ParentSemanticRevisionNotReusable;
        parent.retain();
        errdefer parent.destroy();
        parent.domain.retain();
        errdefer parent.domain.release();
        return createWithDomain(
            allocator,
            parent.domain,
            parent,
            source_capacity,
            masked_sources,
        );
    }

    fn createWithDomain(
        allocator: std.mem.Allocator,
        domain: *SemanticDomain,
        parent: ?*SemanticRevision,
        source_capacity: usize,
        masked_sources: []const AST.SourceId,
    ) std.mem.Allocator.Error!*SemanticRevision {
        const result = try allocator.create(SemanticRevision);
        errdefer allocator.destroy(result);
        result.* = undefined;
        result.backing_allocator = allocator;
        result.synchronized_allocator = SynchronizedAllocator.init(allocator);
        const semantic_allocator = result.synchronized_allocator.allocator();
        const annotations = if (parent) |previous|
            try ASTAnnotations.AnnotationTable.createOverlay(
                semantic_allocator,
                previous.annotations,
                source_capacity,
                masked_sources,
            )
        else
            try ASTAnnotations.AnnotationTable.create(semantic_allocator);
        result.* = .{
            .backing_allocator = allocator,
            .synchronized_allocator = result.synchronized_allocator,
            .parent = parent,
            .domain = domain,
            .generation = domain.generation,
            .overlay_depth = if (parent) |previous| previous.overlay_depth + 1 else 0,
            .annotations = annotations,
        };
        return result;
    }

    pub fn destroy(self: *SemanticRevision) void {
        std.debug.assert(self.reference_count != 0);
        self.reference_count -= 1;
        if (self.reference_count != 0) return;
        const semantic_allocator = self.semanticAllocator();
        for (self.call_graphs.items) |graphs| graphs.destroy(semantic_allocator);
        self.call_graphs.deinit(semantic_allocator);
        self.dependency_masks.deinit(semantic_allocator);
        for (self.diagnostics.items) |*diagnostic| diagnostic.diagnostic.deinit();
        self.diagnostics.deinit(self.annotations.allocator());
        self.annotations.destroy();
        if (self.compatibility_ids) |*compatibility_ids| compatibility_ids.deinit();
        const allocator = self.backing_allocator;
        const parent = self.parent;
        const domain = self.domain;
        allocator.destroy(self);
        domain.release();
        if (parent) |previous| previous.destroy();
    }

    pub fn retain(self: *SemanticRevision) void {
        std.debug.assert(self.reference_count != std.math.maxInt(usize));
        self.reference_count += 1;
    }

    /// Discarding a child may leave append-only provider state pointing into
    /// syntax that was never committed. Prevent another child from extending
    /// that domain; the next candidate starts a fresh generation and releases
    /// this bounded failed-candidate residue when it commits.
    pub fn discard(self: *SemanticRevision) void {
        self.domain.reuse_allowed = false;
        self.destroy();
    }

    pub fn reusableAsParent(self: *const SemanticRevision) bool {
        return self.completeness == .analyzed and
            self.domain.reuse_allowed and
            self.overlay_depth < max_overlay_depth;
    }

    pub fn reusesPriorState(self: *const SemanticRevision) bool {
        return self.parent != null;
    }

    pub fn overlayDepth(self: *const SemanticRevision) usize {
        return self.overlay_depth;
    }

    pub fn retainedSyntaxSourceCount(self: *const SemanticRevision) usize {
        return self.domain.retained_syntax.items.len;
    }

    pub fn dependencyMasks(
        self: *const SemanticRevision,
    ) []const SemanticFingerprint.DependencyMaskEntry {
        return self.dependency_masks.items;
    }

    /// Initializes one sorted entry for every direct import. Merely importing
    /// a source consumes its exported-symbol surface; semantic references may
    /// widen the entry to all categories after analysis.
    pub fn initializeDependencyMasks(
        self: *SemanticRevision,
        graph: *const SourceGraph,
    ) std.mem.Allocator.Error!void {
        std.debug.assert(self.dependency_masks.items.len == 0);
        try self.dependency_masks.ensureTotalCapacity(
            self.semanticAllocator(),
            graph.edgeCount(),
        );
        for (graph.activeSources()) |importer|
            for (graph.imports(importer)) |imported|
                self.dependency_masks.appendAssumeCapacity(.{
                    .importer = importer,
                    .imported = imported,
                });
    }

    /// A resolved cross-source reference consumes every retained semantic
    /// surface of its direct dependency. If resolution reached a transitive
    /// source, conservatively widen all direct imports of the referencing
    /// source because the exact re-export path is not represented here.
    pub fn markDependencyUsed(
        self: *SemanticRevision,
        graph: *const SourceGraph,
        importer: AST.SourceId,
        referenced: AST.SourceId,
    ) void {
        if (importer == referenced) return;
        if (self.markDependencyPath(graph, importer, referenced)) return;
        if (!graph.isActive(referenced)) return;
        for (self.dependency_masks.items) |*entry| {
            if (entry.importer == importer) entry.categories = .all;
        }
    }

    /// The SCC condensation graph is acyclic, so recursively choosing the
    /// first sorted path requires no per-reference visited allocation. Edges
    /// inside one SCC need no mask widening because invalidation is atomic.
    fn markDependencyPath(
        self: *SemanticRevision,
        graph: *const SourceGraph,
        current: AST.SourceId,
        target: AST.SourceId,
    ) bool {
        const current_scc = graph.sourceScc(current) orelse return false;
        const target_scc = graph.sourceScc(target) orelse return false;
        if (current_scc == target_scc) return true;
        for (graph.imports(current)) |imported| {
            if (graph.sourceScc(imported).? == current_scc) continue;
            if (!self.markDependencyPath(graph, imported, target)) continue;
            for (self.dependency_masks.items) |*entry| {
                if (entry.importer == current and entry.imported == imported) {
                    entry.categories = .all;
                    return true;
                }
            }
            return false;
        }
        return false;
    }

    pub fn compatibilityIdsMatch(
        self: *const SemanticRevision,
        source_node_counts: []const CompatibilityIds.SourceNodeCount,
    ) bool {
        const compatibility_ids = self.compatibility_ids orelse return false;
        return compatibility_ids.matches(source_node_counts);
    }

    pub fn semanticAllocator(self: *SemanticRevision) std.mem.Allocator {
        return self.synchronized_allocator.allocator();
    }

    /// Type objects and global-context caches may retain syntax pointers even
    /// after a failed child analysis. The shared domain therefore keeps every
    /// syntax generation it has observed alive until the domain is released.
    pub fn retainSyntaxSource(
        self: *SemanticRevision,
        source: *SyntaxRevisionModule.SyntaxSource,
    ) std.mem.Allocator.Error!void {
        try self.domain.retainSyntaxSource(source);
    }

    pub fn adoptCallGraphs(
        self: *SemanticRevision,
        creation: *CallGraph,
        deployed: *CallGraph,
    ) std.mem.Allocator.Error!*ContractCallGraphs {
        const semantic_allocator = self.semanticAllocator();
        const owned = try semantic_allocator.create(ContractCallGraphs);
        errdefer semantic_allocator.destroy(owned);
        try self.call_graphs.append(semantic_allocator, owned);
        owned.* = .{ .creation = creation.*, .deployed = deployed.* };
        creation.* = undefined;
        deployed.* = undefined;
        return owned;
    }

    pub fn buildCompatibilityIds(
        self: *SemanticRevision,
        source_node_counts: []const CompatibilityIds.SourceNodeCount,
    ) (CompatibilityIds.BuildError || error{CompatibilityIdsAlreadyBuilt})!CompatibilityIdResolver {
        if (self.compatibility_ids != null) return error.CompatibilityIdsAlreadyBuilt;
        self.compatibility_ids = try CompatibilityIds.CompatibilityIdProjection.initAlloc(
            self.semanticAllocator(),
            source_node_counts,
        );
        self.annotations.setCompatibilityIds(&self.compatibility_ids.?);
        return CompatibilityIdResolver.init(&self.compatibility_ids.?);
    }

    pub fn bindTree(
        self: *SemanticRevision,
        tree: *AST.Tree,
    ) std.mem.Allocator.Error!void {
        try self.annotations.bindTree(tree);
    }

    pub fn bindTreeAssumeCapacity(self: *SemanticRevision, tree: *AST.Tree) void {
        self.annotations.bindTreeAssumeCapacity(tree);
    }

    pub fn replayDiagnostics(
        self: *SemanticRevision,
        phase: DiagnosticPhase,
        source: AST.SourceId,
        reporter: *Diagnostics.ErrorReporter,
    ) Diagnostics.ReportError!void {
        const previous = self.parent orelse return;
        for (previous.diagnostics.items) |*stored| {
            if (stored.phase != phase or stored.source != source) continue;
            const diagnostic = &stored.diagnostic;
            try reporter.reportWithSecondary(
                diagnostic.error_id,
                diagnostic.error_type,
                diagnostic.location orelse .{},
                &diagnostic.secondary,
                diagnostic.description,
            );
        }
    }

    pub fn recordDiagnostics(
        self: *SemanticRevision,
        phase: DiagnosticPhase,
        source: AST.SourceId,
        diagnostics: []const Diagnostics.Diagnostic,
    ) std.mem.Allocator.Error!void {
        const allocator = self.annotations.allocator();
        for (diagnostics) |*diagnostic| {
            var cloned = try diagnostic.clone(allocator);
            errdefer cloned.deinit();
            try self.diagnostics.append(allocator, .{
                .phase = phase,
                .source = source,
                .diagnostic = cloned,
            });
        }
    }

    pub fn beginAnalysis(
        self: *SemanticRevision,
        evm_version: EVMVersion,
    ) (TypeProviderModule.ProviderError || GlobalContextModule.GlobalContextError || error{
        AnalysisAlreadyStarted,
        IncompatibleSemanticDomain,
    })!void {
        if (self.completeness != .parsed)
            return error.AnalysisAlreadyStarted;
        try self.domain.ensureAnalysis(evm_version);
        self.completeness = .analyzing;
    }

    pub fn typeProvider(
        self: *SemanticRevision,
    ) error{AnalysisNotStarted}!*TypeProviderModule.TypeProvider {
        if (self.completeness == .parsed) return error.AnalysisNotStarted;
        return if (self.domain.type_provider) |*provider| provider else error.AnalysisNotStarted;
    }

    pub fn globalContext(
        self: *SemanticRevision,
    ) error{AnalysisNotStarted}!*GlobalContextModule.GlobalContext {
        if (self.completeness == .parsed) return error.AnalysisNotStarted;
        return if (self.domain.global_context) |*context| context else error.AnalysisNotStarted;
    }

    pub fn markAnalyzed(self: *SemanticRevision) void {
        std.debug.assert(self.completeness == .analyzing);
        self.completeness = .analyzed;
    }

    pub fn setSourceCounts(
        self: *SemanticRevision,
        analyzed_sources: usize,
        reused_sources: usize,
    ) void {
        std.debug.assert(self.completeness == .analyzing);
        self.analyzed_sources = analyzed_sources;
        self.reused_sources = reused_sources;
    }

    pub fn markFailed(self: *SemanticRevision) void {
        std.debug.assert(self.completeness != .analyzed);
        self.completeness = .failed;
    }
};

test "semantic revision owns annotations and one type generation" {
    const semantic = try SemanticRevision.create(
        std.testing.allocator,
        @enumFromInt(9),
    );
    defer semantic.destroy();
    var tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(2),
        "value",
        "A.sol",
    );
    defer tree.deinit();
    const node = try tree.createNode(.{}, .{ .identifier = .{ .name = "value" } });
    try semantic.bindTree(&tree);
    _ = try ASTAnnotations.ensure(&tree, node);
    try semantic.beginAnalysis(EVMVersion.current());
    _ = (try semantic.typeProvider()).boolean();
    semantic.markAnalyzed();
    try std.testing.expectEqual(SemanticCompleteness.analyzed, semantic.completeness);
}

test "semantic child revisions share types and copy dirty annotations" {
    const parent = try SemanticRevision.create(
        std.testing.allocator,
        @enumFromInt(17),
    );
    defer parent.destroy();
    var clean_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(1),
        "clean",
        "Clean.sol",
    );
    defer clean_tree.deinit();
    const clean = try clean_tree.createNode(.{}, .{ .identifier = .{ .name = "clean" } });
    var dirty_tree = try AST.Tree.initWithSourceId(
        std.testing.allocator,
        AST.SourceId.init(2),
        "dirty",
        "Dirty.sol",
    );
    defer dirty_tree.deinit();
    const dirty = try dirty_tree.createNode(.{}, .{ .identifier = .{ .name = "dirty" } });
    try parent.bindTree(&clean_tree);
    try parent.bindTree(&dirty_tree);
    const clean_parent = try ASTAnnotations.ensure(&clean_tree, clean);
    const dirty_parent = try ASTAnnotations.ensure(&dirty_tree, dirty);
    try parent.beginAnalysis(EVMVersion.current());
    const boolean = (try parent.typeProvider()).boolean();
    parent.markAnalyzed();

    const child = try SemanticRevision.createChild(
        std.testing.allocator,
        parent,
        3,
        &.{AST.SourceId.init(2)},
    );
    try child.bindTree(&clean_tree);
    try child.bindTree(&dirty_tree);
    try child.beginAnalysis(EVMVersion.current());
    try std.testing.expect((try child.typeProvider()).boolean() == boolean);
    try std.testing.expect(ASTAnnotations.annotation(clean) == clean_parent);
    try std.testing.expect(ASTAnnotations.annotation(dirty) == null);
    try std.testing.expect((try ASTAnnotations.ensure(&dirty_tree, dirty)) != dirty_parent);
    child.markAnalyzed();
    child.destroy();

    parent.bindTreeAssumeCapacity(&clean_tree);
    parent.bindTreeAssumeCapacity(&dirty_tree);
    try std.testing.expect(ASTAnnotations.annotation(clean) == clean_parent);
    try std.testing.expect(ASTAnnotations.annotation(dirty) == dirty_parent);
}

test "semantic overlay chains have a fixed maximum depth" {
    var current = try SemanticRevision.create(
        std.testing.allocator,
        @enumFromInt(31),
    );
    defer {
        current.destroy();
    }
    try current.beginAnalysis(EVMVersion.current());
    current.markAnalyzed();

    for (0..max_overlay_depth) |_| {
        const child = try SemanticRevision.createChild(
            std.testing.allocator,
            current,
            0,
            &.{},
        );
        try child.beginAnalysis(EVMVersion.current());
        child.markAnalyzed();
        current.destroy();
        current = child;
    }

    try std.testing.expectEqual(max_overlay_depth, current.overlayDepth());
    try std.testing.expect(!current.reusableAsParent());
    try std.testing.expectError(
        error.ParentSemanticRevisionNotReusable,
        SemanticRevision.createChild(std.testing.allocator, current, 0, &.{}),
    );
}

test "discarded semantic children prevent further domain extension" {
    const parent = try SemanticRevision.create(
        std.testing.allocator,
        @enumFromInt(47),
    );
    defer parent.destroy();
    try parent.beginAnalysis(EVMVersion.current());
    parent.markAnalyzed();

    const discarded = try SemanticRevision.createChild(
        std.testing.allocator,
        parent,
        0,
        &.{},
    );
    discarded.discard();

    try std.testing.expect(!parent.reusableAsParent());
    try std.testing.expectError(
        error.ParentSemanticRevisionNotReusable,
        SemanticRevision.createChild(std.testing.allocator, parent, 0, &.{}),
    );
}
