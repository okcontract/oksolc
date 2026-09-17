// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Public incremental-compiler building blocks.

pub const key_hasher = @import("incremental/key_hasher.zig");
pub const identity = @import("incremental/identity.zig");
pub const compatibility_ids = @import("incremental/compatibility_ids.zig");
pub const source_registry = @import("incremental/source_registry.zig");
pub const source_graph = @import("incremental/source_graph.zig");
pub const syntax_revision = @import("incremental/syntax_revision.zig");
pub const semantic_fingerprint = @import("incremental/semantic_fingerprint.zig");
pub const semantic_revision = @import("incremental/semantic_revision.zig");
pub const frontend_revision_state = @import("incremental/frontend_revision_state.zig");
pub const phase_key = @import("incremental/phase_key.zig");
pub const artifact_store = @import("incremental/artifact_store.zig");
pub const compiler_session = @import("incremental/compiler_session.zig");
pub const backend_artifact = @import("incremental/backend_artifact.zig");
pub const backend_artifact_cache = @import("incremental/backend_artifact_cache.zig");
pub const sqlite_store = @import("incremental/sqlite_store.zig");
pub const sqlite_compiler_session = @import("incremental/sqlite_compiler_session.zig");

pub const SourceId = identity.SourceId;
pub const SourceKey = identity.SourceKey;
pub const SourceRegistry = source_registry.SourceRegistry;
pub const SourceEdge = source_graph.SourceEdge;
pub const SourceGraph = source_graph.SourceGraph;
pub const SyntaxRevision = syntax_revision.SyntaxRevision;
pub const SyntaxSource = syntax_revision.SyntaxSource;
pub const SemanticFingerprint = semantic_fingerprint.SourceFingerprints;
pub const SemanticRevision = semantic_revision.SemanticRevision;
pub const SourceSccId = source_graph.SourceSccId;
pub const DirtySourceSet = source_graph.DirtySourceSet;
pub const FrontendRevisionState = frontend_revision_state.FrontendRevisionState;
pub const ContractId = identity.ContractId;
pub const ContractKey = identity.ContractKey;
pub const LocalNodeId = identity.LocalNodeId;
pub const NodeRef = identity.NodeRef;
pub const CompatibilityIdProjection = compatibility_ids.CompatibilityIdProjection;
pub const ArtifactKind = phase_key.ArtifactKind;
pub const ArtifactKey = phase_key.ArtifactKey;
pub const CompilerFingerprint = phase_key.CompilerFingerprint;
pub const PhaseKeyBuilder = phase_key.PhaseKeyBuilder;
pub const PhaseFingerprints = phase_key.PhaseFingerprints;
pub const ArtifactRef = artifact_store.ArtifactRef;
pub const ArtifactStore = artifact_store.ArtifactStore;
pub const CacheLimits = artifact_store.CacheLimits;
pub const MemoryArtifactStore = artifact_store.MemoryArtifactStore;
pub const CompilerSession = compiler_session.CompilerSession;
pub const CompilerSessionOptions = compiler_session.CompilerSession.Options;
pub const SessionStatistics = compiler_session.SessionStatistics;
pub const BackendArtifactCache = backend_artifact_cache.BackendArtifactCache;
pub const SqliteStore = sqlite_store.SqliteStore;
pub const CacheAuthenticationKey = sqlite_store.AuthenticationKey;
pub const SqliteStoreOptions = sqlite_store.Options;
pub const SqliteStoreSummary = sqlite_store.Summary;
pub const SqlitePruneReport = sqlite_store.PruneReport;
pub const SqliteQueryId = sqlite_store.QueryId;
pub const SqliteDiagnosticOperation = sqlite_store.DiagnosticOperation;
pub const SqliteDiagnosticSnapshot = sqlite_store.DiagnosticSnapshot;
pub const SqliteDiagnosticSink = sqlite_store.DiagnosticSink;
pub const SqliteCompilerSession = sqlite_compiler_session.SqliteCompilerSession;
pub const SqliteCompilerSessionOptions = sqlite_compiler_session.SqliteCompilerSession.Options;
pub const PersistenceMode = sqlite_compiler_session.PersistenceMode;

test {
    _ = key_hasher;
    _ = identity;
    _ = compatibility_ids;
    _ = source_registry;
    _ = source_graph;
    _ = syntax_revision;
    _ = semantic_fingerprint;
    _ = semantic_revision;
    _ = frontend_revision_state;
    _ = phase_key;
    _ = artifact_store;
    _ = compiler_session;
    _ = backend_artifact;
    _ = backend_artifact_cache;
    _ = sqlite_store;
    _ = sqlite_compiler_session;
}
