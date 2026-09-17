// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Long-lived compiler session with a process-local exact-response cache.

const std = @import("std");
const common = @import("common");
const ArtifactStoreModule = @import("artifact_store.zig");
const PhaseKey = @import("phase_key.zig");
const Libsolc = @import("../libsolc/libsolc.zig");
const Profiler = @import("../libsolutil/profiler.zig").Profiler;
const ObjectOptimizerModule = @import("../libyul/object_optimizer.zig");
const ObjectOptimizer = ObjectOptimizerModule.ObjectOptimizer;
const BackendCacheModule = @import("backend_artifact_cache.zig");
const BackendArtifactCache = BackendCacheModule.BackendArtifactCache;
const FrontendRevisionStateModule = @import("frontend_revision_state.zig");
const FrontendRevisionState = FrontendRevisionStateModule.FrontendRevisionState;
const SemanticRevisionModule = @import("semantic_revision.zig");
const SourceChange = @import("source_registry.zig").Change;
const AST = @import("../libsolidity/ast/ast.zig");

const MemoryArtifactStore = ArtifactStoreModule.MemoryArtifactStore;

pub const SessionStatistics = struct {
    requests: u64,
    reentrant_rejections: u64,
    cacheable_requests: u64,
    bypassed_requests: u64,
    store_failures: u64,
    memory_response_hits: u64,
    response_misses: u64,
    coherence_rejections: u64,
    persistent_hits: u64,
    persistent_misses: u64,
    memory: ArtifactStoreModule.MemoryStoreStatistics,
    optimizer: ObjectOptimizerModule.Statistics,
    backend: BackendCacheModule.Statistics,
    frontend: FrontendRevisionStateModule.Statistics,
};

/// Stateful Zig API. The existing stateless dispatcher and C ABI remain
/// unchanged and serve as the clean-compilation oracle.
///
/// Synchronous source, progress, and backing-store diagnostic callbacks may
/// call `statistics()`. A direct callback attempt to compile through this same
/// session returns `error.ReentrantCompilation`; querying its live
/// `frontend_state` remains unsupported because the active Solidity revision
/// may retain its locks.
/// Ordinary concurrent compilations and callback compilation through a
/// different session remain supported.
pub const CompilerSession = struct {
    pub const Options = struct {
        response_cache_limits: ArtifactStoreModule.CacheLimits =
            ArtifactStoreModule.default_memory_limits,
        optimizer_cache_limits: ArtifactStoreModule.CacheLimits =
            ObjectOptimizerModule.default_memory_limits,
        backend_cache_limits: ArtifactStoreModule.CacheLimits =
            BackendCacheModule.default_memory_limits,
    };

    compiler_fingerprint: PhaseKey.CompilerFingerprint,
    memory_store: MemoryArtifactStore,
    object_optimizer: ObjectOptimizer,
    backend_cache: BackendArtifactCache,
    frontend_state: FrontendRevisionState,
    backing_store: ?ArtifactStoreModule.ArtifactStore = null,
    dispatcher: Libsolc.Dispatcher = .{},
    request_count: std.atomic.Value(u64) = .init(0),
    reentrant_rejection_count: std.atomic.Value(u64) = .init(0),
    cacheable_request_count: std.atomic.Value(u64) = .init(0),
    bypassed_request_count: std.atomic.Value(u64) = .init(0),
    store_failure_count: std.atomic.Value(u64) = .init(0),
    memory_response_hit_count: std.atomic.Value(u64) = .init(0),
    response_miss_count: std.atomic.Value(u64) = .init(0),
    coherence_rejection_count: std.atomic.Value(u64) = .init(0),
    persistent_hit_count: std.atomic.Value(u64) = .init(0),
    persistent_miss_count: std.atomic.Value(u64) = .init(0),

    pub fn init(allocator: std.mem.Allocator) CompilerSession {
        return initWithOptions(allocator, .{});
    }

    pub fn initWithOptions(
        allocator: std.mem.Allocator,
        options: Options,
    ) CompilerSession {
        return initWithFingerprintAndOptions(
            allocator,
            PhaseKey.CompilerFingerprint.current(),
            options,
        );
    }

    pub fn initWithFingerprint(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
    ) CompilerSession {
        return initWithFingerprintAndOptions(allocator, compiler_fingerprint, .{});
    }

    pub fn initWithFingerprintAndOptions(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
        options: Options,
    ) CompilerSession {
        return .{
            .compiler_fingerprint = compiler_fingerprint,
            .memory_store = MemoryArtifactStore.initWithLimits(
                allocator,
                options.response_cache_limits,
            ),
            .object_optimizer = ObjectOptimizer.initWithFingerprintAndLimits(
                allocator,
                compiler_fingerprint,
                options.optimizer_cache_limits,
            ),
            .backend_cache = BackendArtifactCache.initWithFingerprintAndLimits(
                allocator,
                compiler_fingerprint,
                options.backend_cache_limits,
            ),
            .frontend_state = FrontendRevisionState.init(allocator),
        };
    }

    pub fn initWithBackingStore(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
        backing_store: ArtifactStoreModule.ArtifactStore,
    ) PhaseKey.PersistentFingerprintError!CompilerSession {
        return initWithBackingStoreAndOptions(
            allocator,
            compiler_fingerprint,
            backing_store,
            .{},
        );
    }

    pub fn initWithBackingStoreAndOptions(
        allocator: std.mem.Allocator,
        compiler_fingerprint: PhaseKey.CompilerFingerprint,
        backing_store: ArtifactStoreModule.ArtifactStore,
        options: Options,
    ) PhaseKey.PersistentFingerprintError!CompilerSession {
        if (!compiler_fingerprint.isPersistentSafe())
            return error.UnidentifiedCompilerBuild;
        return .{
            .compiler_fingerprint = compiler_fingerprint,
            .memory_store = MemoryArtifactStore.initWithLimits(
                allocator,
                options.response_cache_limits,
            ),
            .object_optimizer = try ObjectOptimizer.initWithBackingStoreAndLimits(
                allocator,
                compiler_fingerprint,
                backing_store,
                options.optimizer_cache_limits,
            ),
            .backend_cache = try BackendArtifactCache.initWithBackingStoreAndLimits(
                allocator,
                compiler_fingerprint,
                backing_store,
                options.backend_cache_limits,
            ),
            .frontend_state = FrontendRevisionState.init(allocator),
            .backing_store = backing_store,
        };
    }

    /// No compilation may remain active when the session is destroyed.
    pub fn deinit(self: *CompilerSession) void {
        self.frontend_state.deinit();
        self.backend_cache.deinit();
        self.object_optimizer.deinit();
        self.memory_store.deinit();
        self.* = undefined;
    }

    pub fn compiler(self: *CompilerSession) common.standard_json.Compiler {
        return .{
            .context = self,
            .compile_fn = compileOpaque,
        };
    }

    /// Compile one Standard JSON request while retaining reusable state for
    /// later calls. The returned output owns its bytes and must be deinitialized.
    pub fn compile(
        self: *CompilerSession,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
    ) common.standard_json.CompileError!common.standard_json.Output {
        return self.compileRequest(allocator, request);
    }

    /// Profiling configuration must not be changed concurrently with a
    /// compilation. The profiler itself already serializes worker updates.
    pub fn setOptimizerProfiler(self: *CompilerSession, profiler: ?*Profiler) void {
        self.dispatcher.optimizer_profiler = profiler;
    }

    /// Callback-safe statistics. The frontend fields are one coherent snapshot
    /// of the last committed revision; other counters may advance concurrently.
    pub fn statistics(self: *CompilerSession) SessionStatistics {
        return .{
            .requests = self.request_count.load(.monotonic),
            .reentrant_rejections = self.reentrant_rejection_count.load(.monotonic),
            .cacheable_requests = self.cacheable_request_count.load(.monotonic),
            .bypassed_requests = self.bypassed_request_count.load(.monotonic),
            .store_failures = self.store_failure_count.load(.monotonic),
            .memory_response_hits = self.memory_response_hit_count.load(.monotonic),
            .response_misses = self.response_miss_count.load(.monotonic),
            .coherence_rejections = self.coherence_rejection_count.load(.monotonic),
            .persistent_hits = self.persistent_hit_count.load(.monotonic),
            .persistent_misses = self.persistent_miss_count.load(.monotonic),
            .memory = self.memory_store.statistics(),
            .optimizer = self.object_optimizer.statistics(),
            .backend = self.backend_cache.statistics(),
            .frontend = self.frontend_state.statistics(),
        };
    }

    fn compileOpaque(
        context: *anyopaque,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
    ) common.standard_json.CompileError!common.standard_json.Output {
        const self: *CompilerSession = @ptrCast(@alignCast(context));
        return self.compileRequest(allocator, request);
    }

    fn compileRequest(
        self: *CompilerSession,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
    ) common.standard_json.CompileError!common.standard_json.Output {
        if (compilationSessionIsActive(self)) {
            _ = self.reentrant_rejection_count.fetchAdd(1, .monotonic);
            return error.ReentrantCompilation;
        }
        var session_frame: CompilationSessionFrame = .{
            .session = self,
            .parent = active_compilation_session,
        };
        active_compilation_session = &session_frame;
        defer {
            std.debug.assert(active_compilation_session == &session_frame);
            active_compilation_session = session_frame.parent;
        }
        _ = self.request_count.fetchAdd(1, .monotonic);

        const reference = exactResponseReference(
            self.compiler_fingerprint,
            request.input,
        );

        // Progress is always observable.
        // Solidity may consult a source loader for imports even when every
        // source entry has inline content. Other languages can observe it
        // through explicit source URLs.
        if (request.progress != null or
            (request.source_loader != null and requestMayObserveSourceLoader(
                allocator,
                request.input,
            )))
        {
            _ = self.bypassed_request_count.fetchAdd(1, .monotonic);
            return self.dispatcher.compileWithCachesAndFrontendState(
                allocator,
                request,
                &self.object_optimizer,
                &self.backend_cache,
                &self.frontend_state,
                reference.key,
            );
        }
        _ = self.cacheable_request_count.fetchAdd(1, .monotonic);

        var requires_frontend_coherence: ?bool = null;
        cache_lookup: {
            // Classify only a request with a known candidate response. This
            // avoids a second full input scan on ordinary changed requests.
            // The probe is advisory, so every read still handles a race miss.
            if (self.memory_store.contains(reference)) {
                const requires = requestRequiresFrontendCoherence(allocator, request.input);
                requires_frontend_coherence = requires;
                if (requires and !exactResponseIsCoherent(&self.frontend_state, reference.key)) {
                    _ = self.coherence_rejection_count.fetchAdd(1, .monotonic);
                    break :cache_lookup;
                }
            }

            var cached = self.memory_store.getAlloc(allocator, reference) catch blk: {
                _ = self.store_failure_count.fetchAdd(1, .monotonic);
                break :blk null;
            };
            if (cached) |*artifact| {
                const requires = requires_frontend_coherence orelse requires: {
                    const value = requestRequiresFrontendCoherence(allocator, request.input);
                    requires_frontend_coherence = value;
                    break :requires value;
                };
                if (requires) {
                    var hit_guard = self.frontend_state.lockExactResponse(reference.key);
                    if (hit_guard.coherent) {
                        defer hit_guard.release();
                        _ = self.memory_response_hit_count.fetchAdd(1, .monotonic);
                        return .{
                            .allocator = allocator,
                            .bytes = artifact.takePayload(),
                            .execution = .{ .backend = .zig },
                        };
                    }
                    hit_guard.release();
                    _ = self.coherence_rejection_count.fetchAdd(1, .monotonic);
                    artifact.deinit();
                    break :cache_lookup;
                } else {
                    _ = self.memory_response_hit_count.fetchAdd(1, .monotonic);
                    return .{
                        .allocator = allocator,
                        .bytes = artifact.takePayload(),
                        .execution = .{ .backend = .zig },
                    };
                }
            }

            const backing_store = self.backing_store orelse break :cache_lookup;
            const requires = requires_frontend_coherence orelse requires: {
                const value = requestRequiresFrontendCoherence(allocator, request.input);
                requires_frontend_coherence = value;
                break :requires value;
            };
            if (requires and !exactResponseIsCoherent(&self.frontend_state, reference.key)) {
                // Only an incoherent revision needs the non-copying probe.
                // Coherent hits and process restarts retain the former single
                // store read instead of paying a second persistent query.
                const persistent_present = backing_store.contains(reference) catch {
                    _ = self.store_failure_count.fetchAdd(1, .monotonic);
                    _ = self.persistent_miss_count.fetchAdd(1, .monotonic);
                    break :cache_lookup;
                };
                if (persistent_present)
                    _ = self.coherence_rejection_count.fetchAdd(1, .monotonic);
                _ = self.persistent_miss_count.fetchAdd(1, .monotonic);
                break :cache_lookup;
            }

            var persisted = backing_store.getAlloc(allocator, reference) catch blk: {
                _ = self.store_failure_count.fetchAdd(1, .monotonic);
                break :blk null;
            };
            if (persisted) |*artifact| {
                if (requires) {
                    var hit_guard = self.frontend_state.lockExactResponse(reference.key);
                    if (hit_guard.coherent) {
                        defer hit_guard.release();
                        _ = self.persistent_hit_count.fetchAdd(1, .monotonic);
                        self.memory_store.put(
                            reference,
                            artifact.payload,
                            artifact.dependencies,
                        ) catch {
                            _ = self.store_failure_count.fetchAdd(1, .monotonic);
                        };
                        return .{
                            .allocator = allocator,
                            .bytes = artifact.takePayload(),
                            .execution = .{ .backend = .zig },
                        };
                    }
                    hit_guard.release();
                    _ = self.coherence_rejection_count.fetchAdd(1, .monotonic);
                    artifact.deinit();
                } else {
                    _ = self.persistent_hit_count.fetchAdd(1, .monotonic);
                    self.memory_store.put(
                        reference,
                        artifact.payload,
                        artifact.dependencies,
                    ) catch {
                        _ = self.store_failure_count.fetchAdd(1, .monotonic);
                    };
                    return .{
                        .allocator = allocator,
                        .bytes = artifact.takePayload(),
                        .execution = .{ .backend = .zig },
                    };
                }
            }
            _ = self.persistent_miss_count.fetchAdd(1, .monotonic);
        }

        _ = self.response_miss_count.fetchAdd(1, .monotonic);
        const output = try self.dispatcher.compileWithCachesAndFrontendState(
            allocator,
            request,
            &self.object_optimizer,
            &self.backend_cache,
            &self.frontend_state,
            reference.key,
        );
        self.memory_store.put(reference, output.bytes, &.{}) catch {
            _ = self.store_failure_count.fetchAdd(1, .monotonic);
        };
        if (self.backing_store) |backing_store| {
            backing_store.put(reference, output.bytes, &.{}) catch {
                _ = self.store_failure_count.fetchAdd(1, .monotonic);
            };
        }
        return output;
    }
};

const CompilationSessionFrame = struct {
    session: *CompilerSession,
    parent: ?*CompilationSessionFrame,
};

threadlocal var active_compilation_session: ?*CompilationSessionFrame = null;

fn compilationSessionIsActive(session: *CompilerSession) bool {
    var frame = active_compilation_session;
    while (frame) |current| : (frame = current.parent)
        if (current.session == session) return true;
    return false;
}

fn exactResponseReference(
    compiler_fingerprint: PhaseKey.CompilerFingerprint,
    input: []const u8,
) ArtifactStoreModule.ArtifactRef {
    var key_builder = PhaseKey.PhaseKeyBuilder.init(
        .exact_response,
        compiler_fingerprint,
    );
    key_builder.addInputBytes(input);
    return .{
        .kind = .exact_response,
        .key = key_builder.finish(),
    };
}

fn exactResponseIsCoherent(
    frontend_state: *FrontendRevisionState,
    request_key: PhaseKey.ArtifactKey,
) bool {
    var guard = frontend_state.lockExactResponse(request_key);
    defer guard.release();
    return guard.coherent;
}

/// Invalid or unusually deep JSON is gated conservatively. Valid non-Solidity
/// requests do not observe the session-owned Solidity frontend mutex.
fn requestRequiresFrontendCoherence(
    allocator: std.mem.Allocator,
    input: []const u8,
) bool {
    return requestUsesSolidityFrontend(allocator, input) catch true;
}

fn requestUsesSolidityFrontend(
    allocator: std.mem.Allocator,
    input: []const u8,
) !bool {
    return (try common.standard_json.inspectRequestFeatures(allocator, input)).language ==
        .solidity;
}

fn requestMayObserveSourceLoader(
    allocator: std.mem.Allocator,
    input: []const u8,
) bool {
    const features = common.standard_json.inspectRequestFeatures(
        allocator,
        input,
    ) catch return true;
    return features.language == .solidity or features.may_load_sources;
}

test "exact-response coherence classification follows the final language field" {
    try std.testing.expect(requestRequiresFrontendCoherence(std.testing.allocator,
        \\{"language":"Solidity"}
    ));
    try std.testing.expect(requestRequiresFrontendCoherence(std.testing.allocator,
        \\{"langu\u0061ge":"S\u006flidity"}
    ));
    try std.testing.expect(!requestRequiresFrontendCoherence(std.testing.allocator,
        \\{"language":"Solidity","language":"Yul"}
    ));
    try std.testing.expect(requestRequiresFrontendCoherence(std.testing.allocator,
        \\{"language":"Yul","language":"Solidity"}
    ));
    try std.testing.expect(!requestRequiresFrontendCoherence(std.testing.allocator,
        \\{"language":"Yul"}
    ));
    try std.testing.expect(requestRequiresFrontendCoherence(std.testing.allocator,
        \\{"language":"Yul"
    ));
}

test "compiler session returns independent exact-response cache hits" {
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var oracle_dispatcher: Libsolc.Dispatcher = .{};
    var expected = try oracle_dispatcher.compiler().compile(std.testing.allocator, .{
        .input = input,
    });
    defer expected.deinit();

    var session = CompilerSession.initWithFingerprint(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("session-test"),
    );
    defer session.deinit();

    var first = try session.compiler().compile(std.testing.allocator, .{ .input = input });
    try common.standard_json.compareExact(expected.bytes, first.bytes);
    first.bytes[0] = 'x';
    first.deinit();

    var cached = try session.compiler().compile(std.testing.allocator, .{ .input = input });
    defer cached.deinit();
    try common.standard_json.compareExact(expected.bytes, cached.bytes);

    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.requests);
    try std.testing.expectEqual(@as(u64, 2), statistics.cacheable_requests);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory.misses);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory.hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory.puts);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory_response_hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.response_misses);
    try std.testing.expectEqual(@as(u64, 0), statistics.coherence_rejections);
}

test "compiler session bounds retained exact responses" {
    const first_input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const second_input =
        \\{"language":"Yul","sources":{"B.yul":{"content":"object \"B\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var session = CompilerSession.initWithFingerprintAndOptions(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("bounded-session-test"),
        .{ .response_cache_limits = .{
            .max_entries = 1,
            .max_bytes = std.math.maxInt(u64),
        } },
    );
    defer session.deinit();

    var first = try session.compile(std.testing.allocator, .{ .input = first_input });
    defer first.deinit();
    var second = try session.compile(std.testing.allocator, .{ .input = second_input });
    defer second.deinit();
    var recompiled = try session.compile(std.testing.allocator, .{ .input = first_input });
    defer recompiled.deinit();
    try common.standard_json.compareExact(first.bytes, recompiled.bytes);

    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 3), statistics.memory.misses);
    try std.testing.expectEqual(@as(u64, 0), statistics.memory.hits);
    try std.testing.expectEqual(@as(u64, 2), statistics.memory.evictions);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory.entries);
}

test "Solidity frontend state does not disable Yul exact-response reuse" {
    const solidity_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing"}}
    ;
    const yul_input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();

    var solidity = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = solidity_input },
    );
    solidity.deinit();
    var first_yul = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = yul_input },
    );
    defer first_yul.deinit();
    var cached_yul = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = yul_input },
    );
    defer cached_yul.deinit();

    try common.standard_json.compareExact(first_yul.bytes, cached_yul.bytes);
    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 1), statistics.memory.hits);
    try std.testing.expectEqual(@as(u64, 2), statistics.memory.misses);
    try std.testing.expectEqual(@as(u64, 2), statistics.memory.puts);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory_response_hits);
    try std.testing.expectEqual(@as(u64, 2), statistics.response_misses);
    try std.testing.expectEqual(@as(u64, 0), statistics.coherence_rejections);
    try std.testing.expectEqual(@as(u64, 1), statistics.frontend.revision);
}

test "compiler session keeps source IDs stable across real Solidity revisions" {
    const first_input =
        \\{"language":"Solidity","sources":{"Dep.sol":{"content":"contract Dep {}"},"Z.sol":{"content":"import \"Dep.sol\"; contract Z is Dep {}"}},"settings":{"stopAfter":"parsing"}}
    ;
    const revised_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"},"Dep.sol":{"content":"contract Dep { uint256 value; }"},"Z.sol":{"content":"import \"Dep.sol\"; contract Z is Dep {}"}},"settings":{"stopAfter":"parsing"}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    var expected_first = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    defer expected_first.deinit();
    var first = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    defer first.deinit();
    try common.standard_json.compareExact(expected_first.bytes, first.bytes);
    const dep = session.frontend_state.sourceId("Dep.sol").?;
    const z = session.frontend_state.sourceId("Z.sol").?;

    var expected_revised = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer expected_revised.deinit();
    var revised = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer revised.deinit();
    try common.standard_json.compareExact(expected_revised.bytes, revised.bytes);

    try std.testing.expectEqual(dep, session.frontend_state.sourceId("Dep.sol").?);
    try std.testing.expectEqual(z, session.frontend_state.sourceId("Z.sol").?);
    const a = session.frontend_state.sourceId("A.sol").?;
    try std.testing.expectEqual(@as(u32, 2), a.index());
    try std.testing.expectEqual(SourceChange.added, session.frontend_state.sourceChange(a).?);
    try std.testing.expectEqual(SourceChange.modified, session.frontend_state.sourceChange(dep).?);
    try std.testing.expectEqual(SourceChange.unchanged, session.frontend_state.sourceChange(z).?);
    try std.testing.expect(session.frontend_state.isDirty(a));
    try std.testing.expect(session.frontend_state.isDirty(dep));
    try std.testing.expect(session.frontend_state.isDirty(z));
    const revised_statistics = session.statistics();
    try std.testing.expectEqual(
        @as(usize, 2),
        revised_statistics.frontend.parsed_syntax_sources,
    );
    try std.testing.expectEqual(
        @as(usize, 1),
        revised_statistics.frontend.reused_syntax_sources,
    );

    // A cached response for the first request must not leave the retained
    // frontend revision on the second request. It is recompiled and committed.
    var restored = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    defer restored.deinit();
    try common.standard_json.compareExact(expected_first.bytes, restored.bytes);
    try std.testing.expectEqual(@as(u64, 3), session.statistics().frontend.revision);
    try std.testing.expectEqual(SourceChange.removed, session.frontend_state.sourceChange(a).?);
    try std.testing.expectEqual(SourceChange.modified, session.frontend_state.sourceChange(dep).?);
    try std.testing.expect(session.frontend_state.isDirty(a));
    try std.testing.expect(session.frontend_state.isDirty(dep));
    try std.testing.expect(session.frontend_state.isDirty(z));
}

test "compiler session dirties unchanged sources after frontend settings change" {
    const first_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing","remappings":["alias/=lib/"]}}
    ;
    const revised_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing","remappings":["alias/=vendor/"]}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var first = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    first.deinit();
    const source = session.frontend_state.sourceId("A.sol").?;

    var revised = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    revised.deinit();

    try std.testing.expectEqual(SourceChange.unchanged, session.frontend_state.sourceChange(source).?);
    try std.testing.expect(session.frontend_state.isDirty(source));
}

test "compiler session dirties unchanged syntax when Yul optimizer policy changes" {
    const disabled_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A { function f() external pure returns (uint256) { assembly { let x := msize() } return 1; } }"}},"settings":{"optimizer":{"enabled":false},"outputSelection":{"*":{"*":["abi"]}}}}
    ;
    const enabled_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A { function f() external pure returns (uint256) { assembly { let x := msize() } return 1; } }"}},"settings":{"optimizer":{"enabled":true},"outputSelection":{"*":{"*":["abi"]}}}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    var expected_disabled = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = disabled_input },
    );
    defer expected_disabled.deinit();
    var disabled = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = disabled_input },
    );
    defer disabled.deinit();
    try common.standard_json.compareExact(expected_disabled.bytes, disabled.bytes);
    const source = session.frontend_state.sourceId("A.sol").?;

    var expected_enabled = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = enabled_input },
    );
    defer expected_enabled.deinit();
    var enabled = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = enabled_input },
    );
    defer enabled.deinit();
    try common.standard_json.compareExact(expected_enabled.bytes, enabled.bytes);
    try std.testing.expectEqual(
        SourceChange.unchanged,
        session.frontend_state.sourceChange(source).?,
    );
    try std.testing.expect(session.frontend_state.isDirty(source));

    // Replaying the cached first request must still advance frontend state and
    // invalidate the syntax policy retained by the enabled revision.
    var restored = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = disabled_input },
    );
    defer restored.deinit();
    try common.standard_json.compareExact(expected_disabled.bytes, restored.bytes);
    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 3), statistics.frontend.revision);
    try std.testing.expect(session.frontend_state.isDirty(source));
    try std.testing.expectEqual(@as(u64, 0), statistics.memory.hits);
    try std.testing.expectEqual(@as(u64, 0), statistics.memory.bytes_read);
    try std.testing.expectEqual(@as(u64, 1), statistics.coherence_rejections);
    try std.testing.expectEqual(@as(u64, 3), statistics.response_misses);
}

test "compiler session retains remapping-driven graph replacements" {
    const lib_input =
        \\{"language":"Solidity","sources":{"App.sol":{"content":"import \"alias/Dep.sol\"; contract App {}"},"lib/Dep.sol":{"content":"contract LibDep {}"},"vendor/Dep.sol":{"content":"contract VendorDep {}"}},"settings":{"stopAfter":"parsing","remappings":["alias/=lib/"]}}
    ;
    const vendor_input =
        \\{"language":"Solidity","sources":{"App.sol":{"content":"import \"alias/Dep.sol\"; contract App {}"},"lib/Dep.sol":{"content":"contract LibDep {}"},"vendor/Dep.sol":{"content":"contract VendorDep {}"}},"settings":{"stopAfter":"parsing","remappings":["alias/=vendor/"]}}
    ;
    const vendor_changed_input =
        \\{"language":"Solidity","sources":{"App.sol":{"content":"import \"alias/Dep.sol\"; contract App {}"},"lib/Dep.sol":{"content":"contract LibDep {}"},"vendor/Dep.sol":{"content":"contract VendorDep { uint256 value; }"}},"settings":{"stopAfter":"parsing","remappings":["alias/=vendor/"]}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    var expected_lib = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = lib_input },
    );
    defer expected_lib.deinit();
    var lib = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = lib_input },
    );
    defer lib.deinit();
    try common.standard_json.compareExact(expected_lib.bytes, lib.bytes);
    const app_source = session.frontend_state.sourceId("App.sol").?;
    const lib_source = session.frontend_state.sourceId("lib/Dep.sol").?;
    const vendor_source = session.frontend_state.sourceId("vendor/Dep.sol").?;

    var expected_vendor = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = vendor_input },
    );
    defer expected_vendor.deinit();
    var vendor = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = vendor_input },
    );
    defer vendor.deinit();
    try common.standard_json.compareExact(expected_vendor.bytes, vendor.bytes);
    try std.testing.expect(session.frontend_state.isDirty(app_source));
    try std.testing.expect(session.frontend_state.isDirty(lib_source));
    try std.testing.expect(session.frontend_state.isDirty(vendor_source));

    var expected_changed = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = vendor_changed_input },
    );
    defer expected_changed.deinit();
    var changed = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = vendor_changed_input },
    );
    defer changed.deinit();
    try common.standard_json.compareExact(expected_changed.bytes, changed.bytes);

    // With settings stable, only the changed vendor dependency and its
    // importer in the replacement graph belong to the reverse closure.
    try std.testing.expect(session.frontend_state.isDirty(app_source));
    try std.testing.expect(!session.frontend_state.isDirty(lib_source));
    try std.testing.expect(session.frontend_state.isDirty(vendor_source));
}

test "compiler session reuses semantics outside the reverse import closure" {
    const Transition = struct {
        input: []const u8,
        analyzed_sources: usize,
        reused_sources: usize,
    };
    const transitions = [_]Transition{
        .{
            .input =
            \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; contract Dep { function value() public pure returns (uint256) { return 1; } }"},"Main.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Main is Dep { function twice() external pure returns (uint256) { return value() * 2; } }"},"Warnings.sol":{"content":"pragma solidity ^0.8.0; contract Warnings { function ping(address payable recipient) external { recipient.send(1); } }"}},"settings":{"optimizer":{"enabled":false},"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
            ,
            .analyzed_sources = 3,
            .reused_sources = 0,
        },
        // Editing the dependency reanalyzes its importer while retaining the
        // independent source and replaying its type-checker warning.
        .{
            .input =
            \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; contract Dep { function value() public pure returns (uint256) { return 3; } }"},"Main.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Main is Dep { function twice() external pure returns (uint256) { return value() * 2; } }"},"Warnings.sol":{"content":"pragma solidity ^0.8.0; contract Warnings { function ping(address payable recipient) external { recipient.send(1); } }"}},"settings":{"optimizer":{"enabled":false},"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
            ,
            .analyzed_sources = 2,
            .reused_sources = 1,
        },
        // Editing only the independent source retains both sides of the
        // import edge.
        .{
            .input =
            \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; contract Dep { function value() public pure returns (uint256) { return 3; } }"},"Main.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Main is Dep { function twice() external pure returns (uint256) { return value() * 2; } }"},"Warnings.sol":{"content":"pragma solidity ^0.8.0; contract Warnings { function ping(address payable recipient) external { recipient.send(2); } }"}},"settings":{"optimizer":{"enabled":false},"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
            ,
            .analyzed_sources = 1,
            .reused_sources = 2,
        },
        // Projection-only requests reuse the complete semantic revision.
        .{
            .input =
            \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; contract Dep { function value() public pure returns (uint256) { return 3; } }"},"Main.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Main is Dep { function twice() external pure returns (uint256) { return value() * 2; } }"},"Warnings.sol":{"content":"pragma solidity ^0.8.0; contract Warnings { function ping(address payable recipient) external { recipient.send(2); } }"}},"settings":{"optimizer":{"enabled":false},"viaIR":true,"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
            ,
            .analyzed_sources = 0,
            .reused_sources = 3,
        },
        // A frontend-affecting optimizer change starts a fresh semantic
        // generation and reanalyzes every active source.
        .{
            .input =
            \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; contract Dep { function value() public pure returns (uint256) { return 3; } }"},"Main.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Main is Dep { function twice() external pure returns (uint256) { return value() * 2; } }"},"Warnings.sol":{"content":"pragma solidity ^0.8.0; contract Warnings { function ping(address payable recipient) external { recipient.send(2); } }"}},"settings":{"optimizer":{"enabled":true},"viaIR":true,"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
            ,
            .analyzed_sources = 3,
            .reused_sources = 0,
        },
    };

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    for (transitions, 1..) |transition, expected_revision| {
        var expected = try oracle.compiler().compile(
            std.testing.allocator,
            .{ .input = transition.input },
        );
        defer expected.deinit();
        var actual = try session.compiler().compile(
            std.testing.allocator,
            .{ .input = transition.input },
        );
        defer actual.deinit();
        try common.standard_json.compareExact(expected.bytes, actual.bytes);

        const frontend = session.statistics().frontend;
        try std.testing.expectEqual(@as(u64, @intCast(expected_revision)), frontend.revision);
        try std.testing.expectEqual(
            transition.analyzed_sources,
            frontend.analyzed_semantic_sources,
        );
        try std.testing.expectEqual(
            transition.reused_sources,
            frontend.reused_semantic_sources,
        );
        try std.testing.expectEqual(
            transition.analyzed_sources,
            frontend.dirty_sources,
        );
        try std.testing.expect(frontend.semantic_analyzed);
    }
}

test "semantic fingerprints skip importers that do not consume changed inputs" {
    const initial_input =
        \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; contract Dep { function value() internal pure returns (uint256) { return 1; } }"},"Unused.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Unused {}"},"Used.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Used is Dep { function read() external pure returns (uint256) { return value(); } }"}},"settings":{"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
    ;
    const body_input =
        \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; contract Dep { function value() internal pure returns (uint256) { return 2; } }"},"Unused.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Unused {}"},"Used.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Used is Dep { function read() external pure returns (uint256) { return value(); } }"}},"settings":{"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
    ;
    const interface_input =
        \\{"language":"Solidity","sources":{"Dep.sol":{"content":"pragma solidity ^0.8.0; struct Added { uint256 value; } contract Dep { function value() internal pure returns (uint256) { return 2; } }"},"Unused.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Unused {}"},"Used.sol":{"content":"pragma solidity ^0.8.0; import \"./Dep.sol\"; contract Used is Dep { function read() external pure returns (uint256) { return value(); } }"}},"settings":{"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    var expected_initial = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = initial_input },
    );
    defer expected_initial.deinit();
    var initial = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = initial_input },
    );
    defer initial.deinit();
    try common.standard_json.compareExact(expected_initial.bytes, initial.bytes);

    const dependency = session.frontend_state.sourceId("Dep.sol").?;
    const unused = session.frontend_state.sourceId("Unused.sol").?;
    const used = session.frontend_state.sourceId("Used.sol").?;

    var expected_body = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = body_input },
    );
    defer expected_body.deinit();
    var body = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = body_input },
    );
    defer body.deinit();
    try common.standard_json.compareExact(expected_body.bytes, body.bytes);
    try std.testing.expect(session.frontend_state.isDirty(dependency));
    try std.testing.expect(session.frontend_state.isDirty(used));
    try std.testing.expect(!session.frontend_state.isDirty(unused));
    const body_frontend = session.statistics().frontend;
    try std.testing.expectEqual(@as(usize, 2), body_frontend.dirty_sources);
    try std.testing.expectEqual(@as(usize, 2), body_frontend.analyzed_semantic_sources);
    try std.testing.expectEqual(@as(usize, 1), body_frontend.reused_semantic_sources);
    try std.testing.expectEqual(@as(usize, 3), body_frontend.fingerprinted_sources);
    try std.testing.expectEqual(@as(usize, 2), body_frontend.semantic_dependency_edges);

    var expected_interface = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = interface_input },
    );
    defer expected_interface.deinit();
    var interface = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = interface_input },
    );
    defer interface.deinit();
    try common.standard_json.compareExact(expected_interface.bytes, interface.bytes);
    const interface_frontend = session.statistics().frontend;
    try std.testing.expectEqual(@as(usize, 3), interface_frontend.dirty_sources);
    try std.testing.expectEqual(@as(usize, 3), interface_frontend.analyzed_semantic_sources);
    try std.testing.expectEqual(@as(usize, 0), interface_frontend.reused_semantic_sources);
}

test "semantic dependency masks retain transitive import paths" {
    const initial_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"pragma solidity ^0.8.0; contract Base { function value() internal pure returns (uint256) { return 1; } }"},"B.sol":{"content":"pragma solidity ^0.8.0; import \"./A.sol\";"},"C.sol":{"content":"pragma solidity ^0.8.0; import \"./B.sol\"; contract C is Base { function read() external pure returns (uint256) { return value(); } }"}},"settings":{"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
    ;
    const revised_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"pragma solidity ^0.8.0; contract Base { function value() internal pure returns (uint256) { return 2; } }"},"B.sol":{"content":"pragma solidity ^0.8.0; import \"./A.sol\";"},"C.sol":{"content":"pragma solidity ^0.8.0; import \"./B.sol\"; contract C is Base { function read() external pure returns (uint256) { return value(); } }"}},"settings":{"viaIR":true,"outputSelection":{"*":{"*":["abi","evm.bytecode.object","evm.deployedBytecode.object"],"":["ast"]}}}}
    ;
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    var expected_initial = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = initial_input },
    );
    defer expected_initial.deinit();
    var initial = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = initial_input },
    );
    defer initial.deinit();
    try common.standard_json.compareExact(expected_initial.bytes, initial.bytes);

    var expected_revised = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer expected_revised.deinit();
    var revised = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer revised.deinit();
    try common.standard_json.compareExact(expected_revised.bytes, revised.bytes);

    const frontend = session.statistics().frontend;
    try std.testing.expectEqual(@as(usize, 3), frontend.dirty_sources);
    try std.testing.expectEqual(@as(usize, 3), frontend.analyzed_semantic_sources);
    try std.testing.expectEqual(@as(usize, 0), frontend.reused_semantic_sources);
}

test "compiler session periodically rebases semantic overlays" {
    const input_prefix =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"pragma solidity ^0.8.0; contract A { function value() external pure returns (uint256) { return
    ;
    const input_suffix =
        \\; } }"},"Stable.sol":{"content":"pragma solidity ^0.8.0; contract Stable {}"}},"settings":{"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};
    var fresh_revisions: usize = 0;
    var maximum_retained_syntax: usize = 0;

    for (0..SemanticRevisionModule.max_overlay_depth + 2) |revision_index| {
        const input = try std.fmt.allocPrint(
            std.testing.allocator,
            "{s} {d}{s}",
            .{ input_prefix, revision_index, input_suffix },
        );
        defer std.testing.allocator.free(input);
        var expected = try oracle.compiler().compile(
            std.testing.allocator,
            .{ .input = input },
        );
        defer expected.deinit();
        var actual = try session.compiler().compile(std.testing.allocator, .{
            .input = input,
            .progress = .{ .report_fn = NoopProgress.report },
        });
        defer actual.deinit();
        try common.standard_json.compareExact(expected.bytes, actual.bytes);

        const frontend = session.statistics().frontend;
        try std.testing.expect(
            frontend.semantic_overlay_depth <= SemanticRevisionModule.max_overlay_depth,
        );
        maximum_retained_syntax = @max(
            maximum_retained_syntax,
            frontend.retained_semantic_syntax_sources,
        );
        if (frontend.semantic_overlay_depth == 0) {
            fresh_revisions += 1;
            try std.testing.expectEqual(
                @as(usize, 2),
                frontend.analyzed_semantic_sources,
            );
            try std.testing.expectEqual(
                @as(usize, 2),
                frontend.retained_semantic_syntax_sources,
            );
        } else {
            try std.testing.expectEqual(
                @as(usize, 1),
                frontend.analyzed_semantic_sources,
            );
            try std.testing.expectEqual(
                frontend.semantic_overlay_depth + 2,
                frontend.retained_semantic_syntax_sources,
            );
        }
    }

    try std.testing.expectEqual(@as(usize, 2), fresh_revisions);
    try std.testing.expectEqual(
        SemanticRevisionModule.max_overlay_depth + 2,
        maximum_retained_syntax,
    );
    const final_frontend = session.statistics().frontend;
    try std.testing.expectEqual(@as(usize, 0), final_frontend.semantic_overlay_depth);
    try std.testing.expectEqual(
        @as(usize, 2),
        final_frontend.retained_semantic_syntax_sources,
    );
}

test "callback import-order changes invalidate retained compatibility ordering" {
    const Loader = struct {
        fn read(
            _: ?*anyopaque,
            allocator: std.mem.Allocator,
            kind: []const u8,
            path: []const u8,
        ) common.standard_json.SourceReadError!common.standard_json.SourceReadResult {
            if (!std.mem.eql(u8, kind, "source")) return .unsupported;
            const contents = if (std.mem.eql(u8, path, "B.sol"))
                "pragma solidity ^0.8.0; contract B {}"
            else if (std.mem.eql(u8, path, "C.sol"))
                "pragma solidity ^0.8.0; contract C {}"
            else
                return .unsupported;
            return .{ .contents = try allocator.dupe(u8, contents) };
        }
    };
    const first_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"pragma solidity ^0.8.0; import \"B.sol\"; import \"C.sol\"; contract A {}"},"D.sol":{"content":"pragma solidity ^0.8.0; import \"B.sol\"; import \"C.sol\"; contract D { function make() external returns (B, C) { return (new B(), new C()); } }"}},"settings":{"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
    ;
    const reordered_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"pragma solidity ^0.8.0; import \"C.sol\"; import \"B.sol\"; contract A {}"},"D.sol":{"content":"pragma solidity ^0.8.0; import \"B.sol\"; import \"C.sol\"; contract D { function make() external returns (B, C) { return (new B(), new C()); } }"}},"settings":{"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
    ;
    const source_loader: common.standard_json.SourceLoader = .{
        .context = null,
        .read_fn = Loader.read,
    };

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    var expected_first = try oracle.compiler().compile(std.testing.allocator, .{
        .input = first_input,
        .source_loader = source_loader,
    });
    defer expected_first.deinit();
    var first = try session.compiler().compile(std.testing.allocator, .{
        .input = first_input,
        .source_loader = source_loader,
    });
    defer first.deinit();
    try common.standard_json.compareExact(expected_first.bytes, first.bytes);
    const independent = session.frontend_state.sourceId("D.sol").?;

    var expected_reordered = try oracle.compiler().compile(std.testing.allocator, .{
        .input = reordered_input,
        .source_loader = source_loader,
    });
    defer expected_reordered.deinit();
    var reordered = try session.compiler().compile(std.testing.allocator, .{
        .input = reordered_input,
        .source_loader = source_loader,
    });
    defer reordered.deinit();
    try common.standard_json.compareExact(expected_reordered.bytes, reordered.bytes);

    // Only A belongs to the graph dirty closure, but swapping its callback
    // discovery order changes B/C compatibility IDs. Retained call graphs for
    // clean D would otherwise preserve their obsolete B/C ordering.
    try std.testing.expect(!session.frontend_state.isDirty(independent));
    const frontend = session.statistics().frontend;
    try std.testing.expectEqual(@as(usize, 4), frontend.analyzed_semantic_sources);
    try std.testing.expectEqual(@as(usize, 0), frontend.reused_semantic_sources);
}

test "retained legacy node IDs cannot merge override signatures" {
    const initial_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"pragma solidity ^0.8.0; struct S { uint256 x; } contract BA { function f(S memory) internal virtual {} }"},"B.sol":{"content":"pragma solidity ^0.8.0; struct S { uint256 x; } contract BB { function f(S memory) internal virtual {} }"},"D.sol":{"content":"pragma solidity ^0.8.0; import * as A from \"./A.sol\"; import * as B from \"./B.sol\"; contract D is A.BA, B.BB {}"}},"settings":{"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
    ;
    // Thirteen leading contract nodes move the reparsed A.S declaration from
    // compatibility ID 4 to 17. B.S keeps its stored ID 17 in retained syntax,
    // while the current compatibility projection moves it to ID 30.
    const revised_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"pragma solidity ^0.8.0; contract X0 {} contract X1 {} contract X2 {} contract X3 {} contract X4 {} contract X5 {} contract X6 {} contract X7 {} contract X8 {} contract X9 {} contract X10 {} contract X11 {} contract X12 {} struct S { uint256 x; } contract BA { function f(S memory) internal virtual {} }"},"B.sol":{"content":"pragma solidity ^0.8.0; struct S { uint256 x; } contract BB { function f(S memory) internal virtual {} }"},"D.sol":{"content":"pragma solidity ^0.8.0; import * as A from \"./A.sol\"; import * as B from \"./B.sol\"; contract D is A.BA, B.BB {}"}},"settings":{"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
    ;
    const findStruct = struct {
        fn in(source: *const FrontendRevisionStateModule.SyntaxSource) ?*const AST.Node {
            for (source.parsed.tree.nodesInCreationOrder()) |node|
                if (node.nodeKind() == .struct_definition) return node;
            return null;
        }
    }.in;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var oracle: Libsolc.Dispatcher = .{};

    var expected_initial = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = initial_input },
    );
    defer expected_initial.deinit();
    var initial = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = initial_input },
    );
    defer initial.deinit();
    try common.standard_json.compareExact(expected_initial.bytes, initial.bytes);

    const a_source = session.frontend_state.sourceId("A.sol").?;
    const b_source = session.frontend_state.sourceId("B.sol").?;
    const retained_b_syntax = session.frontend_state.syntax.?.get(b_source).?;
    const retained_b_struct = findStruct(retained_b_syntax).?;
    try std.testing.expectEqual(@as(i64, 17), retained_b_struct.id);

    var expected_revised = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer expected_revised.deinit();
    var revised = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer revised.deinit();
    try common.standard_json.compareExact(expected_revised.bytes, revised.bytes);

    const current_a_struct = findStruct(
        session.frontend_state.syntax.?.get(a_source).?,
    ).?;
    const current_b_syntax = session.frontend_state.syntax.?.get(b_source).?;
    const current_b_struct = findStruct(current_b_syntax).?;
    try std.testing.expect(current_b_syntax == retained_b_syntax);
    try std.testing.expectEqual(current_a_struct.id, current_b_struct.id);
    try std.testing.expect(!current_a_struct.node_ref.eql(current_b_struct.node_ref));

    // D's OverrideChecker must distinguish the two internal f(S) signatures
    // with stable identities even though their retained legacy IDs collide.
    const frontend = session.statistics().frontend;
    try std.testing.expectEqual(@as(usize, 2), frontend.dirty_sources);
    try std.testing.expectEqual(@as(usize, 3), frontend.analyzed_semantic_sources);
    try std.testing.expectEqual(@as(usize, 0), frontend.reused_semantic_sources);
}

test "compiler session aborts a frontend revision after allocation failure" {
    const first_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing"}}
    ;
    const revised_input =
        \\{"language":"Solidity","sources":{"0.sol":{"content":"contract Earlier {}"},"A.sol":{"content":"contract A { uint256 value; }"}},"settings":{"stopAfter":"parsing"}}
    ;
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{});
    var session = CompilerSession.init(failing.allocator());
    defer session.deinit();

    var first = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    first.deinit();
    const a = session.frontend_state.sourceId("A.sol").?;
    try std.testing.expectEqual(@as(u64, 1), session.statistics().frontend.revision);

    failing.fail_index = failing.alloc_index;
    try std.testing.expectError(
        error.OutOfMemory,
        session.compiler().compile(std.testing.allocator, .{ .input = revised_input }),
    );
    try std.testing.expectEqual(@as(u64, 1), session.statistics().frontend.revision);
    try std.testing.expectEqual(a, session.frontend_state.sourceId("A.sol").?);
    try std.testing.expect(session.frontend_state.sourceId("0.sol") == null);

    failing.fail_index = std.math.maxInt(usize);
    var retry = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    retry.deinit();
    try std.testing.expectEqual(@as(u64, 2), session.statistics().frontend.revision);
    try std.testing.expectEqual(a, session.frontend_state.sourceId("A.sol").?);
    try std.testing.expectEqual(@as(u32, 1), session.frontend_state.sourceId("0.sol").?.index());
}

test "persistent compiler session rejects an unidentified build" {
    var store = MemoryArtifactStore.init(std.testing.allocator);
    defer store.deinit();
    try std.testing.expectError(
        error.UnidentifiedCompilerBuild,
        CompilerSession.initWithBackingStore(
            std.testing.allocator,
            PhaseKey.CompilerFingerprint.unidentified(),
            store.artifactStore(),
        ),
    );
}

test "source callbacks reject only same-session recursive compilation" {
    const Loader = struct {
        const nested_input =
            \\{"language":"Yul","sources":{"Nested.yul":{"content":"object \"Nested\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
        ;

        session: *CompilerSession,
        other_session: *CompilerSession,
        calls: usize = 0,
        reentrant_rejections: usize = 0,
        other_session_compiles: usize = 0,

        fn read(
            opaque_context: ?*anyopaque,
            allocator: std.mem.Allocator,
            kind: []const u8,
            data: []const u8,
        ) common.standard_json.SourceReadError!common.standard_json.SourceReadResult {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            self.calls += 1;
            if (!std.mem.eql(u8, kind, "source") or !std.mem.eql(u8, data, "A.sol"))
                return .unsupported;

            var other_output = self.other_session.compile(
                allocator,
                .{ .input = nested_input },
            ) catch |err| switch (err) {
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.InternalFailure,
            };
            other_output.deinit();
            self.other_session_compiles += 1;

            if (self.session.compile(allocator, .{ .input = nested_input })) |unexpected_value| {
                var unexpected = unexpected_value;
                unexpected.deinit();
                return error.InternalFailure;
            } else |err| switch (err) {
                error.ReentrantCompilation => self.reentrant_rejections += 1,
                error.OutOfMemory => return error.OutOfMemory,
                else => return error.InternalFailure,
            }
            return .{ .contents = try allocator.dupe(u8, "contract A {}") };
        }
    };
    const input =
        \\{"language":"Solidity","sources":{"A.sol":{"urls":["A.sol"]}},"settings":{"outputSelection":{"*":{"*":["abi"]}}}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var other_session = CompilerSession.init(std.testing.allocator);
    defer other_session.deinit();
    var loader: Loader = .{
        .session = &session,
        .other_session = &other_session,
    };
    var output = try session.compile(std.testing.allocator, .{
        .input = input,
        .source_loader = .{ .context = &loader, .read_fn = Loader.read },
    });
    defer output.deinit();
    try std.testing.expect(std.mem.find(u8, output.bytes, "\"contracts\"") != null);
    try std.testing.expect(loader.calls != 0);
    try std.testing.expectEqual(loader.calls, loader.reentrant_rejections);
    try std.testing.expectEqual(loader.calls, loader.other_session_compiles);
    try std.testing.expectEqual(
        @as(u64, @intCast(loader.reentrant_rejections)),
        session.statistics().reentrant_rejections,
    );

    // The callback frame is gone when the outer request returns.
    var after_callback = try session.compile(
        std.testing.allocator,
        .{ .input = Loader.nested_input },
    );
    after_callback.deinit();
}

test "compiler session never bypasses source callbacks" {
    const Loader = struct {
        calls: usize = 0,

        fn read(
            opaque_context: ?*anyopaque,
            allocator: std.mem.Allocator,
            kind: []const u8,
            data: []const u8,
        ) common.standard_json.SourceReadError!common.standard_json.SourceReadResult {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            self.calls += 1;
            if (!std.mem.eql(u8, kind, "source") or !std.mem.eql(u8, data, "A.yul"))
                return .unsupported;
            return .{ .contents = try allocator.dupe(
                u8,
                "object \"A\" { code { stop() } }",
            ) };
        }
    };
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"urls":["A.yul"]}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;

    var loader: Loader = .{};
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    for (0..2) |_| {
        var output = try session.compiler().compile(std.testing.allocator, .{
            .input = input,
            .source_loader = .{ .context = &loader, .read_fn = Loader.read },
        });
        defer output.deinit();
        try std.testing.expectEqualStrings(
            "{\"contracts\":{\"A.yul\":{\"A\":{\"evm\":{\"bytecode\":{\"object\":\"00\"}}}}},\"errors\":[]}\n",
            output.bytes,
        );
    }

    const statistics = session.statistics();
    try std.testing.expectEqual(@as(usize, 2), loader.calls);
    try std.testing.expectEqual(@as(u64, 2), statistics.bypassed_requests);
    try std.testing.expectEqual(@as(u64, 0), statistics.memory.entries);
}

test "compiler session reloads callback imports for inline Solidity sources" {
    const Loader = struct {
        contents: []const u8,
        calls: usize = 0,

        fn read(
            opaque_context: ?*anyopaque,
            allocator: std.mem.Allocator,
            kind: []const u8,
            path: []const u8,
        ) common.standard_json.SourceReadError!common.standard_json.SourceReadResult {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            self.calls += 1;
            if (!std.mem.eql(u8, kind, "source") or
                !std.mem.eql(u8, path, "B.sol"))
            {
                return .unsupported;
            }
            return .{ .contents = try allocator.dupe(u8, self.contents) };
        }
    };
    const input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"import {B} from \"B.sol\"; contract A { function value() external pure returns (uint256) { return B.value(); } }"}},"settings":{"viaIR":true,"optimizer":{"enabled":true},"metadata":{"bytecodeHash":"none"},"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const first_import =
        "library B { function value() internal pure returns (uint256) { return 1; } }";
    const second_import =
        "library B { function value() internal pure returns (uint256) { return 2; } }";

    var loader: Loader = .{ .contents = first_import };
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var first = try session.compiler().compile(std.testing.allocator, .{
        .input = input,
        .source_loader = .{ .context = &loader, .read_fn = Loader.read },
    });
    defer first.deinit();

    loader.contents = second_import;
    var second = try session.compiler().compile(std.testing.allocator, .{
        .input = input,
        .source_loader = .{ .context = &loader, .read_fn = Loader.read },
    });
    defer second.deinit();

    var oracle_loader: Loader = .{ .contents = second_import };
    var oracle: Libsolc.Dispatcher = .{};
    var expected = try oracle.compiler().compile(std.testing.allocator, .{
        .input = input,
        .source_loader = .{
            .context = &oracle_loader,
            .read_fn = Loader.read,
        },
    });
    defer expected.deinit();

    try std.testing.expect(!std.mem.eql(u8, first.bytes, second.bytes));
    try common.standard_json.compareExact(expected.bytes, second.bytes);
    try std.testing.expectEqual(@as(usize, 2), loader.calls);
    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.bypassed_requests);
    try std.testing.expectEqual(@as(u64, 0), statistics.memory_response_hits);
}

test "compiler session caches self-contained requests with a dormant loader" {
    const Loader = struct {
        calls: usize = 0,

        fn read(
            opaque_context: ?*anyopaque,
            _: std.mem.Allocator,
            _: []const u8,
            _: []const u8,
        ) common.standard_json.SourceReadError!common.standard_json.SourceReadResult {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            self.calls += 1;
            return .unsupported;
        }
    };
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;

    var loader: Loader = .{};
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    for (0..2) |_| {
        var output = try session.compiler().compile(std.testing.allocator, .{
            .input = input,
            .source_loader = .{ .context = &loader, .read_fn = Loader.read },
        });
        defer output.deinit();
    }

    const statistics = session.statistics();
    try std.testing.expectEqual(@as(usize, 0), loader.calls);
    try std.testing.expectEqual(@as(u64, 2), statistics.cacheable_requests);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory_response_hits);
}

test "compiler session never bypasses progress callbacks" {
    const Recorder = struct {
        calls: usize = 0,

        fn report(opaque_context: ?*anyopaque, _: common.standard_json.ProgressUpdate) void {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            self.calls += 1;
        }
    };
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;

    var recorder: Recorder = .{};
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var first = try session.compiler().compile(std.testing.allocator, .{
        .input = input,
        .progress = .{ .context = &recorder, .report_fn = Recorder.report },
    });
    defer first.deinit();
    const first_call_count = recorder.calls;
    try std.testing.expect(first_call_count != 0);

    var second = try session.compiler().compile(std.testing.allocator, .{
        .input = input,
        .progress = .{ .context = &recorder, .report_fn = Recorder.report },
    });
    defer second.deinit();
    try common.standard_json.compareExact(first.bytes, second.bytes);
    try std.testing.expect(recorder.calls > first_call_count);

    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.bypassed_requests);
    try std.testing.expectEqual(@as(u64, 0), statistics.memory.entries);
}

test "Solidity progress callbacks can read committed session statistics" {
    const Recorder = struct {
        const nested_input =
            \\{"language":"Yul","sources":{"Nested.yul":{"content":"object \"Nested\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
        ;

        session: *CompilerSession,
        calls: usize = 0,
        inconsistent_revision: bool = false,
        attempted_reentrant_compile: bool = false,
        rejected_reentrant_compile: bool = false,

        fn report(opaque_context: ?*anyopaque, _: common.standard_json.ProgressUpdate) void {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            const statistics = self.session.statistics();
            self.calls += 1;
            if (statistics.frontend.revision != 1)
                self.inconsistent_revision = true;
            if (self.attempted_reentrant_compile) return;
            self.attempted_reentrant_compile = true;
            if (self.session.compile(
                std.testing.allocator,
                .{ .input = nested_input },
            )) |unexpected_value| {
                var unexpected = unexpected_value;
                unexpected.deinit();
            } else |err| {
                self.rejected_reentrant_compile = err == error.ReentrantCompilation;
            }
        }
    };
    const input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing"}}
    ;

    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var first = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    first.deinit();

    var recorder: Recorder = .{ .session = &session };
    var second = try session.compiler().compile(std.testing.allocator, .{
        .input = input,
        .progress = .{ .context = &recorder, .report_fn = Recorder.report },
    });
    second.deinit();

    try std.testing.expect(recorder.calls != 0);
    try std.testing.expect(!recorder.inconsistent_revision);
    try std.testing.expect(recorder.attempted_reentrant_compile);
    try std.testing.expect(recorder.rejected_reentrant_compile);
    try std.testing.expectEqual(@as(u64, 1), session.statistics().reentrant_rejections);
    try std.testing.expectEqual(@as(u64, 2), session.statistics().frontend.revision);
}

test "compiler session reloads an exact response after process-style restart" {
    const SqliteStore = @import("sqlite_store.zig").SqliteStore;
    const authentication_key = [_]u8{0x41} ** 32;
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const fingerprint = PhaseKey.CompilerFingerprint.init("persistent-session-test");
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const cache_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/session-cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(cache_path);

    var first_store = try SqliteStore.init(
        std.testing.allocator,
        std.testing.io,
        cache_path,
        authentication_key,
    );
    var first_session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        first_store.artifactStore(),
    );
    var expected = try first_session.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    first_session.deinit();
    first_store.deinit();

    var reopened_store = try SqliteStore.init(
        std.testing.allocator,
        std.testing.io,
        cache_path,
        authentication_key,
    );
    defer reopened_store.deinit();
    var restarted_session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        reopened_store.artifactStore(),
    );
    defer restarted_session.deinit();
    var actual = try restarted_session.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    defer actual.deinit();
    defer expected.deinit();
    try common.standard_json.compareExact(expected.bytes, actual.bytes);
    const statistics = restarted_session.statistics();
    try std.testing.expectEqual(@as(u64, 1), statistics.memory.misses);
    try std.testing.expectEqual(@as(u64, 1), statistics.persistent_hits);
    try std.testing.expectEqual(@as(u64, 0), statistics.persistent_misses);
}

test "compiler session reloads optimized Yul across process-style restart" {
    const SqliteStore = @import("sqlite_store.zig").SqliteStore;
    const authentication_key = [_]u8{0x42} ** 32;
    const first_input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { let x := add(1, 2) mstore(0, x) return(0, 32) } }"}},"settings":{"optimizer":{"enabled":true},"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const revised_input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { let x := add(1, 2) mstore(0, x) return(0, 32) } }"}},"settings":{"optimizer":{"enabled":true},"outputSelection":{"*":{"*":["evm.bytecode.object","evm.bytecode.opcodes"]}}}}
    ;
    const fingerprint = PhaseKey.CompilerFingerprint.init("persistent-optimizer-test");
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const cache_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/optimizer-cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(cache_path);

    var first_store = try SqliteStore.init(
        std.testing.allocator,
        std.testing.io,
        cache_path,
        authentication_key,
    );
    var first_session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        first_store.artifactStore(),
    );
    var first = try first_session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    first.deinit();
    try std.testing.expect(first_session.statistics().optimizer.optimization_runs != 0);
    first_session.deinit();
    first_store.deinit();

    var oracle_dispatcher: Libsolc.Dispatcher = .{};
    var expected = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer expected.deinit();

    var reopened_store = try SqliteStore.init(
        std.testing.allocator,
        std.testing.io,
        cache_path,
        authentication_key,
    );
    defer reopened_store.deinit();
    var restarted_session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        reopened_store.artifactStore(),
    );
    defer restarted_session.deinit();
    var actual = try restarted_session.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer actual.deinit();
    try common.standard_json.compareExact(expected.bytes, actual.bytes);

    const statistics = restarted_session.statistics();
    try std.testing.expectEqual(@as(u64, 1), statistics.persistent_misses);
    try std.testing.expect(statistics.optimizer.persistent_hits != 0);
    try std.testing.expectEqual(@as(u64, 0), statistics.optimizer.optimization_runs);
    try std.testing.expect(statistics.backend.persistent_hits != 0);
    try std.testing.expectEqual(@as(u64, 1), statistics.backend.machine_hits);
    try std.testing.expectEqual(@as(u64, 0), statistics.backend.lowering_runs);
    try std.testing.expectEqual(@as(u64, 0), statistics.backend.bytecode_assembly_runs);
}

test "compiler session reuses backend layers across metadata and projection changes" {
    const first_input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { datacopy(0, dataoffset(\"A_deployed\"), datasize(\"A_deployed\")) return(0, datasize(\"A_deployed\")) } object \"A_deployed\" { code { mstore(0, 1) return(0, 32) } data \".metadata\" hex\"aabb\" } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const metadata_changed =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { datacopy(0, dataoffset(\"A_deployed\"), datasize(\"A_deployed\")) return(0, datasize(\"A_deployed\")) } object \"A_deployed\" { code { mstore(0, 1) return(0, 32) } data \".metadata\" hex\"ccdd\" } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object","evm.bytecode.opcodes"]}}}}
    ;
    const projection_changed =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { datacopy(0, dataoffset(\"A_deployed\"), datasize(\"A_deployed\")) return(0, datasize(\"A_deployed\")) } object \"A_deployed\" { code { mstore(0, 1) return(0, 32) } data \".metadata\" hex\"ccdd\" } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object","evm.bytecode.opcodes","evm.bytecode.sourceMap"]}}}}
    ;

    var session = CompilerSession.initWithFingerprint(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("backend-layer-test"),
    );
    defer session.deinit();
    var first = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    first.deinit();

    var oracle_dispatcher: Libsolc.Dispatcher = .{};
    var expected_metadata = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = metadata_changed },
    );
    defer expected_metadata.deinit();
    var actual_metadata = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = metadata_changed },
    );
    defer actual_metadata.deinit();
    try common.standard_json.compareExact(expected_metadata.bytes, actual_metadata.bytes);

    var expected_projection = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = projection_changed },
    );
    defer expected_projection.deinit();
    var actual_projection = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = projection_changed },
    );
    defer actual_projection.deinit();
    try common.standard_json.compareExact(expected_projection.bytes, actual_projection.bytes);

    const statistics = session.statistics().backend;
    try std.testing.expectEqual(@as(u64, 1), statistics.lowering_runs);
    try std.testing.expectEqual(@as(u64, 1), statistics.blueprint_hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.machine_hits);
    try std.testing.expectEqual(@as(u64, 2), statistics.bytecode_assembly_runs);
    try std.testing.expectEqual(@as(u64, 0), statistics.link_hits);
    try std.testing.expectEqual(@as(u64, 0), statistics.link_misses);
}

test "metadata-only Solidity rebuild preserves assembly and function debug projections" {
    const first_input =
        \\{"language":"Solidity","sources":{"C.sol":{"content":"contract C { function f(uint256 x) public pure returns (uint256) { return g(x); } function g(uint256 x) internal pure returns (uint256) { return x + 1; } }"}},"settings":{"viaIR":true,"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const revised_input =
        \\{"language":"Solidity","sources":{"C.sol":{"content":"contract C { function f(uint256 x) public pure returns (uint256) { return g(x); } function g(uint256 x) internal pure returns (uint256) { return x + 1; } }"}},"settings":{"viaIR":true,"metadata":{"bytecodeHash":"none"},"outputSelection":{"*":{"*":["evm.assembly","evm.legacyAssembly","evm.gasEstimates","evm.bytecode.functionDebugData","evm.deployedBytecode.functionDebugData"]}}}}
    ;

    var session = CompilerSession.initWithFingerprint(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("backend-solidity-blueprint-test"),
    );
    defer session.deinit();
    var first = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    first.deinit();

    var oracle_dispatcher: Libsolc.Dispatcher = .{};
    var expected = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer expected.deinit();
    var actual = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer actual.deinit();
    try common.standard_json.compareExact(expected.bytes, actual.bytes);

    const statistics = session.statistics().backend;
    try std.testing.expectEqual(@as(u64, 1), statistics.lowering_runs);
    try std.testing.expectEqual(@as(u64, 1), statistics.blueprint_hits);
    try std.testing.expectEqual(@as(u64, 2), statistics.machine_misses);
    try std.testing.expectEqual(@as(u64, 2), statistics.bytecode_assembly_runs);
}

test "compiler session reuses machine and linked artifacts across library settings" {
    const first_input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { mstore(0, linkersymbol(\"lib.sol:L\")) return(0, 32) } }"}},"settings":{"libraries":{"lib.sol":{"L":"0x1111111111111111111111111111111111111111"}},"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const library_changed =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { mstore(0, linkersymbol(\"lib.sol:L\")) return(0, 32) } }"}},"settings":{"libraries":{"lib.sol":{"L":"0x2222222222222222222222222222222222222222"}},"outputSelection":{"*":{"*":["evm.bytecode.object","evm.bytecode.opcodes"]}}}}
    ;
    const projection_changed =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { mstore(0, linkersymbol(\"lib.sol:L\")) return(0, 32) } }"}},"settings":{"libraries":{"lib.sol":{"L":"0x2222222222222222222222222222222222222222"}},"outputSelection":{"*":{"*":["evm.bytecode.object","evm.bytecode.opcodes","evm.bytecode.sourceMap"]}}}}
    ;

    var session = CompilerSession.initWithFingerprint(
        std.testing.allocator,
        PhaseKey.CompilerFingerprint.init("backend-link-test"),
    );
    defer session.deinit();
    var first = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    first.deinit();

    var oracle_dispatcher: Libsolc.Dispatcher = .{};
    var expected_library = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = library_changed },
    );
    defer expected_library.deinit();
    var actual_library = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = library_changed },
    );
    defer actual_library.deinit();
    try common.standard_json.compareExact(expected_library.bytes, actual_library.bytes);

    var expected_projection = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = projection_changed },
    );
    defer expected_projection.deinit();
    var actual_projection = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = projection_changed },
    );
    defer actual_projection.deinit();
    try common.standard_json.compareExact(expected_projection.bytes, actual_projection.bytes);

    const statistics = session.statistics().backend;
    try std.testing.expectEqual(@as(u64, 1), statistics.lowering_runs);
    try std.testing.expectEqual(@as(u64, 2), statistics.machine_hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.bytecode_assembly_runs);
    try std.testing.expectEqual(@as(u64, 1), statistics.link_hits);
    try std.testing.expectEqual(@as(u64, 2), statistics.link_misses);
}

const NoopProgress = struct {
    fn report(_: ?*anyopaque, _: common.standard_json.ProgressUpdate) void {}
};

/// A borrowed, immutable exact response used to observe whether a session
/// probes or copies a persistent payload. Non-response cache traffic misses.
const ExactResponseProbeStore = struct {
    reference: ArtifactStoreModule.ArtifactRef,
    payload: []const u8,
    block_get: bool = false,
    exact_contains: std.atomic.Value(u64) = .init(0),
    exact_gets: std.atomic.Value(u64) = .init(0),
    exact_puts: std.atomic.Value(u64) = .init(0),
    get_entered: std.atomic.Value(bool) = .init(false),
    release_get: std.atomic.Value(bool) = .init(false),

    fn artifactStore(self: *ExactResponseProbeStore) ArtifactStoreModule.ArtifactStore {
        return .{
            .context = self,
            .contains_fn = containsErased,
            .get_alloc_fn = getAllocErased,
            .put_fn = putErased,
        };
    }

    fn containsErased(
        context: *anyopaque,
        reference: ArtifactStoreModule.ArtifactRef,
    ) ArtifactStoreModule.StoreError!bool {
        const self: *ExactResponseProbeStore = @ptrCast(@alignCast(context));
        if (!reference.eql(self.reference)) return false;
        _ = self.exact_contains.fetchAdd(1, .monotonic);
        return true;
    }

    fn getAllocErased(
        context: *anyopaque,
        allocator: std.mem.Allocator,
        reference: ArtifactStoreModule.ArtifactRef,
    ) ArtifactStoreModule.StoreError!?ArtifactStoreModule.Artifact {
        const self: *ExactResponseProbeStore = @ptrCast(@alignCast(context));
        if (!reference.eql(self.reference)) return null;
        _ = self.exact_gets.fetchAdd(1, .monotonic);
        self.get_entered.store(true, .release);
        while (self.block_get and !self.release_get.load(.acquire))
            std.atomic.spinLoopHint();

        const payload = try allocator.dupe(u8, self.payload);
        errdefer allocator.free(payload);
        const dependencies = try allocator.alloc(ArtifactStoreModule.ArtifactRef, 0);
        return .{
            .allocator = allocator,
            .payload = payload,
            .dependencies = dependencies,
        };
    }

    fn putErased(
        context: *anyopaque,
        reference: ArtifactStoreModule.ArtifactRef,
        _: []const u8,
        _: []const ArtifactStoreModule.ArtifactRef,
    ) ArtifactStoreModule.StoreError!void {
        const self: *ExactResponseProbeStore = @ptrCast(@alignCast(context));
        if (reference.eql(self.reference))
            _ = self.exact_puts.fetchAdd(1, .monotonic);
    }
};

test "Solidity coherence preflight rejects a persistent response without copying it" {
    const first_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing"}}
    ;
    const revised_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A { uint256 value; }"}},"settings":{"stopAfter":"parsing"}}
    ;
    const fingerprint = PhaseKey.CompilerFingerprint.init("coherence-preflight-test");

    var oracle: Libsolc.Dispatcher = .{};
    var expected_first = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    defer expected_first.deinit();
    var expected_revised = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer expected_revised.deinit();

    var probe_store: ExactResponseProbeStore = .{
        .reference = exactResponseReference(fingerprint, first_input),
        .payload = expected_first.bytes,
    };
    var session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        probe_store.artifactStore(),
    );
    defer session.deinit();

    // Callback-bearing requests bypass exact-response caching while still
    // committing real frontend revisions, yielding an A-B-A transition with
    // no process-local A payload.
    var first = try session.compiler().compile(std.testing.allocator, .{
        .input = first_input,
        .progress = .{ .report_fn = NoopProgress.report },
    });
    defer first.deinit();
    try common.standard_json.compareExact(expected_first.bytes, first.bytes);
    var revised = try session.compiler().compile(std.testing.allocator, .{
        .input = revised_input,
        .progress = .{ .report_fn = NoopProgress.report },
    });
    defer revised.deinit();
    try common.standard_json.compareExact(expected_revised.bytes, revised.bytes);

    var restored = try session.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    defer restored.deinit();
    try common.standard_json.compareExact(expected_first.bytes, restored.bytes);

    try std.testing.expectEqual(
        @as(u64, 1),
        probe_store.exact_contains.load(.monotonic),
    );
    try std.testing.expectEqual(@as(u64, 0), probe_store.exact_gets.load(.monotonic));
    try std.testing.expectEqual(@as(u64, 1), probe_store.exact_puts.load(.monotonic));
    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 3), statistics.frontend.revision);
    try std.testing.expectEqual(@as(u64, 0), statistics.memory.hits);
    try std.testing.expectEqual(@as(u64, 0), statistics.memory.bytes_read);
    try std.testing.expectEqual(@as(u64, 1), statistics.coherence_rejections);
    try std.testing.expectEqual(@as(u64, 0), statistics.persistent_hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.persistent_misses);
    try std.testing.expectEqual(@as(u64, 1), statistics.response_misses);
}

const ExactResponseRaceWorker = struct {
    session: *CompilerSession,
    input: []const u8,
    expected: []const u8,
    completed: *std.atomic.Value(bool),
    failed: *std.atomic.Value(bool),

    fn run(self: *const ExactResponseRaceWorker) void {
        var output = self.session.compiler().compile(
            std.heap.smp_allocator,
            .{ .input = self.input },
        ) catch {
            self.failed.store(true, .release);
            return;
        };
        defer output.deinit();
        common.standard_json.compareExact(self.expected, output.bytes) catch {
            self.failed.store(true, .release);
            return;
        };
        self.completed.store(true, .release);
    }
};

test "Solidity coherence is rechecked after a persistent response copy" {
    const first_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing"}}
    ;
    const revised_input =
        \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A { uint256 value; }"}},"settings":{"stopAfter":"parsing"}}
    ;
    const fingerprint = PhaseKey.CompilerFingerprint.init("coherence-race-test");

    var oracle: Libsolc.Dispatcher = .{};
    var expected_first = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = first_input },
    );
    defer expected_first.deinit();
    var expected_revised = try oracle.compiler().compile(
        std.testing.allocator,
        .{ .input = revised_input },
    );
    defer expected_revised.deinit();

    var probe_store: ExactResponseProbeStore = .{
        .reference = exactResponseReference(fingerprint, first_input),
        .payload = expected_first.bytes,
        .block_get = true,
    };
    var session = try CompilerSession.initWithBackingStore(
        std.heap.smp_allocator,
        fingerprint,
        probe_store.artifactStore(),
    );
    defer session.deinit();
    var first = try session.compiler().compile(std.heap.smp_allocator, .{
        .input = first_input,
        .progress = .{ .report_fn = NoopProgress.report },
    });
    defer first.deinit();
    try common.standard_json.compareExact(expected_first.bytes, first.bytes);

    var completed: std.atomic.Value(bool) = .init(false);
    var failed: std.atomic.Value(bool) = .init(false);
    var worker: ExactResponseRaceWorker = .{
        .session = &session,
        .input = first_input,
        .expected = expected_first.bytes,
        .completed = &completed,
        .failed = &failed,
    };
    var threaded = std.Io.Threaded.init(std.heap.smp_allocator, .{
        .async_limit = .limited(1),
    });
    defer threaded.deinit();
    const io = threaded.io();
    var group: std.Io.Group = .init;
    group.async(io, ExactResponseRaceWorker.run, .{&worker});
    defer probe_store.release_get.store(true, .release);

    var wait_iterations: usize = 0;
    while (!probe_store.get_entered.load(.acquire) and
        !failed.load(.acquire) and
        wait_iterations < 2_000) : (wait_iterations += 1)
    {
        try std.Io.sleep(io, .fromMilliseconds(1), .awake);
    }
    if (!probe_store.get_entered.load(.acquire)) {
        probe_store.release_get.store(true, .release);
        try group.await(io);
        try std.testing.expect(!failed.load(.acquire));
        try std.testing.expect(probe_store.get_entered.load(.acquire));
        return;
    }

    // The presence preflight observed revision A. Commit B while the store is
    // copying A, then let the post-copy check reject and recompile A.
    var revised = try session.compiler().compile(std.heap.smp_allocator, .{
        .input = revised_input,
        .progress = .{ .report_fn = NoopProgress.report },
    });
    defer revised.deinit();
    try common.standard_json.compareExact(expected_revised.bytes, revised.bytes);
    try std.testing.expectEqual(@as(u64, 2), session.statistics().frontend.revision);

    probe_store.release_get.store(true, .release);
    try group.await(io);
    try std.testing.expect(!failed.load(.acquire));
    try std.testing.expect(completed.load(.acquire));
    try std.testing.expectEqual(
        @as(u64, 0),
        probe_store.exact_contains.load(.monotonic),
    );
    try std.testing.expectEqual(@as(u64, 1), probe_store.exact_gets.load(.monotonic));

    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 3), statistics.frontend.revision);
    try std.testing.expectEqual(@as(u64, 1), statistics.coherence_rejections);
    try std.testing.expectEqual(@as(u64, 0), statistics.persistent_hits);
    try std.testing.expectEqual(@as(u64, 1), statistics.persistent_misses);
    try std.testing.expectEqual(@as(u64, 1), statistics.response_misses);
}

const CacheFailureMode = enum {
    allocation_read,
    disk_write,
};

const CacheFailureStore = struct {
    mode: CacheFailureMode,
    reads: std.atomic.Value(u64) = .init(0),
    writes: std.atomic.Value(u64) = .init(0),

    fn artifactStore(self: *CacheFailureStore) ArtifactStoreModule.ArtifactStore {
        return .{
            .context = self,
            .contains_fn = containsErased,
            .get_alloc_fn = getAllocErased,
            .put_fn = putErased,
        };
    }

    fn containsErased(
        context: *anyopaque,
        _: ArtifactStoreModule.ArtifactRef,
    ) ArtifactStoreModule.StoreError!bool {
        const self: *CacheFailureStore = @ptrCast(@alignCast(context));
        _ = self.reads.fetchAdd(1, .monotonic);
        return switch (self.mode) {
            .allocation_read => error.OutOfMemory,
            .disk_write => false,
        };
    }

    fn getAllocErased(
        context: *anyopaque,
        _: std.mem.Allocator,
        _: ArtifactStoreModule.ArtifactRef,
    ) ArtifactStoreModule.StoreError!?ArtifactStoreModule.Artifact {
        const self: *CacheFailureStore = @ptrCast(@alignCast(context));
        _ = self.reads.fetchAdd(1, .monotonic);
        return switch (self.mode) {
            .allocation_read => error.OutOfMemory,
            .disk_write => null,
        };
    }

    fn putErased(
        context: *anyopaque,
        _: ArtifactStoreModule.ArtifactRef,
        _: []const u8,
        _: []const ArtifactStoreModule.ArtifactRef,
    ) ArtifactStoreModule.StoreError!void {
        const self: *CacheFailureStore = @ptrCast(@alignCast(context));
        _ = self.writes.fetchAdd(1, .monotonic);
        if (self.mode == .disk_write) return error.Unavailable;
    }
};

test "compiler session falls back after cache allocation and disk-write failures" {
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { let x := add(1, 2) mstore(0, x) return(0, 32) } }"}},"settings":{"optimizer":{"enabled":true},"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var oracle_dispatcher: Libsolc.Dispatcher = .{};
    var expected = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    defer expected.deinit();

    for ([_]CacheFailureMode{ .allocation_read, .disk_write }) |mode| {
        var failure_store: CacheFailureStore = .{ .mode = mode };
        var session = try CompilerSession.initWithBackingStore(
            std.testing.allocator,
            PhaseKey.CompilerFingerprint.init("cache-failure-test"),
            failure_store.artifactStore(),
        );
        defer session.deinit();
        var actual = try session.compiler().compile(
            std.testing.allocator,
            .{ .input = input },
        );
        defer actual.deinit();
        try common.standard_json.compareExact(expected.bytes, actual.bytes);
        try std.testing.expect(session.statistics().store_failures != 0);
        try std.testing.expect(failure_store.reads.load(.monotonic) != 0);
        if (mode == .disk_write)
            try std.testing.expect(failure_store.writes.load(.monotonic) != 0);
    }
}

const BlockingSolidityProgress = struct {
    entered: std.atomic.Value(bool) = .init(false),
    release: std.atomic.Value(bool) = .init(false),

    fn report(opaque_context: ?*anyopaque, _: common.standard_json.ProgressUpdate) void {
        const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
        if (self.entered.swap(true, .acq_rel)) return;
        while (!self.release.load(.acquire)) std.atomic.spinLoopHint();
    }
};

const BlockingSolidityWorker = struct {
    session: *CompilerSession,
    progress: *BlockingSolidityProgress,
    failed: *std.atomic.Value(bool),

    fn run(self: *const BlockingSolidityWorker) void {
        const input =
            \\{"language":"Solidity","sources":{"A.sol":{"content":"contract A {}"}},"settings":{"stopAfter":"parsing"}}
        ;
        var output = self.session.compiler().compile(
            std.heap.smp_allocator,
            .{
                .input = input,
                .progress = .{
                    .context = self.progress,
                    .report_fn = BlockingSolidityProgress.report,
                },
            },
        ) catch {
            self.failed.store(true, .release);
            return;
        };
        output.deinit();
    }
};

const CachedYulWorker = struct {
    session: *CompilerSession,
    input: []const u8,
    completed: *std.atomic.Value(bool),
    failed: *std.atomic.Value(bool),

    fn run(self: *const CachedYulWorker) void {
        var output = self.session.compiler().compile(
            std.heap.smp_allocator,
            .{ .input = self.input },
        ) catch {
            self.failed.store(true, .release);
            return;
        };
        output.deinit();
        self.completed.store(true, .release);
    }
};

test "cached Yul responses do not wait for a Solidity frontend revision" {
    const yul_input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var session = CompilerSession.init(std.heap.smp_allocator);
    defer session.deinit();
    var primed = try session.compiler().compile(
        std.heap.smp_allocator,
        .{ .input = yul_input },
    );
    primed.deinit();

    var progress: BlockingSolidityProgress = .{};
    defer progress.release.store(true, .release);
    var failed: std.atomic.Value(bool) = .init(false);
    var yul_completed: std.atomic.Value(bool) = .init(false);
    var solidity_worker: BlockingSolidityWorker = .{
        .session = &session,
        .progress = &progress,
        .failed = &failed,
    };
    var yul_worker: CachedYulWorker = .{
        .session = &session,
        .input = yul_input,
        .completed = &yul_completed,
        .failed = &failed,
    };
    var threaded = std.Io.Threaded.init(std.heap.smp_allocator, .{
        .async_limit = .limited(2),
    });
    defer threaded.deinit();
    const io = threaded.io();
    var group: std.Io.Group = .init;
    group.async(io, BlockingSolidityWorker.run, .{&solidity_worker});
    while (!progress.entered.load(.acquire)) std.atomic.spinLoopHint();
    group.async(io, CachedYulWorker.run, .{&yul_worker});

    var wait_iterations: usize = 0;
    while (!yul_completed.load(.acquire) and wait_iterations < 2_000) : (wait_iterations += 1)
        try std.Io.sleep(io, .fromMilliseconds(1), .awake);
    const completed_while_solidity_was_blocked = yul_completed.load(.acquire);
    progress.release.store(true, .release);
    try group.await(io);

    try std.testing.expect(!failed.load(.acquire));
    try std.testing.expect(completed_while_solidity_was_blocked);
}

const ConcurrentSessionWorker = struct {
    session: *CompilerSession,
    input: []const u8,
    expected: []const u8,
    ready: *std.atomic.Value(usize),
    release: *std.atomic.Value(bool),
    failed: *std.atomic.Value(bool),

    fn run(self: *const ConcurrentSessionWorker) void {
        _ = self.ready.fetchAdd(1, .release);
        while (!self.release.load(.acquire)) std.atomic.spinLoopHint();
        var output = self.session.compiler().compile(
            std.heap.smp_allocator,
            .{ .input = self.input },
        ) catch {
            self.failed.store(true, .release);
            return;
        };
        defer output.deinit();
        common.standard_json.compareExact(self.expected, output.bytes) catch
            self.failed.store(true, .release);
    }
};

test "concurrent duplicate compilations share a real compiler session" {
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { function f(a, b) -> r { r := add(mul(a, 7), b) } let x := f(calldataload(0), calldataload(32)) mstore(0, x) return(0, 32) } }"}},"settings":{"optimizer":{"enabled":true,"runs":500},"outputSelection":{"*":{"*":["evm.bytecode.object","evm.bytecode.opcodes"]}}}}
    ;
    var oracle_dispatcher: Libsolc.Dispatcher = .{};
    var expected = try oracle_dispatcher.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    defer expected.deinit();

    var serial_session = CompilerSession.init(std.testing.allocator);
    var serial_output = try serial_session.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    serial_output.deinit();
    const serial_statistics = serial_session.statistics();
    serial_session.deinit();

    var session = CompilerSession.init(std.heap.smp_allocator);
    defer session.deinit();
    const worker_count = 4;
    var ready: std.atomic.Value(usize) = .init(0);
    var release: std.atomic.Value(bool) = .init(false);
    var failed: std.atomic.Value(bool) = .init(false);
    var workers: [worker_count]ConcurrentSessionWorker = undefined;
    var threaded = std.Io.Threaded.init(std.heap.smp_allocator, .{
        .async_limit = .limited(worker_count),
    });
    defer threaded.deinit();
    const io = threaded.io();
    var group: std.Io.Group = .init;
    for (&workers) |*worker| {
        worker.* = .{
            .session = &session,
            .input = input,
            .expected = expected.bytes,
            .ready = &ready,
            .release = &release,
            .failed = &failed,
        };
        group.async(io, ConcurrentSessionWorker.run, .{worker});
    }
    while (ready.load(.acquire) != worker_count) std.atomic.spinLoopHint();
    release.store(true, .release);
    try group.await(io);
    try std.testing.expect(!failed.load(.acquire));

    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, worker_count), statistics.requests);
    try std.testing.expectEqual(
        serial_statistics.optimizer.optimization_runs,
        statistics.optimizer.optimization_runs,
    );
    try std.testing.expectEqual(
        serial_statistics.backend.lowering_runs,
        statistics.backend.lowering_runs,
    );
    try std.testing.expectEqual(
        serial_statistics.backend.bytecode_assembly_runs,
        statistics.backend.bytecode_assembly_runs,
    );
}
