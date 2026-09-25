// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! SQLite artifact store for persistent incremental compilation.

const std = @import("std");
const ArtifactStoreModule = @import("artifact_store.zig");
const FixedHash = @import("../libsolutil/fixed_hash.zig");
const Keccak256 = @import("../libsolutil/keccak256.zig");

const zqlite = @import("zqlite");
const sqlite = zqlite.c;

const Artifact = ArtifactStoreModule.Artifact;
const ArtifactRef = ArtifactStoreModule.ArtifactRef;
const ArtifactKind = ArtifactStoreModule.ArtifactKind;
const ArtifactKey = ArtifactStoreModule.ArtifactKey;
const StoreError = ArtifactStoreModule.StoreError;
const H256 = FixedHash.H256;
const HmacSha256 = std.crypto.auth.hmac.sha2.HmacSha256;

const application_id: i64 = 0x5a534f4c;
const schema_version: i64 = 2;
const database_authentication_domain = "zsolc sqlite artifact cache v2";
const artifact_authentication_domain = "zsolc sqlite artifact v2";

pub const AuthenticationKey = [HmacSha256.key_length]u8;
const AuthenticationTag = [HmacSha256.mac_length]u8;

pub const default_limits: ArtifactStoreModule.CacheLimits = .{
    .max_entries = 100 * 1024,
    .max_bytes = 16 * 1024 * 1024 * 1024,
};

pub const Options = struct {
    limits: ArtifactStoreModule.CacheLimits = default_limits,
    /// SQLite waits briefly for another process's writer transaction, then the
    /// cache operation becomes `Unavailable` and compilation continues.
    busy_timeout_ms: u32 = 250,
    /// Accesses are accumulated in memory and written with one shared epoch.
    /// A zero interval disables access-age updates without disabling reads.
    access_flush_interval: u32 = 128,
    max_pending_accesses: u32 = 256,
    /// Receives owned, operation-scoped SQLite failures after the database
    /// mutex is released. The sink owns each snapshot it receives.
    diagnostic_sink: ?DiagnosticSink = null,
};

pub const QueryId = enum {
    open_database,
    configure_extended_results,
    configure_busy_timeout,
    configure_trusted_schema,
    configure_foreign_keys,
    configure_journal_mode,
    configure_synchronous,
    configure_temp_store,
    read_application_id,
    read_schema_version,
    count_user_tables,
    create_schema,
    store_authentication,
    read_authentication,
    contains_artifact,
    select_artifact,
    select_dependencies,
    upsert_artifact,
    delete_dependencies,
    insert_dependency,
    load_cache_state,
    store_epoch,
    update_access,
    select_oldest,
    delete_artifact,
    begin_deferred,
    begin_immediate,
    begin_exclusive,
    commit,
    rollback,
    ad_hoc,
};

pub const DiagnosticOperation = enum {
    open,
    configure,
    prepare,
    bind,
    reset,
    step,
    begin,
    commit,
    rollback,
    finalize,
    close,
};

/// One allocator-owned causal SQLite failure. Diagnostic sinks take ownership
/// and must call `deinit()` exactly once.
pub const DiagnosticSnapshot = struct {
    allocator: std.mem.Allocator,
    sequence: u64,
    operation: DiagnosticOperation,
    primary_code: c_int,
    extended_code: c_int,
    query: ?QueryId,
    message: []u8,

    pub fn deinit(self: *DiagnosticSnapshot) void {
        self.allocator.free(self.message);
        self.* = undefined;
    }
};

pub const DiagnosticSink = struct {
    context: ?*anyopaque = null,
    report_fn: *const fn (?*anyopaque, DiagnosticSnapshot) void,

    fn report(self: DiagnosticSink, snapshot: DiagnosticSnapshot) void {
        self.report_fn(self.context, snapshot);
    }
};

const schema_sql =
    \\CREATE TABLE IF NOT EXISTS artifact(
    \\    kind INTEGER NOT NULL,
    \\    key BLOB NOT NULL CHECK(length(key)=32),
    \\    size INTEGER NOT NULL CHECK(size>=0),
    \\    payload BLOB NOT NULL,
    \\    payload_digest BLOB NOT NULL CHECK(length(payload_digest)=32),
    \\    payload_authentication BLOB NOT NULL CHECK(length(payload_authentication)=32),
    \\    created_epoch INTEGER NOT NULL,
    \\    used_epoch INTEGER NOT NULL,
    \\    PRIMARY KEY(kind,key)
    \\) WITHOUT ROWID;
    \\CREATE TABLE IF NOT EXISTS cache_authentication(
    \\    singleton INTEGER PRIMARY KEY CHECK(singleton=1),
    \\    verifier BLOB NOT NULL CHECK(length(verifier)=32)
    \\) WITHOUT ROWID;
    \\CREATE TABLE IF NOT EXISTS dependency(
    \\    owner_kind INTEGER NOT NULL,
    \\    owner_key BLOB NOT NULL CHECK(length(owner_key)=32),
    \\    dependency_kind INTEGER NOT NULL,
    \\    dependency_key BLOB NOT NULL CHECK(length(dependency_key)=32),
    \\    PRIMARY KEY(owner_kind,owner_key,dependency_kind,dependency_key)
    \\) WITHOUT ROWID;
    \\CREATE TABLE IF NOT EXISTS cache_state(
    \\    singleton INTEGER PRIMARY KEY CHECK(singleton=1),
    \\    epoch INTEGER NOT NULL CHECK(epoch>=0),
    \\    entry_count INTEGER NOT NULL CHECK(entry_count>=0),
    \\    logical_bytes INTEGER NOT NULL CHECK(logical_bytes>=0)
    \\) WITHOUT ROWID;
    \\INSERT OR IGNORE INTO cache_state(singleton,epoch,entry_count,logical_bytes)
    \\VALUES(1,0,0,0);
    \\CREATE TRIGGER IF NOT EXISTS artifact_state_insert
    \\AFTER INSERT ON artifact BEGIN
    \\    UPDATE cache_state
    \\    SET entry_count=entry_count+1,logical_bytes=logical_bytes+NEW.size
    \\    WHERE singleton=1;
    \\END;
    \\CREATE TRIGGER IF NOT EXISTS artifact_state_update
    \\AFTER UPDATE OF size ON artifact BEGIN
    \\    UPDATE cache_state
    \\    SET logical_bytes=logical_bytes+NEW.size-OLD.size
    \\    WHERE singleton=1;
    \\END;
    \\CREATE TRIGGER IF NOT EXISTS artifact_state_delete
    \\AFTER DELETE ON artifact BEGIN
    \\    UPDATE cache_state
    \\    SET entry_count=entry_count-1,logical_bytes=logical_bytes-OLD.size
    \\    WHERE singleton=1;
    \\END;
    \\CREATE INDEX IF NOT EXISTS artifact_lru
    \\ON artifact(used_epoch,created_epoch,kind,key);
    \\PRAGMA application_id=0x5a534f4c;
    \\PRAGMA user_version=2;
;

const StoredArtifact = struct {
    allocator: std.mem.Allocator,
    size: u64,
    payload: []u8,
    payload_digest: H256,
    payload_authentication: AuthenticationTag,
    used_epoch: u64,
    dependencies: []ArtifactRef,

    fn deinit(self: *StoredArtifact) void {
        self.allocator.free(self.dependencies);
        self.allocator.free(self.payload);
        self.* = undefined;
    }

    fn take(
        self: *StoredArtifact,
        authentication_key: AuthenticationKey,
        reference: ArtifactRef,
    ) StoreError!Artifact {
        if (self.payload.len != self.size) return error.Corrupt;
        const actual_digest = Keccak256.keccak256(self.payload);
        if (!actual_digest.eql(&self.payload_digest)) return error.Corrupt;
        const actual_authentication = artifactAuthentication(
            authentication_key,
            reference,
            self.payload,
            self.dependencies,
        );
        if (!std.crypto.timing_safe.eql(
            AuthenticationTag,
            actual_authentication,
            self.payload_authentication,
        )) return error.Corrupt;
        const result: Artifact = .{
            .allocator = self.allocator,
            .payload = self.payload,
            .dependencies = self.dependencies,
        };
        self.* = undefined;
        return result;
    }
};

pub const Statistics = struct {
    hits: u64,
    misses: u64,
    puts: u64,
    bytes_read: u64,
    bytes_written: u64,
    resident_entries: u64,
    resident_logical_bytes: u64,
    evictions: u64,
    bytes_evicted: u64,
    admission_rejections: u64,
    access_flushes: u64,
    access_updates: u64,
    dropped_access_updates: u64,
    maintenance_failures: u64,
    /// Cumulative time spent acquiring the already-contended database mutex.
    database_wait_nanoseconds: u64,
};

pub const Summary = struct {
    entries: u64,
    logical_bytes: u64,
    epoch: u64,
};

pub const PruneReport = struct {
    before: Summary,
    after: Summary,
    entries_removed: u64,
    logical_bytes_removed: u64,
};

const PersistentState = struct {
    epoch: u64,
    entries: u64,
    logical_bytes: u64,
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

const PendingAccessMap = std.HashMapUnmanaged(
    ArtifactRef,
    void,
    ArtifactRefContext,
    80,
);

pub const SqliteStore = struct {
    pub const InitError = std.mem.Allocator.Error || error{
        AuthenticationFailed,
        Corrupt,
        IncompatibleSchema,
        NewerSchema,
        Unavailable,
    };

    allocator: std.mem.Allocator,
    io: std.Io,
    database: *sqlite.sqlite3,
    idle_statements: std.enums.EnumArray(QueryId, ?zqlite.Stmt) = .initFill(null),
    authentication_key: AuthenticationKey,
    mutex: std.Io.Mutex = .init,
    limits: ArtifactStoreModule.CacheLimits,
    access_flush_interval: u32,
    max_pending_accesses: u32,
    diagnostic_sink: ?DiagnosticSink,
    diagnostic_sequence: u64 = 0,
    pending_diagnostic: ?DiagnosticSnapshot = null,
    pending_accesses: PendingAccessMap = .empty,
    pending_access_events: u64 = 0,
    epoch: u64 = 0,
    hit_count: std.atomic.Value(u64) = .init(0),
    miss_count: std.atomic.Value(u64) = .init(0),
    put_count: std.atomic.Value(u64) = .init(0),
    bytes_read_count: std.atomic.Value(u64) = .init(0),
    bytes_written_count: std.atomic.Value(u64) = .init(0),
    resident_entry_count: std.atomic.Value(u64) = .init(0),
    resident_logical_byte_count: std.atomic.Value(u64) = .init(0),
    eviction_count: std.atomic.Value(u64) = .init(0),
    evicted_byte_count: std.atomic.Value(u64) = .init(0),
    admission_rejection_count: std.atomic.Value(u64) = .init(0),
    access_flush_count: std.atomic.Value(u64) = .init(0),
    access_update_count: std.atomic.Value(u64) = .init(0),
    dropped_access_update_count: std.atomic.Value(u64) = .init(0),
    maintenance_failure_count: std.atomic.Value(u64) = .init(0),
    database_wait_nanoseconds: std.atomic.Value(u64) = .init(0),

    pub fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        path: []const u8,
        authentication_key: AuthenticationKey,
    ) InitError!SqliteStore {
        return initWithOptions(allocator, io, path, authentication_key, .{});
    }

    pub fn initWithOptions(
        allocator: std.mem.Allocator,
        io: std.Io,
        path: []const u8,
        authentication_key: AuthenticationKey,
        options: Options,
    ) InitError!SqliteStore {
        try ensureDatabaseFilePermissions(io, path);
        const path_z = try allocator.dupeSentinel(u8, path, 0);
        defer allocator.free(path_z);
        // zqlite's pinned open path does not close SQLite's partial handle on
        // failure. Keep open/diagnostic/close together at this C boundary.
        var database_optional: ?*sqlite.sqlite3 = null;
        const flags = sqlite.SQLITE_OPEN_READWRITE |
            sqlite.SQLITE_OPEN_CREATE |
            sqlite.SQLITE_OPEN_FULLMUTEX |
            sqlite.SQLITE_OPEN_NOFOLLOW;
        const open_status = sqlite.sqlite3_open_v2(path_z.ptr, &database_optional, flags, null);
        const database = database_optional orelse return error.Unavailable;
        if (open_status != sqlite.SQLITE_OK) {
            publishStandaloneDiagnostic(
                allocator,
                options.diagnostic_sink,
                database,
                open_status,
                .open,
                .open_database,
            );
            _ = sqlite.sqlite3_close_v2(database);
            return mapInitStatus(open_status);
        }
        errdefer _ = sqlite.sqlite3_close_v2(database);
        var result: SqliteStore = .{
            .allocator = allocator,
            .io = io,
            .database = database,
            .authentication_key = authentication_key,
            .limits = options.limits,
            .access_flush_interval = options.access_flush_interval,
            .max_pending_accesses = options.max_pending_accesses,
            .diagnostic_sink = options.diagnostic_sink,
        };
        errdefer result.publishPendingDiagnosticUnlocked();
        errdefer result.deinitStatements();
        try result.checkInitStatus(
            .configure,
            .configure_extended_results,
            sqlite.sqlite3_extended_result_codes(database, 1),
        );
        if (options.busy_timeout_ms > std.math.maxInt(c_int)) return error.Unavailable;
        try result.checkInitStatus(
            .configure,
            .configure_busy_timeout,
            sqlite.sqlite3_busy_timeout(database, @intCast(options.busy_timeout_ms)),
        );
        try result.initializeSchema();
        const state = try result.loadStateInit();
        if (state.entries > options.limits.max_entries or
            state.logical_bytes > options.limits.max_bytes)
        {
            _ = result.prune(options.limits) catch |err| return mapInitError(err);
        } else {
            result.publishState(state);
        }
        return result;
    }

    pub fn deinit(self: *SqliteStore) void {
        self.pending_accesses.deinit(self.allocator);
        self.deinitStatements();
        if (self.pending_diagnostic) |*diagnostic| diagnostic.deinit();
        _ = sqlite.sqlite3_close_v2(self.database);
        self.* = undefined;
    }

    pub fn artifactStore(self: *SqliteStore) ArtifactStoreModule.ArtifactStore {
        return .{
            .context = self,
            .contains_fn = containsErased,
            .get_alloc_fn = getAllocErased,
            .put_fn = putErased,
        };
    }

    pub fn contains(self: *SqliteStore, reference: ArtifactRef) StoreError!bool {
        self.beginOperation();
        defer self.finishOperation();
        var statement = try self.prepare(
            .contains_artifact,
            "SELECT 1 FROM artifact WHERE kind=?1 AND key=?2;",
        );
        defer statement.deinit();
        try self.bindReference(&statement, reference);
        return switch (try statement.step()) {
            .row => true,
            .done => false,
        };
    }

    pub fn getAlloc(
        self: *SqliteStore,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError!?Artifact {
        var record = (try self.loadArtifactAlloc(allocator, reference)) orelse return null;
        errdefer record.deinit();
        return try record.take(self.authentication_key, reference);
    }

    fn loadArtifactAlloc(
        self: *SqliteStore,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError!?StoredArtifact {
        self.beginOperation();
        defer self.finishOperation();
        var transaction = try Transaction.begin(self.lockedDatabase(), .deferred);
        defer transaction.rollbackUnlessCommitted();

        const record = try self.selectArtifactAlloc(allocator, reference);
        if (record == null) {
            try transaction.commit();
            _ = self.miss_count.fetchAdd(1, .monotonic);
            return null;
        }
        var result = record.?;
        errdefer result.deinit();
        const dependencies = try self.selectDependenciesAlloc(allocator, reference);
        allocator.free(result.dependencies);
        result.dependencies = dependencies;
        try transaction.commit();
        _ = self.hit_count.fetchAdd(1, .monotonic);
        _ = self.bytes_read_count.fetchAdd(result.payload.len, .monotonic);
        self.recordAccessLocked(reference, result.used_epoch);
        return result;
    }

    pub fn put(
        self: *SqliteStore,
        reference: ArtifactRef,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) StoreError!void {
        if (payload.len > std.math.maxInt(i64)) return error.ArtifactTooLarge;
        const payload_digest = Keccak256.keccak256(payload);
        const canonical_dependencies = try canonicalDependenciesAlloc(
            self.allocator,
            dependencies,
        );
        defer self.allocator.free(canonical_dependencies);
        const payload_authentication = artifactAuthentication(
            self.authentication_key,
            reference,
            payload,
            canonical_dependencies,
        );

        self.beginOperation();
        defer self.finishOperation();
        var transaction = try Transaction.begin(self.lockedDatabase(), .immediate);
        defer transaction.rollbackUnlessCommitted();
        var state = try self.loadState();
        const flushed_accesses = try self.applyPendingAccessesInTransaction(&state);

        const logical_size: u64 = @intCast(payload.len);
        const admitted = self.limits.max_entries != 0 and
            self.limits.max_bytes != 0 and logical_size <= self.limits.max_bytes;
        if (!admitted) {
            try self.deleteRecord(reference);
            try self.storeEpoch(state.epoch);
            state = try self.loadState();
            const pruned = try self.pruneToLimitsInTransaction(&state, self.limits);
            try transaction.commit();
            self.finishCommittedAccessFlush(flushed_accesses);
            self.publishState(state);
            _ = self.put_count.fetchAdd(1, .monotonic);
            _ = self.bytes_written_count.fetchAdd(payload.len, .monotonic);
            _ = self.admission_rejection_count.fetchAdd(1, .monotonic);
            _ = self.eviction_count.fetchAdd(pruned.entries_removed, .monotonic);
            _ = self.evicted_byte_count.fetchAdd(pruned.logical_bytes_removed, .monotonic);
            return;
        }

        const record_epoch = try nextEpoch(&state);
        try self.upsertArtifact(
            reference,
            payload,
            payload_digest,
            payload_authentication,
            record_epoch,
        );
        try self.replaceDependencies(reference, canonical_dependencies);
        try self.storeEpoch(state.epoch);
        state = try self.loadState();
        const pruned = try self.pruneToLimitsInTransaction(&state, self.limits);
        try transaction.commit();
        self.finishCommittedAccessFlush(flushed_accesses);
        self.publishState(state);
        _ = self.put_count.fetchAdd(1, .monotonic);
        _ = self.bytes_written_count.fetchAdd(payload.len, .monotonic);
        _ = self.eviction_count.fetchAdd(pruned.entries_removed, .monotonic);
        _ = self.evicted_byte_count.fetchAdd(pruned.logical_bytes_removed, .monotonic);
    }

    /// Reads the transactionally maintained logical cache size. The value is
    /// current across all processes using this database when the call returns.
    pub fn summary(self: *SqliteStore) StoreError!Summary {
        self.beginOperation();
        defer self.finishOperation();
        const state = try self.loadState();
        self.publishState(state);
        return summaryFromState(state);
    }

    /// Removes least-recently-used records until both logical limits hold.
    /// Dependency rows owned by removed artifacts are deleted in the same
    /// transaction.
    pub fn prune(
        self: *SqliteStore,
        limits: ArtifactStoreModule.CacheLimits,
    ) StoreError!PruneReport {
        self.beginOperation();
        defer self.finishOperation();
        var transaction = try Transaction.begin(self.lockedDatabase(), .immediate);
        defer transaction.rollbackUnlessCommitted();
        var state = try self.loadState();
        const before = summaryFromState(state);
        const flushed_accesses = try self.applyPendingAccessesInTransaction(&state);
        try self.storeEpoch(state.epoch);
        state = try self.loadState();
        const removed = try self.pruneToLimitsInTransaction(&state, limits);
        try transaction.commit();
        self.finishCommittedAccessFlush(flushed_accesses);
        self.publishState(state);
        _ = self.eviction_count.fetchAdd(removed.entries_removed, .monotonic);
        _ = self.evicted_byte_count.fetchAdd(removed.logical_bytes_removed, .monotonic);
        return .{
            .before = before,
            .after = summaryFromState(state),
            .entries_removed = removed.entries_removed,
            .logical_bytes_removed = removed.logical_bytes_removed,
        };
    }

    pub fn statistics(self: *const SqliteStore) Statistics {
        return .{
            .hits = self.hit_count.load(.monotonic),
            .misses = self.miss_count.load(.monotonic),
            .puts = self.put_count.load(.monotonic),
            .bytes_read = self.bytes_read_count.load(.monotonic),
            .bytes_written = self.bytes_written_count.load(.monotonic),
            .resident_entries = self.resident_entry_count.load(.monotonic),
            .resident_logical_bytes = self.resident_logical_byte_count.load(.monotonic),
            .evictions = self.eviction_count.load(.monotonic),
            .bytes_evicted = self.evicted_byte_count.load(.monotonic),
            .admission_rejections = self.admission_rejection_count.load(.monotonic),
            .access_flushes = self.access_flush_count.load(.monotonic),
            .access_updates = self.access_update_count.load(.monotonic),
            .dropped_access_updates = self.dropped_access_update_count.load(.monotonic),
            .maintenance_failures = self.maintenance_failure_count.load(.monotonic),
            .database_wait_nanoseconds = self.database_wait_nanoseconds.load(.monotonic),
        };
    }

    fn initializeSchema(self: *SqliteStore) InitError!void {
        self.execInitQuery(
            .configure,
            .configure_trusted_schema,
            "PRAGMA trusted_schema=OFF;",
        ) catch |err| return mapInitError(err);
        self.execInitQuery(
            .configure,
            .configure_foreign_keys,
            "PRAGMA foreign_keys=ON;",
        ) catch |err| return mapInitError(err);
        self.execInitQuery(
            .configure,
            .configure_journal_mode,
            "PRAGMA journal_mode=WAL;",
        ) catch |err| return mapInitError(err);
        self.execInitQuery(
            .configure,
            .configure_synchronous,
            "PRAGMA synchronous=NORMAL;",
        ) catch |err| return mapInitError(err);
        self.execInitQuery(
            .configure,
            .configure_temp_store,
            "PRAGMA temp_store=MEMORY;",
        ) catch |err| return mapInitError(err);

        // Read the version and authentication from one snapshot. Only a new
        // database needs a writer lock; existing caches can open during writes.
        var transaction = Transaction.begin(self.lockedDatabase(), .deferred) catch |err|
            return mapInitError(err);
        defer transaction.rollbackUnlessCommitted();
        if (!try self.hasCompatibleSchema()) {
            transaction.rollback() catch |err| return mapInitError(err);
            transaction = Transaction.begin(self.lockedDatabase(), .immediate) catch |err|
                return mapInitError(err);
            // Another process may have initialized the database while we
            // waited. Schema creation and authentication must commit together.
            if (!try self.hasCompatibleSchema()) {
                try self.execInitQuery(.step, .create_schema, schema_sql);
                self.storeAuthenticationVerifier() catch |err| return mapInitError(err);
            }
        }
        transaction.commit() catch |err| return mapInitError(err);
    }

    fn hasCompatibleSchema(self: *SqliteStore) InitError!bool {
        const actual_application_id = self.scalarIntInit(
            .read_application_id,
            "PRAGMA application_id;",
        ) catch |err|
            return mapInitError(err);
        const actual_schema_version = self.scalarIntInit(
            .read_schema_version,
            "PRAGMA user_version;",
        ) catch |err|
            return mapInitError(err);
        if (actual_application_id == 0 and actual_schema_version == 0) {
            const table_count = self.scalarIntInit(
                .count_user_tables,
                "SELECT count(*) FROM sqlite_schema WHERE type='table' AND name NOT LIKE 'sqlite_%';",
            ) catch |err| return mapInitError(err);
            if (table_count != 0) return error.IncompatibleSchema;
            return false;
        }
        if (actual_application_id != application_id) return error.IncompatibleSchema;
        if (actual_schema_version > schema_version) return error.NewerSchema;
        if (actual_schema_version != schema_version) return error.IncompatibleSchema;
        self.verifyAuthentication() catch |err| return mapInitError(err);
        return true;
    }

    fn storeAuthenticationVerifier(self: *SqliteStore) StoreError!void {
        var statement = try self.prepare(
            .store_authentication,
            "INSERT INTO cache_authentication(singleton,verifier) VALUES(1,?1);",
        );
        defer statement.deinit();
        const verifier = databaseAuthentication(self.authentication_key);
        try statement.bindBlobOwned(1, &verifier);
        if (try statement.step() != .done) return error.Corrupt;
    }

    fn verifyAuthentication(self: *SqliteStore) StoreError!void {
        var statement = try self.prepare(
            .read_authentication,
            "SELECT verifier FROM cache_authentication WHERE singleton=1;",
        );
        defer statement.deinit();
        // Older versions could commit the schema before inserting this row.
        // An absent verifier is incomplete storage and can be quarantined;
        // a present verifier from another key remains an authentication error.
        if (try statement.step() != .row) return error.Corrupt;
        const stored = try statement.columnAuthenticationTag(0);
        if (try statement.step() != .done) return error.AuthenticationFailed;
        const expected = databaseAuthentication(self.authentication_key);
        if (!std.crypto.timing_safe.eql(AuthenticationTag, stored, expected))
            return error.AuthenticationFailed;
    }

    fn selectArtifactAlloc(
        self: *SqliteStore,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError!?StoredArtifact {
        const sql =
            "SELECT size,payload,payload_digest,payload_authentication,used_epoch " ++
            "FROM artifact WHERE kind=?1 AND key=?2;";
        var statement = try self.prepare(.select_artifact, sql);
        defer statement.deinit();
        try self.bindReference(&statement, reference);
        if (try statement.step() == .done) return null;

        const size = try statement.columnNonNegativeU64(0);
        const payload = try statement.columnBlobAlloc(allocator, 1);
        errdefer allocator.free(payload);
        const payload_digest = try statement.columnH256(2);
        const payload_authentication = try statement.columnAuthenticationTag(3);
        const used_epoch = try statement.columnNonNegativeU64(4);
        return .{
            .allocator = allocator,
            .size = size,
            .payload = payload,
            .payload_digest = payload_digest,
            .payload_authentication = payload_authentication,
            .used_epoch = used_epoch,
            .dependencies = try allocator.alloc(ArtifactRef, 0),
        };
    }

    fn selectDependenciesAlloc(
        self: *SqliteStore,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError![]ArtifactRef {
        const sql =
            "SELECT dependency_kind,dependency_key FROM dependency " ++
            "WHERE owner_kind=?1 AND owner_key=?2 " ++
            "ORDER BY dependency_kind,dependency_key;";
        var statement = try self.prepare(.select_dependencies, sql);
        defer statement.deinit();
        try self.bindReference(&statement, reference);
        var dependencies: std.ArrayList(ArtifactRef) = .empty;
        errdefer dependencies.deinit(allocator);
        while (true) {
            if (try statement.step() == .done) break;
            const kind = try statement.columnEnum(ArtifactKind, 0);
            const key = try statement.columnArtifactKey(1);
            try dependencies.append(allocator, .{
                .kind = kind,
                .key = key,
            });
        }
        return dependencies.toOwnedSlice(allocator);
    }

    fn upsertArtifact(
        self: *SqliteStore,
        reference: ArtifactRef,
        payload: []const u8,
        payload_digest: H256,
        payload_authentication: AuthenticationTag,
        epoch: u64,
    ) StoreError!void {
        const sql =
            "INSERT INTO artifact(" ++
            "kind,key,size,payload,payload_digest,payload_authentication," ++
            "created_epoch,used_epoch" ++
            ") VALUES(?1,?2,?3,?4,?5,?6,?7,?7) " ++
            "ON CONFLICT(kind,key) DO UPDATE SET " ++
            "size=excluded.size,payload=excluded.payload," ++
            "payload_digest=excluded.payload_digest," ++
            "payload_authentication=excluded.payload_authentication," ++
            "used_epoch=MAX(artifact.used_epoch,excluded.used_epoch);";
        var statement = try self.prepare(.upsert_artifact, sql);
        defer statement.deinit();
        try self.bindReference(&statement, reference);
        try statement.bindInt64(3, @intCast(payload.len));
        // The lease clears every binding before this caller-owned slice expires.
        try statement.bindBlobBorrowed(4, payload);
        try statement.bindBlobOwned(5, payload_digest.bytes());
        try statement.bindBlobOwned(6, &payload_authentication);
        try statement.bindInt64(7, @intCast(epoch));
        if (try statement.step() != .done) return error.Corrupt;
    }

    fn replaceDependencies(
        self: *SqliteStore,
        reference: ArtifactRef,
        dependencies: []const ArtifactRef,
    ) StoreError!void {
        var delete_statement = try self.prepare(
            .delete_dependencies,
            "DELETE FROM dependency WHERE owner_kind=?1 AND owner_key=?2;",
        );
        defer delete_statement.deinit();
        try self.bindReference(&delete_statement, reference);
        if (try delete_statement.step() != .done) return error.Corrupt;

        if (dependencies.len == 0) return;
        var insert_statement = try self.prepare(
            .insert_dependency,
            "INSERT INTO dependency(owner_kind,owner_key,dependency_kind,dependency_key) " ++
                "VALUES(?1,?2,?3,?4);",
        );
        defer insert_statement.deinit();
        for (dependencies) |dependency| {
            try insert_statement.reset();
            try insert_statement.clearBindings();
            try self.bindReference(&insert_statement, reference);
            try insert_statement.bindEnum(3, dependency.kind);
            try insert_statement.bindBlobOwned(4, dependency.key.bytes());
            if (try insert_statement.step() != .done) return error.Corrupt;
        }
    }

    fn loadStateInit(self: *SqliteStore) InitError!PersistentState {
        return self.loadState() catch |err| return mapInitError(err);
    }

    fn loadState(self: *SqliteStore) StoreError!PersistentState {
        var statement = try self.prepare(
            .load_cache_state,
            "SELECT epoch,entry_count,logical_bytes " ++
                "FROM cache_state WHERE singleton=1;",
        );
        defer statement.deinit();
        if (try statement.step() != .row) return error.Corrupt;
        const epoch = try statement.columnNonNegativeU64(0);
        const entries = try statement.columnNonNegativeU64(1);
        const logical_bytes = try statement.columnNonNegativeU64(2);
        if (try statement.step() != .done) return error.Corrupt;
        return .{
            .epoch = epoch,
            .entries = entries,
            .logical_bytes = logical_bytes,
        };
    }

    fn storeEpoch(self: *SqliteStore, epoch: u64) StoreError!void {
        if (epoch > std.math.maxInt(i64)) return error.Unavailable;
        var statement = try self.prepare(
            .store_epoch,
            "UPDATE cache_state SET epoch=MAX(epoch,?1) WHERE singleton=1;",
        );
        defer statement.deinit();
        try statement.bindInt64(1, @intCast(epoch));
        if (try statement.step() != .done) return error.Corrupt;
    }

    fn recordAccessLocked(
        self: *SqliteStore,
        reference: ArtifactRef,
        used_epoch: u64,
    ) void {
        if (self.access_flush_interval == 0 or self.max_pending_accesses == 0) return;

        if (!self.pending_accesses.contains(reference)) {
            if (self.pending_accesses.count() >= @as(usize, self.max_pending_accesses)) {
                self.flushPendingAccessesLocked() catch {
                    _ = self.maintenance_failure_count.fetchAdd(1, .monotonic);
                    _ = self.dropped_access_update_count.fetchAdd(1, .monotonic);
                    return;
                };
            }
            self.pending_accesses.put(self.allocator, reference, {}) catch {
                _ = self.maintenance_failure_count.fetchAdd(1, .monotonic);
                _ = self.dropped_access_update_count.fetchAdd(1, .monotonic);
                return;
            };
        }
        self.pending_access_events +|= 1;
        const interval: u64 = self.access_flush_interval;
        const stale = self.epoch >= used_epoch and self.epoch - used_epoch >= interval;
        if (self.pending_access_events < interval and !stale) return;
        self.flushPendingAccessesLocked() catch {
            _ = self.maintenance_failure_count.fetchAdd(1, .monotonic);
        };
    }

    /// Requires `mutex` and no active transaction. Access aging is advisory,
    /// so callers that serve cache hits deliberately convert failures into a
    /// maintenance statistic rather than failing compilation.
    fn flushPendingAccessesLocked(self: *SqliteStore) StoreError!void {
        if (self.pending_accesses.count() == 0) return;
        var transaction = try Transaction.begin(self.lockedDatabase(), .immediate);
        defer transaction.rollbackUnlessCommitted();
        var state = try self.loadState();
        const update_count = try self.applyPendingAccessesInTransaction(&state);
        try self.storeEpoch(state.epoch);
        try transaction.commit();
        self.finishCommittedAccessFlush(update_count);
        self.publishState(state);
    }

    /// Requires `mutex` and an active immediate transaction. The pending map is
    /// retained until the caller commits so rollback never loses access data.
    fn applyPendingAccessesInTransaction(
        self: *SqliteStore,
        state: *PersistentState,
    ) StoreError!u64 {
        const update_count: u64 = @intCast(self.pending_accesses.count());
        if (update_count == 0) return 0;
        const access_epoch = try nextEpoch(state);
        var statement = try self.prepare(
            .update_access,
            "UPDATE artifact SET used_epoch=MAX(used_epoch,?3) " ++
                "WHERE kind=?1 AND key=?2;",
        );
        defer statement.deinit();
        var iterator = self.pending_accesses.keyIterator();
        while (iterator.next()) |reference| {
            try statement.reset();
            try statement.clearBindings();
            try self.bindReference(&statement, reference.*);
            try statement.bindInt64(3, @intCast(access_epoch));
            if (try statement.step() != .done) return error.Corrupt;
        }
        return update_count;
    }

    fn finishCommittedAccessFlush(self: *SqliteStore, update_count: u64) void {
        if (update_count == 0) return;
        self.pending_accesses.clearRetainingCapacity();
        self.pending_access_events = 0;
        _ = self.access_flush_count.fetchAdd(1, .monotonic);
        _ = self.access_update_count.fetchAdd(update_count, .monotonic);
    }

    const OldestRecord = struct {
        reference: ArtifactRef,
        size: u64,
    };

    fn selectOldestRecord(self: *SqliteStore) StoreError!?OldestRecord {
        var statement = try self.prepare(
            .select_oldest,
            "SELECT kind,key,size FROM artifact " ++
                "ORDER BY used_epoch,created_epoch,kind,key LIMIT 1;",
        );
        defer statement.deinit();
        if (try statement.step() == .done) return null;
        const kind = try statement.columnEnum(ArtifactKind, 0);
        const key = try statement.columnArtifactKey(1);
        const size = try statement.columnNonNegativeU64(2);
        return .{
            .reference = .{
                .kind = kind,
                .key = key,
            },
            .size = size,
        };
    }

    fn deleteRecord(self: *SqliteStore, reference: ArtifactRef) StoreError!void {
        var dependency_statement = try self.prepare(
            .delete_dependencies,
            "DELETE FROM dependency WHERE owner_kind=?1 AND owner_key=?2;",
        );
        defer dependency_statement.deinit();
        try self.bindReference(&dependency_statement, reference);
        if (try dependency_statement.step() != .done) return error.Corrupt;

        var artifact_statement = try self.prepare(
            .delete_artifact,
            "DELETE FROM artifact WHERE kind=?1 AND key=?2;",
        );
        defer artifact_statement.deinit();
        try self.bindReference(&artifact_statement, reference);
        if (try artifact_statement.step() != .done) return error.Corrupt;
    }

    fn pruneToLimitsInTransaction(
        self: *SqliteStore,
        state: *PersistentState,
        limits: ArtifactStoreModule.CacheLimits,
    ) StoreError!PruneReport {
        const before = summaryFromState(state.*);
        var removed_entries: u64 = 0;
        var removed_bytes: u64 = 0;
        while (state.entries > limits.max_entries or state.logical_bytes > limits.max_bytes) {
            const oldest = (try self.selectOldestRecord()) orelse return error.Corrupt;
            try self.deleteRecord(oldest.reference);
            state.entries -= 1;
            state.logical_bytes -= oldest.size;
            removed_entries +|= 1;
            removed_bytes +|= oldest.size;
        }
        return .{
            .before = before,
            .after = summaryFromState(state.*),
            .entries_removed = removed_entries,
            .logical_bytes_removed = removed_bytes,
        };
    }

    fn publishState(self: *SqliteStore, state: PersistentState) void {
        self.epoch = state.epoch;
        self.resident_entry_count.store(state.entries, .monotonic);
        self.resident_logical_byte_count.store(state.logical_bytes, .monotonic);
    }

    /// Borrowed facade; the store alone closes the connection under its lock.
    fn connection(self: *const SqliteStore) zqlite.Conn {
        return .{ .conn = self.database };
    }

    fn libraryFailure(
        self: *SqliteStore,
        err: anyerror,
        operation: DiagnosticOperation,
        query: QueryId,
    ) StoreError {
        const status = if (err == error.NoMem)
            sqlite.SQLITE_NOMEM
        else
            sqlite.sqlite3_extended_errcode(self.database);
        self.captureDiagnostic(status, operation, query);
        return mapStoreStatus(status);
    }

    fn prepare(
        self: *SqliteStore,
        query: QueryId,
        sql: [*:0]const u8,
    ) StoreError!Statement {
        const slot = self.idle_statements.getPtr(query);
        if (slot.*) |handle| {
            // A QueryId always names the same SQL, including on a cache hit.
            if (!std.mem.eql(u8, std.mem.span(sqlite.sqlite3_sql(handle.stmt)), std.mem.span(sql)))
                return error.Corrupt;
            slot.* = null;
            return .{
                .store = self,
                .query = query,
                .handle = handle,
                .specification = statementSpec(query),
                .reusable = true,
            };
        }
        const handle = self.connection().prepare(std.mem.span(sql)) catch |err|
            return self.libraryFailure(err, .prepare, query);
        var statement: Statement = .{
            .store = self,
            .query = query,
            .handle = handle,
            .specification = statementSpec(query),
        };
        errdefer statement.deinit();
        try statement.validateSpecification();
        statement.reusable = statement.specification != null;
        return statement;
    }

    fn finalizeStatement(self: *SqliteStore, query: QueryId, handle: zqlite.Stmt) void {
        handle.deinitErr() catch self.captureDiagnostic(
            sqlite.sqlite3_extended_errcode(self.database),
            .finalize,
            query,
        );
    }

    fn deinitStatements(self: *SqliteStore) void {
        var iterator = self.idle_statements.iterator();
        while (iterator.next()) |entry| {
            if (entry.value.*) |handle| self.finalizeStatement(entry.key, handle);
            entry.value.* = null;
        }
    }

    fn execQuery(
        self: *SqliteStore,
        operation: DiagnosticOperation,
        query: QueryId,
        sql: [*:0]const u8,
    ) StoreError!void {
        self.connection().execNoArgs(sql) catch |err|
            return self.libraryFailure(err, operation, query);
    }

    fn exec(self: *SqliteStore, sql: [*:0]const u8) StoreError!void {
        return self.execQuery(.step, .ad_hoc, sql);
    }

    fn execInitQuery(
        self: *SqliteStore,
        operation: DiagnosticOperation,
        query: QueryId,
        sql: [*:0]const u8,
    ) InitError!void {
        self.execQuery(operation, query, sql) catch |err| return mapInitError(err);
    }

    fn execInit(self: *SqliteStore, sql: [*:0]const u8) InitError!void {
        return self.execInitQuery(.step, .ad_hoc, sql);
    }

    fn scalarIntInit(
        self: *SqliteStore,
        query: QueryId,
        sql: [*:0]const u8,
    ) InitError!i64 {
        var statement = self.prepare(query, sql) catch |err| return mapInitError(err);
        defer statement.deinit();
        const result = statement.step() catch |err| return mapInitError(err);
        if (result != .row) return error.Corrupt;
        return statement.columnInt64(0) catch |err| return mapInitError(err);
    }

    fn bindReference(
        self: *SqliteStore,
        statement: *Statement,
        reference: ArtifactRef,
    ) StoreError!void {
        std.debug.assert(statement.store == self);
        try statement.bindEnum(1, reference.kind);
        try statement.bindBlobOwned(2, reference.key.bytes());
    }

    fn getAllocErased(
        context: *anyopaque,
        allocator: std.mem.Allocator,
        reference: ArtifactRef,
    ) StoreError!?Artifact {
        const self: *SqliteStore = @ptrCast(@alignCast(context));
        return self.getAlloc(allocator, reference);
    }

    fn containsErased(
        context: *anyopaque,
        reference: ArtifactRef,
    ) StoreError!bool {
        const self: *SqliteStore = @ptrCast(@alignCast(context));
        return self.contains(reference);
    }

    fn putErased(
        context: *anyopaque,
        reference: ArtifactRef,
        payload: []const u8,
        dependencies: []const ArtifactRef,
    ) StoreError!void {
        const self: *SqliteStore = @ptrCast(@alignCast(context));
        return self.put(reference, payload, dependencies);
    }

    fn beginOperation(self: *SqliteStore) void {
        self.lock();
        std.debug.assert(self.pending_diagnostic == null);
    }

    /// Constructed only by code paths that already hold `mutex`.
    fn lockedDatabase(self: *SqliteStore) LockedDatabase {
        return .{ .store = self };
    }

    fn finishOperation(self: *SqliteStore) void {
        const diagnostic = self.pending_diagnostic;
        self.pending_diagnostic = null;
        self.unlock();
        self.publishDiagnostic(diagnostic);
    }

    fn publishPendingDiagnosticUnlocked(self: *SqliteStore) void {
        const diagnostic = self.pending_diagnostic;
        self.pending_diagnostic = null;
        self.publishDiagnostic(diagnostic);
    }

    fn publishDiagnostic(
        self: *SqliteStore,
        diagnostic: ?DiagnosticSnapshot,
    ) void {
        var snapshot = diagnostic orelse return;
        if (self.diagnostic_sink) |sink| {
            sink.report(snapshot);
        } else {
            snapshot.deinit();
        }
    }

    fn captureDiagnostic(
        self: *SqliteStore,
        status: c_int,
        operation: DiagnosticOperation,
        query: ?QueryId,
    ) void {
        if (self.diagnostic_sink == null or self.pending_diagnostic != null) return;
        self.diagnostic_sequence +|= 1;
        self.pending_diagnostic = diagnosticSnapshotAlloc(
            self.allocator,
            self.diagnostic_sequence,
            self.database,
            status,
            operation,
            query,
        ) catch null;
    }

    fn checkStatus(
        self: *SqliteStore,
        operation: DiagnosticOperation,
        query: ?QueryId,
        status: c_int,
    ) StoreError!void {
        if (status == sqlite.SQLITE_OK or status == sqlite.SQLITE_ROW) return;
        self.captureDiagnostic(status, operation, query);
        return mapStoreStatus(status);
    }

    fn checkInitStatus(
        self: *SqliteStore,
        operation: DiagnosticOperation,
        query: ?QueryId,
        status: c_int,
    ) InitError!void {
        if (status == sqlite.SQLITE_OK or status == sqlite.SQLITE_ROW) return;
        self.captureDiagnostic(status, operation, query);
        return mapInitStatus(status);
    }

    fn lock(self: *SqliteStore) void {
        if (self.mutex.tryLock()) return;
        const start = std.Io.Clock.awake.now(self.io).nanoseconds;
        std.Io.Threaded.mutexLock(&self.mutex);
        const end = std.Io.Clock.awake.now(self.io).nanoseconds;
        if (end > start) {
            const elapsed = std.math.cast(u64, end - start) orelse std.math.maxInt(u64);
            _ = self.database_wait_nanoseconds.fetchAdd(elapsed, .monotonic);
        }
    }

    fn unlock(self: *SqliteStore) void {
        std.Io.Threaded.mutexUnlock(&self.mutex);
    }
};

const StatementStep = enum {
    row,
    done,
};

const SqlValueKind = enum {
    integer,
    blob,
};

const StatementSpec = struct {
    parameters: []const SqlValueKind,
    columns: []const SqlValueKind,
};

fn statementSpec(query: QueryId) ?StatementSpec {
    return switch (query) {
        .read_application_id,
        .read_schema_version,
        .count_user_tables,
        => .{ .parameters = &.{}, .columns = &.{.integer} },
        .store_authentication => .{
            .parameters = &.{.blob},
            .columns = &.{},
        },
        .read_authentication => .{
            .parameters = &.{},
            .columns = &.{.blob},
        },
        .contains_artifact => .{
            .parameters = &.{ .integer, .blob },
            .columns = &.{.integer},
        },
        .select_artifact => .{
            .parameters = &.{ .integer, .blob },
            .columns = &.{
                .integer,
                .blob,
                .blob,
                .blob,
                .integer,
            },
        },
        .select_dependencies => .{
            .parameters = &.{ .integer, .blob },
            .columns = &.{ .integer, .blob },
        },
        .upsert_artifact => .{
            .parameters = &.{
                .integer,
                .blob,
                .integer,
                .blob,
                .blob,
                .blob,
                .integer,
            },
            .columns = &.{},
        },
        .delete_dependencies, .delete_artifact => .{
            .parameters = &.{ .integer, .blob },
            .columns = &.{},
        },
        .insert_dependency => .{
            .parameters = &.{ .integer, .blob, .integer, .blob },
            .columns = &.{},
        },
        .load_cache_state => .{
            .parameters = &.{},
            .columns = &.{ .integer, .integer, .integer },
        },
        .store_epoch => .{
            .parameters = &.{.integer},
            .columns = &.{},
        },
        .update_access => .{
            .parameters = &.{ .integer, .blob, .integer },
            .columns = &.{},
        },
        .select_oldest => .{
            .parameters = &.{},
            .columns = &.{ .integer, .blob, .integer },
        },
        else => null,
    };
}

const BorrowedBlob = struct {
    bytes: []const u8,
};

/// Exclusive statement lease inside an already locked store operation. Fixed
/// queries return to the connection's bounded cache with no cursor or bindings;
/// ad hoc statements and failed resets are finalized instead.
const Statement = struct {
    store: *SqliteStore,
    query: QueryId,
    handle: ?zqlite.Stmt,
    specification: ?StatementSpec,
    reusable: bool = false,

    fn deinit(self: *Statement) void {
        const handle = self.handle orelse return;
        defer self.handle = null;
        const slot = self.store.idle_statements.getPtr(self.query);
        if (self.reusable and slot.* == null) {
            self.reset() catch {
                self.store.finalizeStatement(self.query, handle);
                return;
            };
            self.clearBindings() catch {
                self.store.finalizeStatement(self.query, handle);
                return;
            };
            slot.* = handle;
        } else {
            // Overlapping leases never alias and retain at most one idle handle.
            self.store.finalizeStatement(self.query, handle);
        }
    }

    fn raw(self: *const Statement) *sqlite.sqlite3_stmt {
        return self.handle.?.stmt;
    }

    fn validateSpecification(self: *const Statement) StoreError!void {
        const specification = self.specification orelse return;
        const expected_parameters = std.math.cast(
            c_int,
            specification.parameters.len,
        ) orelse return error.Corrupt;
        if (sqlite.sqlite3_bind_parameter_count(self.raw()) != expected_parameters) {
            return error.Corrupt;
        }
        const expected_columns = std.math.cast(
            c_int,
            specification.columns.len,
        ) orelse return error.Corrupt;
        if (sqlite.sqlite3_column_count(self.raw()) != expected_columns) {
            return error.Corrupt;
        }
    }

    fn expectParameter(
        self: *const Statement,
        index: c_int,
        first: SqlValueKind,
        second: ?SqlValueKind,
    ) StoreError!void {
        if (index <= 0) return error.Corrupt;
        const specification = self.specification orelse return;
        const offset: usize = @intCast(index - 1);
        if (offset >= specification.parameters.len) return error.Corrupt;
        const actual = specification.parameters[offset];
        if (actual != first and actual != (second orelse first)) return error.Corrupt;
    }

    fn expectColumn(
        self: *const Statement,
        column: c_int,
        first: SqlValueKind,
        second: ?SqlValueKind,
    ) StoreError!void {
        if (column < 0) return error.Corrupt;
        const specification = self.specification orelse return;
        const offset: usize = @intCast(column);
        if (offset >= specification.columns.len) return error.Corrupt;
        const actual = specification.columns[offset];
        if (actual != first and actual != (second orelse first)) return error.Corrupt;
    }

    fn reset(self: *Statement) StoreError!void {
        self.handle.?.reset() catch |err|
            return self.store.libraryFailure(err, .reset, self.query);
    }

    fn clearBindings(self: *Statement) StoreError!void {
        self.handle.?.clearBindings() catch |err|
            return self.store.libraryFailure(err, .reset, self.query);
    }

    fn step(self: *Statement) StoreError!StatementStep {
        const has_row = self.handle.?.step() catch |err|
            return self.store.libraryFailure(err, .step, self.query);
        return if (has_row) .row else .done;
    }

    fn bindInt(self: *Statement, index: c_int, value: c_int) StoreError!void {
        try self.expectParameter(index, .integer, null);
        self.handle.?.bindValue(value, @intCast(index - 1)) catch |err|
            return self.store.libraryFailure(err, .bind, self.query);
    }

    fn bindInt64(self: *Statement, index: c_int, value: i64) StoreError!void {
        try self.expectParameter(index, .integer, null);
        self.handle.?.bindValue(value, @intCast(index - 1)) catch |err|
            return self.store.libraryFailure(err, .bind, self.query);
    }

    /// Bytes remain immutable until clearBindings or deinit; reset alone is
    /// insufficient. Use only when the caller outlives the statement lease.
    fn bindBlobBorrowed(self: *Statement, index: c_int, bytes: []const u8) StoreError!void {
        try self.expectParameter(index, .blob, null);
        if (bytes.len > std.math.maxInt(c_int)) return error.ArtifactTooLarge;
        // A null pointer means SQL NULL even at length zero. An empty caller
        // slice need not have a usable pointer, so supply a static non-null one.
        const non_null: []const u8 = if (bytes.len == 0) "" else bytes;
        self.handle.?.bindValue(zqlite.blob(non_null), @intCast(index - 1)) catch |err|
            return self.store.libraryFailure(err, .bind, self.query);
    }

    fn bindBlobOwned(
        self: *Statement,
        index: c_int,
        bytes: []const u8,
    ) StoreError!void {
        try self.expectParameter(index, .blob, null);
        // zqlite binds SQLITE_STATIC. Cache keys may be temporary stack values;
        // the statement must own these bytes through step/reset/finalize.
        const allocation_size = @max(bytes.len, 1);
        const memory = sqlite.sqlite3_malloc64(allocation_size) orelse
            return error.OutOfMemory;
        if (bytes.len != 0) {
            const destination: [*]u8 = @ptrCast(memory);
            @memcpy(destination[0..bytes.len], bytes);
        }
        return self.store.checkStatus(
            .bind,
            self.query,
            sqlite.sqlite3_bind_blob64(
                self.raw(),
                index,
                memory,
                bytes.len,
                sqlite.sqlite3_free,
            ),
        );
    }

    fn bindEnum(
        self: *Statement,
        index: c_int,
        value: anytype,
    ) StoreError!void {
        const integer = std.math.cast(c_int, @intFromEnum(value)) orelse
            return error.Corrupt;
        return self.bindInt(index, integer);
    }

    fn columnInt64(self: *const Statement, column: c_int) StoreError!i64 {
        try self.expectColumn(column, .integer, null);
        if (sqlite.sqlite3_column_type(self.raw(), column) != sqlite.SQLITE_INTEGER)
            return error.Corrupt;
        return sqlite.sqlite3_column_int64(self.raw(), column);
    }

    fn columnNonNegativeU64(
        self: *const Statement,
        column: c_int,
    ) StoreError!u64 {
        const value = try self.columnInt64(column);
        if (value < 0) return error.Corrupt;
        return @intCast(value);
    }

    fn columnEnum(
        self: *const Statement,
        comptime Enum: type,
        column: c_int,
    ) StoreError!Enum {
        const value = try self.columnInt64(column);
        const Tag = std.meta.Tag(Enum);
        const tag = std.math.cast(Tag, value) orelse return error.Corrupt;
        return std.enums.fromInt(Enum, tag) orelse error.Corrupt;
    }

    fn columnBlobBorrowed(
        self: *const Statement,
        column: c_int,
    ) StoreError!BorrowedBlob {
        try self.expectColumn(column, .blob, null);
        if (sqlite.sqlite3_column_type(self.raw(), column) != sqlite.SQLITE_BLOB)
            return error.Corrupt;
        const byte_count = sqlite.sqlite3_column_bytes(self.raw(), column);
        if (byte_count < 0) return error.Corrupt;
        if (byte_count == 0) return .{ .bytes = &.{} };
        const pointer = sqlite.sqlite3_column_blob(self.raw(), column) orelse
            return error.Corrupt;
        const source: [*]const u8 = @ptrCast(pointer);
        return .{ .bytes = source[0..@intCast(byte_count)] };
    }

    fn columnBlobAlloc(
        self: *const Statement,
        allocator: std.mem.Allocator,
        column: c_int,
    ) StoreError![]u8 {
        const borrowed = try self.columnBlobBorrowed(column);
        return allocator.dupe(u8, borrowed.bytes);
    }

    fn columnH256(self: *const Statement, column: c_int) StoreError!H256 {
        const borrowed = try self.columnBlobBorrowed(column);
        if (borrowed.bytes.len != H256.size) return error.Corrupt;
        var bytes: [H256.size]u8 = undefined;
        @memcpy(&bytes, borrowed.bytes);
        return H256.fromArray(bytes);
    }

    fn columnAuthenticationTag(
        self: *const Statement,
        column: c_int,
    ) StoreError!AuthenticationTag {
        const borrowed = try self.columnBlobBorrowed(column);
        if (borrowed.bytes.len != HmacSha256.mac_length) return error.Corrupt;
        var bytes: AuthenticationTag = undefined;
        @memcpy(&bytes, borrowed.bytes);
        return bytes;
    }

    fn columnArtifactKey(
        self: *const Statement,
        column: c_int,
    ) StoreError!ArtifactKey {
        const digest = try self.columnH256(column);
        return ArtifactKey.fromDigest(digest);
    }
};

const LockedDatabase = struct {
    store: *SqliteStore,
};

const TransactionMode = enum {
    deferred,
    immediate,
    exclusive,
};

const TransactionState = enum {
    active,
    committed,
    rolled_back,
};

/// Transaction over a capability produced only while the store mutex is held.
const Transaction = struct {
    database: LockedDatabase,
    state: TransactionState = .active,

    fn begin(
        database: LockedDatabase,
        mode: TransactionMode,
    ) StoreError!Transaction {
        const command: struct {
            query: QueryId,
            sql: [*:0]const u8,
        } = switch (mode) {
            .deferred => .{ .query = .begin_deferred, .sql = "BEGIN;" },
            .immediate => .{ .query = .begin_immediate, .sql = "BEGIN IMMEDIATE;" },
            .exclusive => .{ .query = .begin_exclusive, .sql = "BEGIN EXCLUSIVE;" },
        };
        try database.store.execQuery(.begin, command.query, command.sql);
        return .{ .database = database };
    }

    fn commit(self: *Transaction) StoreError!void {
        std.debug.assert(self.state == .active);
        try self.database.store.execQuery(.commit, .commit, "COMMIT;");
        self.state = .committed;
    }

    fn rollback(self: *Transaction) StoreError!void {
        std.debug.assert(self.state == .active);
        try self.database.store.execQuery(.rollback, .rollback, "ROLLBACK;");
        self.state = .rolled_back;
    }

    fn rollbackUnlessCommitted(self: *Transaction) void {
        if (self.state != .active) return;
        self.rollback() catch {}; // zlinter-disable-current-line no_swallow_error - best-effort cleanup preserves the initiating operation error and diagnostic
    }
};

fn diagnosticSnapshotAlloc(
    allocator: std.mem.Allocator,
    sequence: u64,
    database: ?*sqlite.sqlite3,
    status: c_int,
    operation: DiagnosticOperation,
    query: ?QueryId,
) std.mem.Allocator.Error!DiagnosticSnapshot {
    const extended_code = if (database) |handle|
        sqlite.sqlite3_extended_errcode(handle)
    else
        status;
    const message_pointer = if (database) |handle|
        sqlite.sqlite3_errmsg(handle)
    else
        sqlite.sqlite3_errstr(status);
    const message = if (message_pointer == null)
        "SQLite operation failed"
    else
        std.mem.span(message_pointer);
    return .{
        .allocator = allocator,
        .sequence = sequence,
        .operation = operation,
        .primary_code = extended_code & 0xff,
        .extended_code = extended_code,
        .query = query,
        .message = try allocator.dupe(u8, message),
    };
}

fn publishStandaloneDiagnostic(
    allocator: std.mem.Allocator,
    sink: ?DiagnosticSink,
    database: ?*sqlite.sqlite3,
    status: c_int,
    operation: DiagnosticOperation,
    query: ?QueryId,
) void {
    const destination = sink orelse return;
    const snapshot = diagnosticSnapshotAlloc(
        allocator,
        1,
        database,
        status,
        operation,
        query,
    ) catch return;
    destination.report(snapshot);
}

fn nextEpoch(state: *PersistentState) StoreError!u64 {
    if (state.epoch >= std.math.maxInt(i64)) return error.Unavailable;
    state.epoch += 1;
    return state.epoch;
}

fn summaryFromState(state: PersistentState) Summary {
    return .{
        .entries = state.entries,
        .logical_bytes = state.logical_bytes,
        .epoch = state.epoch,
    };
}

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

fn databaseAuthentication(key: AuthenticationKey) AuthenticationTag {
    var result: AuthenticationTag = undefined;
    HmacSha256.create(&result, database_authentication_domain, &key);
    return result;
}

fn artifactAuthentication(
    key: AuthenticationKey,
    reference: ArtifactRef,
    payload: []const u8,
    dependencies: []const ArtifactRef,
) AuthenticationTag {
    var authentication = HmacSha256.init(&key);
    authentication.update(artifact_authentication_domain);
    authentication.update(&.{@intFromEnum(reference.kind)});
    authentication.update(reference.key.bytes());
    updateAuthenticationLength(&authentication, payload.len);
    authentication.update(payload);
    updateAuthenticationLength(&authentication, dependencies.len);
    for (dependencies) |dependency| {
        authentication.update(&.{@intFromEnum(dependency.kind)});
        authentication.update(dependency.key.bytes());
    }
    var result: AuthenticationTag = undefined;
    authentication.final(&result);
    return result;
}

fn updateAuthenticationLength(authentication: *HmacSha256, length: usize) void {
    var encoded: [8]u8 = undefined;
    std.mem.writeInt(u64, &encoded, @intCast(length), .big);
    authentication.update(&encoded);
}

const secure_file_permissions = if (@hasDecl(std.Io.File.Permissions, "fromMode"))
    std.Io.File.Permissions.fromMode(0o600)
else
    std.Io.File.Permissions.default_file;

fn ensureDatabaseFilePermissions(io: std.Io, path: []const u8) SqliteStore.InitError!void {
    const cwd = std.Io.Dir.cwd();
    var created = cwd.createFile(io, path, .{
        .read = true,
        .truncate = false,
        .exclusive = true,
        .permissions = secure_file_permissions,
    }) catch |err| switch (err) {
        error.PathAlreadyExists => null,
        else => return error.Unavailable,
    };
    if (created) |*file| {
        defer file.close(io);
        file.setPermissions(io, secure_file_permissions) catch return error.Unavailable;
        return;
    }
    cwd.setFilePermissions(
        io,
        path,
        secure_file_permissions,
        .{ .follow_symlinks = false },
    ) catch return error.Unavailable;
}

fn mapStoreStatus(status: c_int) StoreError {
    return switch (status & 0xff) {
        sqlite.SQLITE_NOMEM => error.OutOfMemory,
        sqlite.SQLITE_CORRUPT, sqlite.SQLITE_NOTADB => error.Corrupt,
        sqlite.SQLITE_BUSY, sqlite.SQLITE_LOCKED => error.Unavailable,
        else => error.Unavailable,
    };
}

fn mapInitStatus(status: c_int) SqliteStore.InitError {
    return switch (status & 0xff) {
        sqlite.SQLITE_NOMEM => error.OutOfMemory,
        sqlite.SQLITE_CORRUPT, sqlite.SQLITE_NOTADB => error.Corrupt,
        sqlite.SQLITE_BUSY, sqlite.SQLITE_LOCKED => error.Unavailable,
        else => error.Unavailable,
    };
}

fn mapInitError(err: (StoreError || SqliteStore.InitError)) SqliteStore.InitError {
    return switch (err) {
        error.OutOfMemory => error.OutOfMemory,
        error.AuthenticationFailed => error.AuthenticationFailed,
        error.Corrupt => error.Corrupt,
        error.IncompatibleSchema => error.IncompatibleSchema,
        error.NewerSchema => error.NewerSchema,
        else => error.Unavailable,
    };
}

fn testPathAlloc(allocator: std.mem.Allocator, temporary: *const std.testing.TmpDir) ![]u8 {
    return std.fmt.allocPrint(
        allocator,
        ".zig-cache/tmp/{s}/cache.sqlite",
        .{&temporary.sub_path},
    );
}

const test_authentication_key: AuthenticationKey = [_]u8{0x5a} ** 32;

fn testStoreInit(
    allocator: std.mem.Allocator,
    io: std.Io,
    path: []const u8,
) SqliteStore.InitError!SqliteStore {
    return SqliteStore.init(allocator, io, path, test_authentication_key);
}

fn testStoreInitWithOptions(
    allocator: std.mem.Allocator,
    io: std.Io,
    path: []const u8,
    options: Options,
) SqliteStore.InitError!SqliteStore {
    return SqliteStore.initWithOptions(
        allocator,
        io,
        path,
        test_authentication_key,
        options,
    );
}

fn testReference(kind: ArtifactKind, label: []const u8) ArtifactRef {
    const PhaseKey = @import("phase_key.zig");
    var builder = PhaseKey.PhaseKeyBuilder.init(
        kind,
        PhaseKey.CompilerFingerprint.init("sqlite-budget-test"),
    );
    builder.addInputBytes(label);
    return .{ .kind = kind, .key = builder.finish() };
}

fn testUninitializedStore(path: [:0]const u8) !SqliteStore {
    var database: ?*sqlite.sqlite3 = null;
    const status = sqlite.sqlite3_open_v2(path.ptr, &database, sqlite.SQLITE_OPEN_READWRITE | sqlite.SQLITE_OPEN_CREATE, null);
    if (status != sqlite.SQLITE_OK) {
        if (database) |handle| _ = sqlite.sqlite3_close_v2(handle);
        return mapInitStatus(status);
    }
    const options: Options = .{};
    return .{
        .allocator = std.testing.allocator,
        .io = std.testing.io,
        .database = database.?,
        .authentication_key = test_authentication_key,
        .limits = options.limits,
        .access_flush_interval = options.access_flush_interval,
        .max_pending_accesses = options.max_pending_accesses,
        .diagnostic_sink = null,
    };
}

test "SQLite initialization rolls back the schema if authentication cannot be written" {
    const Injection = struct {
        fn authorize(_: ?*anyopaque, action: c_int, table: [*c]const u8, _: [*c]const u8, _: [*c]const u8, _: [*c]const u8) callconv(.c) c_int {
            if (action == sqlite.SQLITE_INSERT and table != null and std.mem.eql(u8, std.mem.span(table), "cache_authentication"))
                return sqlite.SQLITE_DENY;
            return sqlite.SQLITE_OK;
        }
    };
    var store = try testUninitializedStore(":memory:");
    defer store.deinit();
    try std.testing.expectEqual(sqlite.SQLITE_OK, sqlite.sqlite3_set_authorizer(store.database, Injection.authorize, null));
    try std.testing.expectError(error.Unavailable, store.initializeSchema());
    try std.testing.expectEqual(sqlite.SQLITE_OK, sqlite.sqlite3_set_authorizer(store.database, null, null));
    try std.testing.expectEqual(@as(i64, 0), try store.scalarIntInit(.ad_hoc, "PRAGMA application_id;"));
    try std.testing.expectEqual(@as(i64, 0), try store.scalarIntInit(.ad_hoc, "PRAGMA user_version;"));
    try std.testing.expectEqual(@as(i64, 0), try store.scalarIntInit(.ad_hoc, "SELECT count(*) FROM sqlite_schema WHERE type='table';"));
    try store.initializeSchema();
    try store.verifyAuthentication();
}

test "SQLite initialization rechecks a database created by another connection" {
    const Injection = struct {
        path: []const u8,
        ran: bool = false,
        failure: ?anyerror = null,

        fn authorize(context: ?*anyopaque, action: c_int, pragma: [*c]const u8, _: [*c]const u8, _: [*c]const u8, _: [*c]const u8) callconv(.c) c_int {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            if (!self.ran and action == sqlite.SQLITE_PRAGMA and pragma != null and std.mem.eql(u8, std.mem.span(pragma), "user_version")) {
                self.ran = true;
                var peer = testStoreInit(std.testing.allocator, std.testing.io, self.path) catch |err| {
                    self.failure = err;
                    return sqlite.SQLITE_DENY;
                };
                peer.deinit();
            }
            return sqlite.SQLITE_OK;
        }
    };
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const path_z = try std.testing.allocator.dupeSentinel(u8, path, 0);
    defer std.testing.allocator.free(path_z);
    var store = try testUninitializedStore(path_z);
    defer store.deinit();
    var injection: Injection = .{ .path = path };
    try std.testing.expectEqual(sqlite.SQLITE_OK, sqlite.sqlite3_set_authorizer(store.database, Injection.authorize, &injection));
    defer _ = sqlite.sqlite3_set_authorizer(store.database, null, null);
    try store.initializeSchema();
    try std.testing.expect(injection.ran);
    try std.testing.expect(injection.failure == null);
    try store.verifyAuthentication();
}

test "SQLite artifact store identifies authenticated cache format v2" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    try std.testing.expectEqual(
        application_id,
        try store.scalarIntInit(.ad_hoc, "PRAGMA application_id;"),
    );
    try std.testing.expectEqual(
        schema_version,
        try store.scalarIntInit(.ad_hoc, "PRAGMA user_version;"),
    );
}

test "SQLite artifact store rejects a database from another trust domain" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    var trusted = try SqliteStore.init(
        std.testing.allocator,
        std.testing.io,
        path,
        [_]u8{0x11} ** 32,
    );
    trusted.deinit();
    try std.testing.expectError(
        error.AuthenticationFailed,
        SqliteStore.init(
            std.testing.allocator,
            std.testing.io,
            path,
            [_]u8{0x22} ** 32,
        ),
    );
}

test "SQLite artifact store invalidates the unauthenticated v1 format" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    try store.execInit("PRAGMA user_version=1;");
    store.deinit();
    try std.testing.expectError(
        error.IncompatibleSchema,
        testStoreInit(std.testing.allocator, std.testing.io, path),
    );
}

test "SQLite artifact store persists dependencies across restart" {
    const PhaseKey = @import("phase_key.zig");
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    const compiler = PhaseKey.CompilerFingerprint.init("sqlite-test");
    var owner_builder = PhaseKey.PhaseKeyBuilder.init(.metadata, compiler);
    owner_builder.addInputBytes("owner");
    const owner: ArtifactRef = .{ .kind = .metadata, .key = owner_builder.finish() };
    var dependency_builder = PhaseKey.PhaseKeyBuilder.init(.creation_machine, compiler);
    dependency_builder.addInputBytes("dependency");
    const dependency: ArtifactRef = .{
        .kind = .creation_machine,
        .key = dependency_builder.finish(),
    };

    var first = try testStoreInit(std.testing.allocator, std.testing.io, path);
    try first.put(owner, "metadata", &.{ dependency, dependency });
    first.deinit();

    var reopened = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer reopened.deinit();
    try std.testing.expect(try reopened.artifactStore().contains(owner));
    var artifact = (try reopened.getAlloc(std.testing.allocator, owner)).?;
    defer artifact.deinit();
    try std.testing.expectEqualStrings("metadata", artifact.payload);
    try std.testing.expectEqual(@as(usize, 1), artifact.dependencies.len);
    try std.testing.expect(artifact.dependencies[0].eql(dependency));
}

test "SQLite typed rows preserve empty blobs and reject invalid blob types" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const reference = testReference(.exact_response, "typed-empty-payload");

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    try store.put(reference, "", &.{});
    var empty = (try store.getAlloc(std.testing.allocator, reference)).?;
    try std.testing.expectEqual(@as(usize, 0), empty.payload.len);
    empty.deinit();

    try store.exec("UPDATE artifact SET payload=1;");
    try std.testing.expectError(
        error.Corrupt,
        store.getAlloc(std.testing.allocator, reference),
    );
}

test "SQLite owned blob bindings copy and isolate caller bytes" {
    const allocator = std.testing.allocator;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(allocator, &temporary);
    defer allocator.free(path);
    var store = try testStoreInit(allocator, std.testing.io, path);
    defer store.deinit();
    const payload = try allocator.alloc(u8, 1024 * 1024);
    defer allocator.free(payload);
    @memset(payload, 0x5a);
    store.beginOperation();
    defer store.finishOperation();
    var statement = try store.prepare(.ad_hoc, "SELECT ?1;");
    defer statement.deinit();
    try statement.bindBlobOwned(1, payload);
    try std.testing.expectEqual(.row, try statement.step());
    const bound = try statement.columnBlobBorrowed(0);
    try std.testing.expect(bound.bytes.ptr != payload.ptr);
    try std.testing.expectEqualSlices(u8, payload, bound.bytes);
    payload[0] = 0xff;
    try std.testing.expectEqual(@as(u8, 0x5a), bound.bytes[0]);
}

test "SQLite borrowed blob bindings avoid a payload copy and preserve empty blobs" {
    const allocator = std.testing.allocator;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(allocator, &temporary);
    defer allocator.free(path);
    var store = try testStoreInit(allocator, std.testing.io, path);
    defer store.deinit();
    const payload = try allocator.alloc(u8, 1024 * 1024);
    defer allocator.free(payload);
    @memset(payload, 0x5a);
    store.beginOperation();
    defer store.finishOperation();
    var statement = try store.prepare(.ad_hoc, "SELECT ?1;");
    defer statement.deinit();
    try statement.bindBlobBorrowed(1, payload);
    try std.testing.expectEqual(.row, try statement.step());
    const bound = try statement.columnBlobBorrowed(0);
    try std.testing.expectEqual(payload.ptr, bound.bytes.ptr);
    try std.testing.expectEqual(payload.len, bound.bytes.len);
    try statement.reset();
    try statement.clearBindings();
    var empty: []const u8 = undefined;
    empty.len = 0;
    try statement.bindBlobBorrowed(1, empty);
    try std.testing.expectEqual(.row, try statement.step());
    try std.testing.expectEqual(@as(usize, 0), (try statement.columnBlobBorrowed(0)).bytes.len);
}

test "SQLite payload writes release caller storage after success and bind failure" {
    const allocator = std.testing.allocator;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(allocator, &temporary);
    defer allocator.free(path);
    var store = try testStoreInit(allocator, std.testing.io, path);
    defer store.deinit();
    const reference = testReference(.exact_response, "borrowed-payload");
    {
        const payload = try allocator.alloc(u8, 1024 * 1024);
        defer allocator.free(payload);
        @memset(payload, 0x5a);
        for ([_]bool{ false, true }) |fail_bind| {
            // Fail on the payload bind after the key and size have been rebound.
            const previous_limit = sqlite.sqlite3_limit(store.database, sqlite.SQLITE_LIMIT_LENGTH, if (fail_bind) 4096 else -1);
            defer _ = sqlite.sqlite3_limit(store.database, sqlite.SQLITE_LIMIT_LENGTH, previous_limit);
            if (fail_bind) {
                try std.testing.expectError(error.Unavailable, store.put(reference, payload, &.{}));
            } else {
                try store.put(reference, payload, &.{});
            }
            const idle = store.idle_statements.get(.upsert_artifact).?;
            const expanded = sqlite.sqlite3_expanded_sql(idle.stmt) orelse return error.OutOfMemory;
            defer sqlite.sqlite3_free(expanded);
            try std.testing.expect(std.mem.find(u8, std.mem.span(expanded), "VALUES(NULL,NULL,NULL,NULL,NULL,NULL,NULL,NULL)") != null);
        }
        @memset(payload, 0xff);
    }
    var original = (try store.getAlloc(allocator, reference)).?;
    defer original.deinit();
    try std.testing.expectEqual(@as(usize, 1024 * 1024), original.payload.len);
    for (original.payload) |byte| try std.testing.expectEqual(@as(u8, 0x5a), byte);
    try store.put(reference, "replacement", &.{});
    var replacement = (try store.getAlloc(allocator, reference)).?;
    defer replacement.deinit();
    try std.testing.expectEqualStrings("replacement", replacement.payload);
}

test "SQLite repeated artifact lookups reuse preparation" {
    const PreparationCount = struct {
        selects: usize = 0,

        fn authorize(context: ?*anyopaque, action: c_int, _: [*c]const u8, _: [*c]const u8, _: [*c]const u8, _: [*c]const u8) callconv(.c) c_int {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            if (action == sqlite.SQLITE_SELECT) self.selects += 1;
            return sqlite.SQLITE_OK;
        }
    };
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    const present = testReference(.exact_response, "present");
    const missing = testReference(.exact_response, "missing");
    try store.put(present, "payload", &.{});
    var count: PreparationCount = .{};
    try std.testing.expectEqual(sqlite.SQLITE_OK, sqlite.sqlite3_set_authorizer(store.database, PreparationCount.authorize, &count));
    defer _ = sqlite.sqlite3_set_authorizer(store.database, null, null);
    try std.testing.expect(try store.contains(present));
    try std.testing.expect(!try store.contains(missing));
    try std.testing.expect(try store.contains(present));
    try std.testing.expectEqual(@as(usize, 1), count.selects);
}

test "SQLite statement leases clear bindings and cursors without aliasing" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    const present = testReference(.exact_response, "present");
    try store.put(present, "payload", &.{});
    store.beginOperation();
    defer store.finishOperation();
    const sql = "SELECT 1 FROM artifact WHERE kind=?1 AND key=?2;";
    var first = try store.prepare(.contains_artifact, sql);
    defer first.deinit();
    var second = try store.prepare(.contains_artifact, sql);
    defer second.deinit();
    try std.testing.expect(first.raw() != second.raw());
    try store.bindReference(&first, present);
    try std.testing.expectEqual(.row, try first.step());
    try std.testing.expectEqual(.done, try second.step());
    const retained = first.raw();
    first.deinit();
    second.deinit();
    try std.testing.expectEqual(retained, store.idle_statements.get(.contains_artifact).?.stmt);
    try std.testing.expectEqual(@as(c_int, 0), sqlite.sqlite3_stmt_busy(retained));
    const expanded = sqlite.sqlite3_expanded_sql(retained) orelse return error.OutOfMemory;
    defer sqlite.sqlite3_free(expanded);
    try std.testing.expectEqualStrings("SELECT 1 FROM artifact WHERE kind=NULL AND key=NULL;", std.mem.span(expanded));
    try std.testing.expectError(error.Corrupt, store.prepare(.contains_artifact, "SELECT 1;"));
    // A schema change must recompile the cached statement on its next step.
    try store.exec("CREATE INDEX artifact_size ON artifact(size);");
    var reused = try store.prepare(.contains_artifact, sql);
    defer reused.deinit();
    try store.bindReference(&reused, present);
    try std.testing.expectEqual(.row, try reused.step());
    reused.deinit();
    var ad_hoc = try store.prepare(.ad_hoc, "SELECT 42;");
    ad_hoc.deinit();
    store.deinitStatements();
    try std.testing.expect(sqlite.sqlite3_next_stmt(store.database, null) == null);
}

test "SQLite cached writes discard failed statements and recover after rollback" {
    const Recorder = struct {
        snapshot: ?DiagnosticSnapshot = null,

        fn report(context: ?*anyopaque, snapshot: DiagnosticSnapshot) void {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            if (self.snapshot) |*previous| previous.deinit();
            self.snapshot = snapshot;
        }
    };
    var recorder: Recorder = .{};
    defer if (recorder.snapshot) |*snapshot| snapshot.deinit();
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    var store = try testStoreInitWithOptions(std.testing.allocator, std.testing.io, path, .{
        .diagnostic_sink = .{ .context = &recorder, .report_fn = Recorder.report },
    });
    defer store.deinit();
    const reference = testReference(.exact_response, "rollback");
    try store.put(reference, "original", &.{});
    try std.testing.expect(store.idle_statements.get(.upsert_artifact) != null);
    try store.exec("CREATE TEMP TRIGGER reject_artifact BEFORE INSERT ON artifact BEGIN SELECT RAISE(ABORT,'injected'); END;");
    try std.testing.expectError(error.Unavailable, store.put(reference, "rejected", &.{}));
    try std.testing.expect(store.idle_statements.get(.upsert_artifact) == null);
    try std.testing.expectEqual(.step, recorder.snapshot.?.operation);
    try std.testing.expectEqual(.upsert_artifact, recorder.snapshot.?.query.?);
    try std.testing.expectEqual(sqlite.SQLITE_CONSTRAINT_TRIGGER, recorder.snapshot.?.extended_code);
    var original = (try store.getAlloc(std.testing.allocator, reference)).?;
    defer original.deinit();
    try std.testing.expectEqualStrings("original", original.payload);
    try store.exec("DROP TRIGGER reject_artifact;");
    try store.put(reference, "replacement", &.{});
    var replacement = (try store.getAlloc(std.testing.allocator, reference)).?;
    defer replacement.deinit();
    try std.testing.expectEqualStrings("replacement", replacement.payload);
}

test "SQLite statement specifications reject query shape drift" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    store.beginOperation();
    defer store.finishOperation();
    try std.testing.expectError(
        error.Corrupt,
        store.prepare(.contains_artifact, "SELECT 1;"),
    );
    var ad_hoc = try store.prepare(.ad_hoc, "SELECT ?;");
    defer ad_hoc.deinit();
    try std.testing.expectError(error.Corrupt, ad_hoc.bindInt(0, 1));
    try std.testing.expectError(error.Corrupt, ad_hoc.bindInt64(-1, 1));
}

test "SQLite transaction guard rolls back an interrupted operation" {
    const Injection = struct {
        fn run(store: *SqliteStore, reference: ArtifactRef) StoreError!void {
            store.beginOperation();
            defer store.finishOperation();
            var transaction = try Transaction.begin(store.lockedDatabase(), .immediate);
            defer transaction.rollbackUnlessCommitted();
            try store.deleteRecord(reference);
            return error.Corrupt;
        }
    };

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const reference = testReference(.metadata, "transaction-rollback");

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    try store.put(reference, "retained", &.{});
    try std.testing.expectError(error.Corrupt, Injection.run(&store, reference));
    try std.testing.expect(try store.contains(reference));
}

test "SQLite artifact store retains recent entries across restart while pruning" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const first = testReference(.metadata, "first");
    const second = testReference(.optimized_yul, "second");
    const third = testReference(.creation_machine, "third");
    const options: Options = .{
        .limits = .{ .max_entries = 2, .max_bytes = 6 },
        .access_flush_interval = 1,
    };

    var initial = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        options,
    );
    try initial.put(first, "aaa", &.{});
    try initial.put(second, "bbb", &.{first});
    var recently_used = (try initial.getAlloc(std.testing.allocator, first)).?;
    recently_used.deinit();
    initial.deinit();

    var reopened = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        options,
    );
    defer reopened.deinit();
    try reopened.put(third, "ccc", &.{});

    try std.testing.expect(try reopened.contains(first));
    try std.testing.expect(!try reopened.contains(second));
    try std.testing.expect(try reopened.contains(third));
    const summary = try reopened.summary();
    try std.testing.expectEqual(@as(u64, 2), summary.entries);
    try std.testing.expectEqual(@as(u64, 6), summary.logical_bytes);
    try std.testing.expectEqual(@as(u64, 1), reopened.statistics().evictions);
    try std.testing.expectEqual(
        @as(i64, 0),
        try reopened.scalarIntInit(.ad_hoc, "SELECT COUNT(*) FROM dependency;"),
    );
}

test "SQLite artifact store enforces smaller limits when reopened" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const first = testReference(.metadata, "reopen-smaller-first");
    const second = testReference(.optimized_yul, "reopen-smaller-second");

    var initial = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .unlimited, .access_flush_interval = 1 },
    );
    try initial.put(first, "aaa", &.{});
    try initial.put(second, "bbbb", &.{first});
    var recently_used = (try initial.getAlloc(std.testing.allocator, first)).?;
    recently_used.deinit();
    initial.deinit();

    var reopened = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .{ .max_entries = 1, .max_bytes = 4 } },
    );
    defer reopened.deinit();

    try std.testing.expect(try reopened.contains(first));
    try std.testing.expect(!try reopened.contains(second));
    const summary = try reopened.summary();
    try std.testing.expectEqual(@as(u64, 1), summary.entries);
    try std.testing.expectEqual(@as(u64, 3), summary.logical_bytes);
    try std.testing.expectEqual(@as(u64, 1), reopened.statistics().evictions);
    try std.testing.expectEqual(@as(u64, 4), reopened.statistics().bytes_evicted);
    try std.testing.expectEqual(
        @as(i64, 0),
        try reopened.scalarIntInit(.ad_hoc, "SELECT COUNT(*) FROM dependency;"),
    );
}

test "SQLite artifact store enforces zero limits when reopened" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const first = testReference(.metadata, "reopen-zero-first");
    const second = testReference(.optimized_yul, "reopen-zero-second");

    var initial = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .unlimited },
    );
    try initial.put(first, "aaa", &.{});
    try initial.put(second, "bbb", &.{});
    initial.deinit();

    var reopened = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .{ .max_entries = 0, .max_bytes = 0 } },
    );
    defer reopened.deinit();

    try std.testing.expect(!try reopened.contains(first));
    try std.testing.expect(!try reopened.contains(second));
    const summary = try reopened.summary();
    try std.testing.expectEqual(@as(u64, 0), summary.entries);
    try std.testing.expectEqual(@as(u64, 0), summary.logical_bytes);
    try std.testing.expectEqual(@as(u64, 2), reopened.statistics().evictions);
    try std.testing.expectEqual(@as(u64, 6), reopened.statistics().bytes_evicted);
}

test "SQLite artifact store globally prunes after a rejected write" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const first = testReference(.metadata, "rejected-prune-first");
    const second = testReference(.optimized_yul, "rejected-prune-second");
    const rejected = testReference(.exact_response, "rejected-prune-oversized");

    var wide = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .unlimited },
    );
    defer wide.deinit();
    var narrow = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .{ .max_entries = 1, .max_bytes = 3 } },
    );
    defer narrow.deinit();

    try wide.put(first, "aaa", &.{});
    try wide.put(second, "bbb", &.{});
    try narrow.put(rejected, "oversized", &.{});

    try std.testing.expect(!try narrow.contains(first));
    try std.testing.expect(try narrow.contains(second));
    try std.testing.expect(!try narrow.contains(rejected));
    const summary = try narrow.summary();
    try std.testing.expectEqual(@as(u64, 1), summary.entries);
    try std.testing.expectEqual(@as(u64, 3), summary.logical_bytes);
    try std.testing.expectEqual(@as(u64, 1), narrow.statistics().admission_rejections);
    try std.testing.expectEqual(@as(u64, 1), narrow.statistics().evictions);
    try std.testing.expectEqual(@as(u64, 3), narrow.statistics().bytes_evicted);
}

test "SQLite artifact store rejects oversized replacements" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const reference = testReference(.exact_response, "oversized");

    var store = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .{ .max_entries = 1, .max_bytes = 3 } },
    );
    defer store.deinit();
    try store.put(reference, "old", &.{});
    try store.put(reference, "oversized", &.{});
    try std.testing.expect(!try store.contains(reference));
    const summary = try store.summary();
    try std.testing.expectEqual(@as(u64, 0), summary.entries);
    try std.testing.expectEqual(@as(u64, 0), summary.logical_bytes);
    try std.testing.expectEqual(@as(u64, 1), store.statistics().admission_rejections);
}

test "SQLite artifact stores share transactional state and manual LRU pruning" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const first = testReference(.metadata, "shared-first");
    const second = testReference(.optimized_yul, "shared-second");

    var left = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .unlimited, .access_flush_interval = 1 },
    );
    defer left.deinit();
    var right = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        .{ .limits = .unlimited, .access_flush_interval = 1 },
    );
    defer right.deinit();

    try left.put(first, "aa", &.{});
    try right.put(second, "bbb", &.{});
    const shared = try left.summary();
    try std.testing.expectEqual(@as(u64, 2), shared.entries);
    try std.testing.expectEqual(@as(u64, 5), shared.logical_bytes);

    var recent = (try right.getAlloc(std.testing.allocator, first)).?;
    recent.deinit();
    const report = try left.prune(.{ .max_entries = 1, .max_bytes = 10 });
    try std.testing.expectEqual(@as(u64, 1), report.entries_removed);
    try std.testing.expectEqual(@as(u64, 3), report.logical_bytes_removed);
    try std.testing.expect(try left.contains(first));
    try std.testing.expect(!try left.contains(second));
}

test "SQLite artifact store bounds cross-process writer contention" {
    const Recorder = struct {
        store: ?*SqliteStore = null,
        snapshot: ?DiagnosticSnapshot = null,
        reentered_after_unlock: bool = false,
        reporting: bool = false,

        fn deinit(self: *@This()) void {
            if (self.snapshot) |*snapshot| snapshot.deinit();
            self.* = undefined;
        }

        fn report(opaque_context: ?*anyopaque, snapshot_value: DiagnosticSnapshot) void {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            var snapshot = snapshot_value;
            if (self.reporting or self.snapshot != null) {
                snapshot.deinit();
                return;
            }
            self.reporting = true;
            defer self.reporting = false;
            if (self.store) |store| {
                _ = store.summary() catch {
                    self.snapshot = snapshot;
                    return;
                };
                self.reentered_after_unlock = true;
            }
            self.snapshot = snapshot;
        }
    };

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const reference = testReference(.metadata, "busy-writer");
    const options: Options = .{
        .limits = .unlimited,
        .busy_timeout_ms = 1,
    };

    var writer = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        options,
    );
    defer writer.deinit();
    var recorder: Recorder = .{};
    defer recorder.deinit();
    var contender_options = options;
    contender_options.diagnostic_sink = .{
        .context = &recorder,
        .report_fn = Recorder.report,
    };
    var contender = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        contender_options,
    );
    defer contender.deinit();
    recorder.store = &contender;

    try writer.exec("BEGIN IMMEDIATE;");
    var rolled_back = false;
    defer if (!rolled_back) writer.exec("ROLLBACK;") catch {};
    try std.testing.expectError(
        error.Unavailable,
        contender.put(reference, "payload", &.{}),
    );
    try std.testing.expect(recorder.reentered_after_unlock);
    const diagnostic = &recorder.snapshot.?;
    try std.testing.expectEqual(@as(u64, 1), diagnostic.sequence);
    try std.testing.expectEqual(DiagnosticOperation.begin, diagnostic.operation);
    try std.testing.expectEqual(@as(?QueryId, .begin_immediate), diagnostic.query);
    try std.testing.expect(
        diagnostic.primary_code == sqlite.SQLITE_BUSY or
            diagnostic.primary_code == sqlite.SQLITE_LOCKED,
    );
    try std.testing.expectEqual(
        diagnostic.primary_code,
        diagnostic.extended_code & 0xff,
    );
    try std.testing.expect(diagnostic.message.len != 0);
    try writer.exec("ROLLBACK;");
    rolled_back = true;

    try contender.put(reference, "payload", &.{});
    try std.testing.expect(try writer.contains(reference));
}

test "SQLite diagnostics reject recursive compilation through the active session" {
    const CompilerSession = @import("compiler_session.zig").CompilerSession;
    const Recorder = struct {
        session: ?*CompilerSession = null,
        input: []const u8,
        diagnostics: usize = 0,
        attempted_recursive_compile: bool = false,
        rejected_recursive_compile: bool = false,
        unexpected_recursive_result: bool = false,

        fn report(opaque_context: ?*anyopaque, snapshot_value: DiagnosticSnapshot) void {
            const self: *@This() = @ptrCast(@alignCast(opaque_context.?));
            var snapshot = snapshot_value;
            defer snapshot.deinit();
            self.diagnostics += 1;
            if (self.attempted_recursive_compile) return;
            self.attempted_recursive_compile = true;
            const session = self.session orelse {
                self.unexpected_recursive_result = true;
                return;
            };
            if (session.compile(std.testing.allocator, .{ .input = self.input })) |value| {
                var output = value;
                output.deinit();
                self.unexpected_recursive_result = true;
            } else |err| {
                self.rejected_recursive_compile = err == error.ReentrantCompilation;
                self.unexpected_recursive_result = !self.rejected_recursive_compile;
            }
        }
    };
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { let x := add(1, 2) mstore(0, x) return(0, 32) } }"}},"settings":{"optimizer":{"enabled":true},"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    const fingerprint = @import("phase_key.zig").CompilerFingerprint.init(
        "sqlite-diagnostic-reentrancy-test",
    );

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const options: Options = .{
        .limits = .unlimited,
        .busy_timeout_ms = 1,
    };

    var writer = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        options,
    );
    defer writer.deinit();
    var recorder: Recorder = .{ .input = input };
    var session_options = options;
    session_options.diagnostic_sink = .{
        .context = &recorder,
        .report_fn = Recorder.report,
    };
    var backing_store = try testStoreInitWithOptions(
        std.testing.allocator,
        std.testing.io,
        path,
        session_options,
    );
    defer backing_store.deinit();
    var session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        backing_store.artifactStore(),
    );
    defer session.deinit();
    recorder.session = &session;

    try writer.exec("BEGIN IMMEDIATE;");
    var rolled_back = false;
    defer if (!rolled_back) writer.exec("ROLLBACK;") catch {};
    var output = try session.compile(std.testing.allocator, .{ .input = input });
    defer output.deinit();
    try writer.exec("ROLLBACK;");
    rolled_back = true;

    try std.testing.expect(recorder.diagnostics != 0);
    try std.testing.expect(recorder.attempted_recursive_compile);
    try std.testing.expect(recorder.rejected_recursive_compile);
    try std.testing.expect(!recorder.unexpected_recursive_result);
    try std.testing.expectEqual(@as(u64, 1), session.statistics().reentrant_rejections);
    try std.testing.expect(session.statistics().optimizer.persistent_failures != 0);
}

test "SQLite artifact store rejects wrong and corrupt schemas" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    try store.execInit("PRAGMA user_version=999;");
    store.deinit();
    try std.testing.expectError(
        error.NewerSchema,
        testStoreInit(std.testing.allocator, std.testing.io, path),
    );

    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "corrupt.sqlite",
        .data = "not a SQLite database",
    });
    const corrupt_path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/corrupt.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(corrupt_path);
    try std.testing.expectError(
        error.Corrupt,
        testStoreInit(std.testing.allocator, std.testing.io, corrupt_path),
    );
}

test "SQLite artifact store restricts database and WAL sidecar permissions" {
    if (comptime !@hasDecl(std.Io.File.Permissions, "toMode")) return;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "cache.sqlite",
        .data = "",
    });
    try temporary.dir.setFilePermissions(
        std.testing.io,
        "cache.sqlite",
        std.Io.File.Permissions.fromMode(0o666),
        .{ .follow_symlinks = false },
    );

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    try store.put(testReference(.metadata, "permission"), "payload", &.{});
    const database_stat = try std.Io.Dir.cwd().statFile(std.testing.io, path, .{});
    try std.testing.expectEqual(
        @as(std.posix.mode_t, 0o600),
        database_stat.permissions.toMode() & 0o777,
    );

    for ([_][]const u8{ "-wal", "-shm" }) |suffix| {
        const sidecar_path = try std.fmt.allocPrint(
            std.testing.allocator,
            "{s}{s}",
            .{ path, suffix },
        );
        defer std.testing.allocator.free(sidecar_path);
        const sidecar_stat = std.Io.Dir.cwd().statFile(
            std.testing.io,
            sidecar_path,
            .{},
        ) catch |err| switch (err) {
            error.FileNotFound => continue,
            else => return err,
        };
        try std.testing.expectEqual(
            @as(std.posix.mode_t, 0o600),
            sidecar_stat.permissions.toMode() & 0o777,
        );
    }
}

test "SQLite artifact store rejects a symlinked database" {
    if (comptime @import("builtin").os.tag == .windows)
        return error.SkipZigTest;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "outside.sqlite",
        .data = "outside",
    });
    try temporary.dir.symLink(
        std.testing.io,
        "outside.sqlite",
        "cache.sqlite",
        .{},
    );
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    try std.testing.expectError(
        error.Unavailable,
        testStoreInit(std.testing.allocator, std.testing.io, path),
    );
    const target = try temporary.dir.readFileAlloc(
        std.testing.io,
        "outside.sqlite",
        std.testing.allocator,
        .limited(64),
    );
    defer std.testing.allocator.free(target);
    try std.testing.expectEqualStrings("outside", target);
}

test "SQLite artifact store rejects a modified payload" {
    const PhaseKey = @import("phase_key.zig");
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);

    const compiler = PhaseKey.CompilerFingerprint.init("sqlite-corruption-test");
    var builder = PhaseKey.PhaseKeyBuilder.init(.exact_response, compiler);
    builder.addInputBytes("request");
    const reference: ArtifactRef = .{
        .kind = .exact_response,
        .key = builder.finish(),
    };
    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    try store.put(reference, "expected", &.{});
    try store.exec(
        "UPDATE artifact SET payload=zeroblob(8) WHERE kind=1;",
    );
    try std.testing.expectError(
        error.Corrupt,
        store.getAlloc(std.testing.allocator, reference),
    );
}

test "SQLite artifact store rejects a substituted payload with a recomputed digest" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const reference = testReference(.exact_response, "authenticated-substitution");

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    try store.put(reference, "trusted deployable bytecode", &.{});

    const substituted = "attacker-selected bytecode";
    const digest = Keccak256.keccak256(substituted);
    const payload_hex = std.fmt.bytesToHex(substituted, .lower);
    var digest_bytes: [H256.size]u8 = undefined;
    @memcpy(&digest_bytes, digest.bytes());
    const digest_hex = std.fmt.bytesToHex(digest_bytes, .lower);
    const sql = try std.fmt.allocPrintSentinel(
        std.testing.allocator,
        "UPDATE artifact SET payload=x'{s}',size={d},payload_digest=x'{s}';",
        .{ payload_hex, substituted.len, digest_hex },
        0,
    );
    defer std.testing.allocator.free(sql);
    try store.exec(sql);

    try std.testing.expectError(
        error.Corrupt,
        store.getAlloc(std.testing.allocator, reference),
    );
}

test "SQLite artifact store rejects a substituted dependency set" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const reference = testReference(.exact_response, "authenticated-owner");
    const dependency = testReference(.metadata, "authenticated-dependency");

    var store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer store.deinit();
    try store.put(reference, "trusted deployable bytecode", &.{dependency});
    try store.exec("DELETE FROM dependency;");

    try std.testing.expectError(
        error.Corrupt,
        store.getAlloc(std.testing.allocator, reference),
    );
}

test "compiler session recompiles and repairs a corrupted SQLite response" {
    const CompilerSession = @import("compiler_session.zig").CompilerSession;
    const PhaseKey = @import("phase_key.zig");
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const fingerprint = PhaseKey.CompilerFingerprint.init("sqlite-repair-test");

    var first_store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    var first_session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        first_store.artifactStore(),
    );
    var expected = try first_session.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    defer expected.deinit();
    first_session.deinit();
    first_store.deinit();

    var mutator = try testStoreInit(std.testing.allocator, std.testing.io, path);
    try mutator.exec(
        "UPDATE artifact SET payload=zeroblob(size) WHERE kind=1;",
    );
    mutator.deinit();

    var reopened_store = try testStoreInit(std.testing.allocator, std.testing.io, path);
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
    try @import("common").standard_json.compareExact(expected.bytes, actual.bytes);
    try std.testing.expect(restarted_session.statistics().store_failures != 0);

    var repaired = try restarted_session.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    defer repaired.deinit();
    try @import("common").standard_json.compareExact(expected.bytes, repaired.bytes);
    try std.testing.expectEqual(
        @as(u64, 1),
        restarted_session.statistics().memory.hits,
    );
}

test "compiler session repopulates an evicted SQLite cache across restarts" {
    const CompilerSession = @import("compiler_session.zig").CompilerSession;
    const PhaseKey = @import("phase_key.zig");
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { let x := add(1, 2) mstore(0, x) return(0, 32) } }"}},"settings":{"optimizer":{"enabled":true},"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try testPathAlloc(std.testing.allocator, &temporary);
    defer std.testing.allocator.free(path);
    const fingerprint = PhaseKey.CompilerFingerprint.init("sqlite-eviction-test");

    var expected = first: {
        var first_store = try testStoreInit(std.testing.allocator, std.testing.io, path);
        defer first_store.deinit();
        var first_session = try CompilerSession.initWithBackingStore(
            std.testing.allocator,
            fingerprint,
            first_store.artifactStore(),
        );
        defer first_session.deinit();
        break :first try first_session.compiler().compile(
            std.testing.allocator,
            .{ .input = input },
        );
    };
    defer expected.deinit();

    {
        var evictor = try testStoreInit(std.testing.allocator, std.testing.io, path);
        defer evictor.deinit();
        try evictor.exec("DELETE FROM dependency; DELETE FROM artifact;");
    }

    {
        var empty_store = try testStoreInit(std.testing.allocator, std.testing.io, path);
        defer empty_store.deinit();
        var repopulating_session = try CompilerSession.initWithBackingStore(
            std.testing.allocator,
            fingerprint,
            empty_store.artifactStore(),
        );
        defer repopulating_session.deinit();
        var repopulated = try repopulating_session.compiler().compile(
            std.testing.allocator,
            .{ .input = input },
        );
        defer repopulated.deinit();
        try @import("common").standard_json.compareExact(expected.bytes, repopulated.bytes);
        try std.testing.expectEqual(
            @as(u64, 1),
            repopulating_session.statistics().persistent_misses,
        );
    }

    var repaired_store = try testStoreInit(std.testing.allocator, std.testing.io, path);
    defer repaired_store.deinit();
    var restarted_session = try CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        repaired_store.artifactStore(),
    );
    defer restarted_session.deinit();
    var actual = try restarted_session.compiler().compile(
        std.testing.allocator,
        .{ .input = input },
    );
    defer actual.deinit();
    try @import("common").standard_json.compareExact(expected.bytes, actual.bytes);
    try std.testing.expectEqual(
        @as(u64, 1),
        restarted_session.statistics().persistent_hits,
    );
}
