// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Application-facing SQLite compiler session with disposable-cache recovery.

const std = @import("std");
const common = @import("common");
const CompilerSessionModule = @import("compiler_session.zig");
const PhaseKey = @import("phase_key.zig");
const Profiler = @import("../libsolutil/profiler.zig").Profiler;
const SqliteStoreModule = @import("sqlite_store.zig");

const CompilerSession = CompilerSessionModule.CompilerSession;
const CompilerFingerprint = PhaseKey.CompilerFingerprint;
const SqliteStore = SqliteStoreModule.SqliteStore;
const AuthenticationKey = SqliteStoreModule.AuthenticationKey;

const smoke_input =
    \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
;

pub const PersistenceMode = enum {
    sqlite,
    recreated_sqlite,
    memory_only,
};

/// Owns a compiler session and, when available, its SQLite backing store.
///
/// `SqliteStore.init` reports corruption and schema incompatibility to callers.
/// This wrapper disables persistence for unidentified compiler builds, moves
/// a corrupt or incompatible database aside, retries once, and falls back to
/// the same compiler session in memory-only mode.
pub const SqliteCompilerSession = struct {
    pub const Options = struct {
        store: SqliteStoreModule.Options = .{},
        session: CompilerSession.Options = .{},
    };

    allocator: std.mem.Allocator,
    session: CompilerSession,
    store: ?*SqliteStore = null,
    quarantined_database_path: ?[]u8 = null,
    persistence_mode: PersistenceMode,

    pub fn init(
        allocator: std.mem.Allocator,
        io: std.Io,
        database_path: []const u8,
        compiler_fingerprint: CompilerFingerprint,
        authentication_key: AuthenticationKey,
    ) SqliteCompilerSession {
        return initWithOptions(
            allocator,
            io,
            database_path,
            compiler_fingerprint,
            authentication_key,
            .{},
        );
    }

    pub fn initWithOptions(
        allocator: std.mem.Allocator,
        io: std.Io,
        database_path: []const u8,
        compiler_fingerprint: CompilerFingerprint,
        authentication_key: AuthenticationKey,
        options: Options,
    ) SqliteCompilerSession {
        if (!compiler_fingerprint.isPersistentSafe())
            return memoryOnly(allocator, compiler_fingerprint, options.session, null);

        const store = allocator.create(SqliteStore) catch
            return memoryOnly(allocator, compiler_fingerprint, options.session, null);
        store.* = SqliteStore.initWithOptions(
            allocator,
            io,
            database_path,
            authentication_key,
            options.store,
        ) catch |initial_error| {
            allocator.destroy(store);
            switch (initial_error) {
                error.Corrupt, error.IncompatibleSchema => {
                    var recovery_lock = acquireRecoveryLock(
                        allocator,
                        io,
                        database_path,
                    ) catch return memoryOnly(
                        allocator,
                        compiler_fingerprint,
                        options.session,
                        null,
                    );
                    defer recovery_lock.close(io);

                    // Another process may have completed recovery before this
                    // process acquired the lock. Recheck before moving files.
                    const retry = allocator.create(SqliteStore) catch
                        return memoryOnly(
                            allocator,
                            compiler_fingerprint,
                            options.session,
                            null,
                        );
                    const retry_value: ?SqliteStore = SqliteStore.initWithOptions(
                        allocator,
                        io,
                        database_path,
                        authentication_key,
                        options.store,
                    ) catch |retry_error| switch (retry_error) {
                        error.Corrupt, error.IncompatibleSchema => null,
                        else => {
                            allocator.destroy(retry);
                            return memoryOnly(
                                allocator,
                                compiler_fingerprint,
                                options.session,
                                null,
                            );
                        },
                    };
                    if (retry_value) |value| {
                        retry.* = value;
                        return withStore(
                            allocator,
                            compiler_fingerprint,
                            retry,
                            options.session,
                            .sqlite,
                            null,
                        );
                    }
                    allocator.destroy(retry);
                    const quarantined_path = quarantineDatabase(
                        allocator,
                        io,
                        database_path,
                    ) catch return memoryOnly(
                        allocator,
                        compiler_fingerprint,
                        options.session,
                        null,
                    );
                    const replacement = allocator.create(SqliteStore) catch
                        return memoryOnly(
                            allocator,
                            compiler_fingerprint,
                            options.session,
                            quarantined_path,
                        );
                    replacement.* = SqliteStore.initWithOptions(
                        allocator,
                        io,
                        database_path,
                        authentication_key,
                        options.store,
                    ) catch {
                        allocator.destroy(replacement);
                        return memoryOnly(
                            allocator,
                            compiler_fingerprint,
                            options.session,
                            quarantined_path,
                        );
                    };
                    return withStore(
                        allocator,
                        compiler_fingerprint,
                        replacement,
                        options.session,
                        .recreated_sqlite,
                        quarantined_path,
                    );
                },
                error.AuthenticationFailed => return memoryOnly(
                    allocator,
                    compiler_fingerprint,
                    options.session,
                    null,
                ),
                else => return memoryOnly(
                    allocator,
                    compiler_fingerprint,
                    options.session,
                    null,
                ),
            }
        };
        return withStore(
            allocator,
            compiler_fingerprint,
            store,
            options.session,
            .sqlite,
            null,
        );
    }

    pub fn deinit(self: *SqliteCompilerSession) void {
        self.session.deinit();
        if (self.store) |store| {
            store.deinit();
            self.allocator.destroy(store);
        }
        if (self.quarantined_database_path) |path| self.allocator.free(path);
        self.* = undefined;
    }

    pub fn compiler(self: *SqliteCompilerSession) common.standard_json.Compiler {
        return self.session.compiler();
    }

    /// Compile one Standard JSON request through the persistent session.
    pub fn compile(
        self: *SqliteCompilerSession,
        allocator: std.mem.Allocator,
        request: common.standard_json.Request,
    ) common.standard_json.CompileError!common.standard_json.Output {
        return self.session.compile(allocator, request);
    }

    /// Profiling configuration must not change during a compilation.
    pub fn setOptimizerProfiler(
        self: *SqliteCompilerSession,
        profiler: ?*Profiler,
    ) void {
        self.session.setOptimizerProfiler(profiler);
    }

    pub fn statistics(self: *SqliteCompilerSession) CompilerSessionModule.SessionStatistics {
        return self.session.statistics();
    }

    fn withStore(
        allocator: std.mem.Allocator,
        compiler_fingerprint: CompilerFingerprint,
        store: *SqliteStore,
        session_options: CompilerSession.Options,
        persistence_mode: PersistenceMode,
        quarantined_database_path: ?[]u8,
    ) SqliteCompilerSession {
        const session = CompilerSession.initWithBackingStoreAndOptions(
            allocator,
            compiler_fingerprint,
            store.artifactStore(),
            session_options,
        ) catch {
            store.deinit();
            allocator.destroy(store);
            return memoryOnly(
                allocator,
                compiler_fingerprint,
                session_options,
                quarantined_database_path,
            );
        };
        return .{
            .allocator = allocator,
            .session = session,
            .store = store,
            .quarantined_database_path = quarantined_database_path,
            .persistence_mode = persistence_mode,
        };
    }

    fn memoryOnly(
        allocator: std.mem.Allocator,
        compiler_fingerprint: CompilerFingerprint,
        session_options: CompilerSession.Options,
        quarantined_database_path: ?[]u8,
    ) SqliteCompilerSession {
        return .{
            .allocator = allocator,
            .session = CompilerSession.initWithFingerprintAndOptions(
                allocator,
                compiler_fingerprint,
                session_options,
            ),
            .quarantined_database_path = quarantined_database_path,
            .persistence_mode = .memory_only,
        };
    }
};

const secure_lock_permissions = if (@hasDecl(std.Io.File.Permissions, "fromMode"))
    std.Io.File.Permissions.fromMode(0o600)
else
    std.Io.File.Permissions.default_file;

fn acquireRecoveryLock(
    allocator: std.mem.Allocator,
    io: std.Io,
    database_path: []const u8,
) !std.Io.File {
    const database_name = std.Io.Dir.path.basename(database_path);
    if (database_name.len == 0 or
        std.mem.eql(u8, database_name, ".") or
        std.mem.eql(u8, database_name, ".."))
    {
        return error.InvalidRecoveryLockPath;
    }

    const directory_path = try recoveryDirectoryPathAlloc(
        allocator,
        io,
        database_path,
    );
    defer allocator.free(directory_path);
    var directory = try openRecoveryDirectory(io, directory_path);
    defer directory.close(io);

    const lock_name = try std.fmt.allocPrint(
        allocator,
        "{s}.recovery.lock",
        .{database_name},
    );
    defer allocator.free(lock_name);

    var expected_inode: ?std.Io.File.INode = null;
    var file = directory.createFile(io, lock_name, .{
        .read = true,
        .truncate = false,
        .exclusive = true,
        .lock = .exclusive,
        .lock_nonblocking = true,
        .permissions = secure_lock_permissions,
        .resolve_beneath = true,
    }) catch |err| switch (err) {
        error.PathAlreadyExists => existing: {
            const path_stat = try directory.statFile(io, lock_name, .{
                .follow_symlinks = false,
            });
            try validateRecoveryLockStat(path_stat);
            expected_inode = path_stat.inode;
            break :existing try directory.openFile(io, lock_name, .{
                .mode = .read_write,
                .allow_directory = false,
                .lock = .exclusive,
                .lock_nonblocking = true,
                .follow_symlinks = false,
                .resolve_beneath = true,
            });
        },
        else => return err,
    };
    errdefer file.close(io);

    const stat = try file.stat(io);
    try validateRecoveryLockStat(stat);
    if (expected_inode) |inode| {
        if (stat.inode != inode) return error.InvalidRecoveryLock;
    }
    return file;
}

fn validateRecoveryLockStat(stat: std.Io.File.Stat) !void {
    if (stat.kind != .file or stat.nlink != 1)
        return error.InvalidRecoveryLock;
    if (comptime @import("builtin").os.tag != .windows) {
        if (stat.permissions.toMode() & 0o777 != 0o600)
            return error.InsecureRecoveryLockPermissions;
    }
}

fn recoveryDirectoryPathAlloc(
    allocator: std.mem.Allocator,
    io: std.Io,
    database_path: []const u8,
) ![]u8 {
    const relative_directory = std.Io.Dir.path.dirname(database_path) orelse ".";
    if (std.Io.Dir.path.isAbsolute(relative_directory))
        return std.Io.Dir.path.resolve(allocator, &.{relative_directory});

    const current_directory = try std.Io.Dir.cwd().realPathFileAlloc(
        io,
        ".",
        allocator,
    );
    defer allocator.free(current_directory);
    return std.Io.Dir.path.resolve(
        allocator,
        &.{ current_directory, relative_directory },
    );
}

/// Opens every path component without following symbolic links, then verifies
/// that the directory handle still names the lexically resolved cache path.
fn openRecoveryDirectory(io: std.Io, canonical: []const u8) !std.Io.Dir {
    const parsed = std.Io.Dir.path.parsePath(canonical);
    if (parsed.root.len == 0) return error.RecoveryDirectoryNotAbsolute;
    var current = try std.Io.Dir.cwd().openDir(io, parsed.root, .{
        .iterate = false,
        .follow_symlinks = false,
    });
    errdefer current.close(io);

    var component_start = parsed.root.len;
    while (component_start < canonical.len and
        std.Io.Dir.path.isSep(canonical[component_start]))
    {
        component_start += 1;
    }
    var index = component_start;
    while (index <= canonical.len) : (index += 1) {
        if (index != canonical.len and
            !std.Io.Dir.path.isSep(canonical[index]))
        {
            continue;
        }
        const component = canonical[component_start..index];
        if (component.len == 0) break;
        const next = try current.openDir(io, component, .{
            .iterate = false,
            .follow_symlinks = false,
        });
        current.close(io);
        current = next;
        component_start = index + 1;
    }

    var actual_buffer: [std.Io.Dir.max_path_bytes]u8 = undefined;
    const actual_length = try current.realPath(io, &actual_buffer);
    if (!std.mem.eql(u8, canonical, actual_buffer[0..actual_length]))
        return error.RecoveryDirectoryChanged;
    if (comptime @import("builtin").os.tag != .windows) {
        const stat = try current.stat(io);
        if (stat.permissions.toMode() & 0o022 != 0)
            return error.InsecureRecoveryDirectory;
    }
    return current;
}

fn quarantineDatabase(
    allocator: std.mem.Allocator,
    io: std.Io,
    database_path: []const u8,
) ![]u8 {
    var entropy: [8]u8 = undefined;
    std.Io.random(io, &entropy);
    const suffix = std.fmt.bytesToHex(entropy, .lower);

    const quarantined_path = try std.fmt.allocPrint(
        allocator,
        "{s}.rejected-{s}",
        .{ database_path, suffix },
    );
    errdefer allocator.free(quarantined_path);

    const cwd = std.Io.Dir.cwd();
    cwd.rename(database_path, cwd, quarantined_path, io) catch |err| switch (err) {
        error.FileNotFound => return quarantined_path,
        else => return err,
    };

    const sidecars = [_][]const u8{ "-wal", "-shm", "-journal" };
    for (sidecars) |sidecar| {
        const source_path = try std.fmt.allocPrint(
            allocator,
            "{s}{s}",
            .{ database_path, sidecar },
        );
        defer allocator.free(source_path);
        const destination_path = try std.fmt.allocPrint(
            allocator,
            "{s}{s}",
            .{ quarantined_path, sidecar },
        );
        defer allocator.free(destination_path);
        cwd.rename(source_path, cwd, destination_path, io) catch |err| switch (err) {
            error.FileNotFound => {},
            else => return err,
        };
    }
    return quarantined_path;
}

const test_authentication_key: AuthenticationKey = [_]u8{0x6b} ** 32;

fn testSessionInit(
    allocator: std.mem.Allocator,
    io: std.Io,
    database_path: []const u8,
    compiler_fingerprint: CompilerFingerprint,
) SqliteCompilerSession {
    return SqliteCompilerSession.init(
        allocator,
        io,
        database_path,
        compiler_fingerprint,
        test_authentication_key,
    );
}

fn testStoreInit(
    allocator: std.mem.Allocator,
    io: std.Io,
    database_path: []const u8,
) SqliteStore.InitError!SqliteStore {
    return SqliteStore.init(allocator, io, database_path, test_authentication_key);
}

test "SQLite compiler session quarantines a corrupt database" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);

    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "cache.sqlite",
        .data = "not a SQLite database",
    });

    var recovered = testSessionInit(
        std.testing.allocator,
        std.testing.io,
        path,
        CompilerFingerprint.init("sqlite-session-recovery-test"),
    );
    defer recovered.deinit();
    try std.testing.expectEqual(PersistenceMode.recreated_sqlite, recovered.persistence_mode);
    try std.testing.expect(recovered.quarantined_database_path != null);
    try std.Io.Dir.cwd().access(
        std.testing.io,
        recovered.quarantined_database_path.?,
        .{},
    );
    const quarantined_contents = try std.Io.Dir.cwd().readFileAlloc(
        std.testing.io,
        recovered.quarantined_database_path.?,
        std.testing.allocator,
        .limited(1024),
    );
    defer std.testing.allocator.free(quarantined_contents);
    try std.testing.expectEqualStrings("not a SQLite database", quarantined_contents);

    var output = try recovered.compiler().compile(
        std.testing.allocator,
        .{ .input = smoke_input },
    );
    defer output.deinit();
    try std.testing.expect(std.mem.find(u8, output.bytes, "bytecode") != null);

    var reopened = try testStoreInit(std.testing.allocator, std.testing.io, path);
    reopened.deinit();
}

test "SQLite compiler session does not race an active cache recovery" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "cache.sqlite",
        .data = "not a SQLite database",
    });
    var recovery_lock = try acquireRecoveryLock(
        std.testing.allocator,
        std.testing.io,
        path,
    );
    defer recovery_lock.close(std.testing.io);

    var session = testSessionInit(
        std.testing.allocator,
        std.testing.io,
        path,
        CompilerFingerprint.init("sqlite-session-recovery-race-test"),
    );
    defer session.deinit();
    try std.testing.expectEqual(PersistenceMode.memory_only, session.persistence_mode);
    try std.testing.expect(session.quarantined_database_path == null);
    const contents = try temporary.dir.readFileAlloc(
        std.testing.io,
        "cache.sqlite",
        std.testing.allocator,
        .limited(1024),
    );
    defer std.testing.allocator.free(contents);
    try std.testing.expectEqualStrings("not a SQLite database", contents);
}

test "SQLite recovery lock rejects symlinks without modifying their target" {
    if (comptime @import("builtin").os.tag == .windows)
        return error.SkipZigTest;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDir(
        std.testing.io,
        "cache",
        std.Io.Dir.Permissions.fromMode(0o700),
    );
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "outside.txt",
        .data = "outside",
        .flags = .{ .permissions = std.Io.File.Permissions.fromMode(0o644) },
    });
    {
        var target = try temporary.dir.openFile(std.testing.io, "outside.txt", .{
            .mode = .read_write,
            .allow_directory = false,
            .follow_symlinks = false,
        });
        defer target.close(std.testing.io);
        try target.setPermissions(
            std.testing.io,
            std.Io.File.Permissions.fromMode(0o644),
        );
    }
    const original_target_stat = try temporary.dir.statFile(
        std.testing.io,
        "outside.txt",
        .{},
    );
    try std.testing.expectEqual(
        @as(std.posix.mode_t, 0o644),
        original_target_stat.permissions.toMode() & 0o777,
    );
    try temporary.dir.symLink(
        std.testing.io,
        "../outside.txt",
        "cache/cache.sqlite.recovery.lock",
        .{},
    );
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache/cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);

    if (acquireRecoveryLock(std.testing.allocator, std.testing.io, path)) |lock_value| {
        var lock = lock_value;
        lock.close(std.testing.io);
        return error.TestUnexpectedResult;
    } else |_| {}

    const target_stat = try temporary.dir.statFile(
        std.testing.io,
        "outside.txt",
        .{},
    );
    try std.testing.expectEqual(
        original_target_stat.permissions.toMode() & 0o777,
        target_stat.permissions.toMode() & 0o777,
    );
    const target = try temporary.dir.readFileAlloc(
        std.testing.io,
        "outside.txt",
        std.testing.allocator,
        .limited(64),
    );
    defer std.testing.allocator.free(target);
    try std.testing.expectEqualStrings("outside", target);
}

test "SQLite recovery lock rejects hard links without modifying their target" {
    if (comptime @import("builtin").os.tag == .windows)
        return error.SkipZigTest;

    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    try temporary.dir.createDir(
        std.testing.io,
        "cache",
        std.Io.Dir.Permissions.fromMode(0o700),
    );
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "outside.txt",
        .data = "outside",
        .flags = .{ .permissions = std.Io.File.Permissions.fromMode(0o644) },
    });
    {
        var target = try temporary.dir.openFile(std.testing.io, "outside.txt", .{
            .mode = .read_write,
            .allow_directory = false,
            .follow_symlinks = false,
        });
        defer target.close(std.testing.io);
        try target.setPermissions(
            std.testing.io,
            std.Io.File.Permissions.fromMode(0o644),
        );
    }
    const original_target_stat = try temporary.dir.statFile(
        std.testing.io,
        "outside.txt",
        .{},
    );
    try std.testing.expectEqual(
        @as(std.posix.mode_t, 0o644),
        original_target_stat.permissions.toMode() & 0o777,
    );
    try temporary.dir.hardLink(
        "outside.txt",
        temporary.dir,
        "cache/cache.sqlite.recovery.lock",
        std.testing.io,
        .{},
    );
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache/cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);

    if (acquireRecoveryLock(std.testing.allocator, std.testing.io, path)) |lock_value| {
        var lock = lock_value;
        lock.close(std.testing.io);
        return error.TestUnexpectedResult;
    } else |_| {}

    const target_stat = try temporary.dir.statFile(
        std.testing.io,
        "outside.txt",
        .{},
    );
    try std.testing.expectEqual(
        original_target_stat.permissions.toMode() & 0o777,
        target_stat.permissions.toMode() & 0o777,
    );
    const target = try temporary.dir.readFileAlloc(
        std.testing.io,
        "outside.txt",
        std.testing.allocator,
        .limited(64),
    );
    defer std.testing.allocator.free(target);
    try std.testing.expectEqualStrings("outside", target);
}

test "SQLite compiler session replaces an incompatible database" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);

    var compatible = try testStoreInit(std.testing.allocator, std.testing.io, path);
    compatible.deinit();
    const contents = try temporary.dir.readFileAlloc(
        std.testing.io,
        "cache.sqlite",
        std.testing.allocator,
        .limited(1024 * 1024),
    );
    defer std.testing.allocator.free(contents);
    try std.testing.expect(contents.len >= 64);
    // SQLite stores PRAGMA application_id as a big-endian u32 at header offset
    // 68. Changing only this field leaves a valid database belonging to a
    // different application for the recovery policy to exercise.
    std.mem.writeInt(u32, contents[68..72], 0x12345678, .big);
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "cache.sqlite",
        .data = contents,
    });

    var recovered = testSessionInit(
        std.testing.allocator,
        std.testing.io,
        path,
        CompilerFingerprint.init("sqlite-session-schema-test"),
    );
    defer recovered.deinit();
    try std.testing.expectEqual(PersistenceMode.recreated_sqlite, recovered.persistence_mode);
    try std.testing.expect(recovered.quarantined_database_path != null);

    var reopened = try testStoreInit(std.testing.allocator, std.testing.io, path);
    reopened.deinit();
}

test "SQLite compiler session leaves a newer cache schema untouched" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);

    var current = try testStoreInit(std.testing.allocator, std.testing.io, path);
    current.deinit();
    const contents = try temporary.dir.readFileAlloc(
        std.testing.io,
        "cache.sqlite",
        std.testing.allocator,
        .limited(1024 * 1024),
    );
    defer std.testing.allocator.free(contents);
    std.mem.writeInt(u32, contents[60..64], 999, .big);
    try temporary.dir.writeFile(std.testing.io, .{
        .sub_path = "cache.sqlite",
        .data = contents,
    });

    var session = testSessionInit(
        std.testing.allocator,
        std.testing.io,
        path,
        CompilerFingerprint.init("sqlite-session-newer-schema-test"),
    );
    defer session.deinit();
    try std.testing.expectEqual(PersistenceMode.memory_only, session.persistence_mode);
    try std.testing.expect(session.quarantined_database_path == null);

    const preserved = try temporary.dir.readFileAlloc(
        std.testing.io,
        "cache.sqlite",
        std.testing.allocator,
        .limited(1024 * 1024),
    );
    defer std.testing.allocator.free(preserved);
    try std.testing.expectEqual(@as(u32, 999), std.mem.readInt(u32, preserved[60..64], .big));
}

test "SQLite compiler session falls back to memory" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/missing/cache.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);
    var session = testSessionInit(
        std.testing.allocator,
        std.testing.io,
        path,
        CompilerFingerprint.init("sqlite-session-fallback-test"),
    );
    defer session.deinit();
    try std.testing.expectEqual(PersistenceMode.memory_only, session.persistence_mode);
    var output = try session.compiler().compile(std.testing.allocator, .{ .input = smoke_input });
    defer output.deinit();
    try std.testing.expect(std.mem.find(u8, output.bytes, "bytecode") != null);
}
