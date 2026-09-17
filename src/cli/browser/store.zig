// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! SQLite inspection snapshots. One owner imports; HTTP workers copy query
//! results under the same connection lock. Archive browsing freezes imports.
const std = @import("std");
const zqlite = @import("zqlite");
const c = zqlite.c;
const schema = @import("schema.zig");

pub const Source = struct { name: []const u8, content: []const u8 };
pub const Origin = enum { compiled, imported };
// The bundled SQLite uses SQLITE_MAX_LENGTH=1,000,000,000 for an entire
// encoded row. Reserve space for record headers, origin, timestamp and hashes;
// label + request + output share the remaining budget. See sqlite.org/limits.html.
pub const max_document_bytes = 1_000_000_000 - 4096;
const max_query_bytes = 256 * 1024 * 1024;
pub const max_manifest_bytes = 64 * 1024 * 1024;
pub const Receipt = struct { context: []const u8, manifest: []const u8, seal: []const u8 };
/// The caller owns request/output/manifest/seal allocations (normally in a
/// phase arena). Context borrows the resumeAlloc argument.
pub const Resume = struct { id: i64, request: []const u8, output: []const u8, receipt: Receipt };

pub const Store = struct {
    db: zqlite.Conn,
    io: std.Io,
    mutex: std.Io.Mutex = .init,
    frozen: bool = false,

    pub fn open(allocator: std.mem.Allocator, io: std.Io, path: []const u8) !Store {
        if (std.mem.findScalar(u8, path, 0) != null) return error.InvalidDatabasePath;
        // SQLite NOFOLLOW also rejects symlinks in parent directories (including
        // macOS /var). Resolve only the parent; the database leaf stays guarded.
        const path_z = if (std.mem.eql(u8, path, ":memory:")) try allocator.dupeSentinel(u8, path, 0) else resolved: {
            const parent = try std.Io.Dir.cwd().realPathFileAlloc(io, std.Io.Dir.path.dirname(path) orelse ".", allocator);
            defer allocator.free(parent);
            break :resolved try std.Io.Dir.path.joinZ(allocator, &.{ parent, std.Io.Dir.path.basename(path) });
        };
        defer allocator.free(path_z);
        if (!std.mem.eql(u8, path, ":memory:")) {
            const permissions = if (@hasDecl(std.Io.File.Permissions, "fromMode"))
                std.Io.File.Permissions.fromMode(0o600)
            else
                std.Io.File.Permissions.default_file;
            const file = std.Io.Dir.cwd().createFile(io, path_z, .{ .exclusive = true, .permissions = permissions }) catch |err| switch (err) {
                error.PathAlreadyExists => null,
                else => return err,
            };
            if (file) |created| created.close(io);
        }
        // Preserve the failed-open handle for cleanup; the pinned zqlite open
        // helper does not yet close it. All SQL operations use zqlite.
        var raw: ?*c.sqlite3 = null;
        const status = c.sqlite3_open_v2(path_z, &raw, c.SQLITE_OPEN_READWRITE | c.SQLITE_OPEN_CREATE | c.SQLITE_OPEN_NOFOLLOW | c.SQLITE_OPEN_FULLMUTEX | c.SQLITE_OPEN_EXRESCODE, null);
        if (status != c.SQLITE_OK) {
            if (raw) |handle| _ = c.sqlite3_close_v2(handle);
            return if (status == c.SQLITE_NOMEM) error.OutOfMemory else error.DatabaseUnavailable;
        }
        const db: zqlite.Conn = .{ .conn = raw.? };
        errdefer db.close();
        try db.busyTimeout(250);
        try db.execNoArgs("PRAGMA trusted_schema=OFF; PRAGMA foreign_keys=ON;");
        try db.execNoArgs("BEGIN IMMEDIATE;");
        errdefer db.rollback();
        const app = try scalar(db, "PRAGMA application_id;");
        const version = try scalar(db, "PRAGMA user_version;");
        if (app == 0 and version == 0) {
            if (try scalar(db, "SELECT count(*) FROM sqlite_schema WHERE name NOT LIKE 'sqlite_%';") != 0)
                return error.IncompatibleDatabase;
            try db.execNoArgs(schema.create);
        } else if (app == schema.application_id and (version >= 1 and version <= 3)) {
            if (version == 1) try db.execNoArgs(schema.upgrade_v1);
            try db.execNoArgs("PRAGMA user_version=4;");
        } else if (app != schema.application_id or version != schema.version) return error.IncompatibleDatabase;
        try db.commit();
        // Uncompiled source bytes are a connection-local workspace, never a
        // compiler output, persistent cache entry or fabricated snapshot.
        try db.execNoArgs("CREATE TEMP TABLE workspace_source(name TEXT PRIMARY KEY,content TEXT NOT NULL) STRICT;");
        return .{ .db = db, .io = io };
    }

    pub fn deinit(self: *Store) void {
        self.db.close();
        self.* = undefined;
    }

    /// One publication transaction serializes with readers. Canonical bytes
    /// remain unchanged; indexes never participate in analysis or codegen.
    pub fn importCompilation(self: *Store, allocator: std.mem.Allocator, label: []const u8, origin: Origin, request: []const u8, output: []const u8, captured: []const Source) !i64 {
        return self.publish(allocator, label, origin, request, output, captured, null);
    }

    pub fn publish(self: *Store, allocator: std.mem.Allocator, label: []const u8, origin: Origin, request: []const u8, output: []const u8, captured: []const Source, receipt: ?Receipt) !i64 {
        if (!snapshotFits(label.len, request.len, output.len)) return error.CompilerSnapshotTooLarge;
        if (receipt) |value| if (value.manifest.len > max_manifest_bytes or value.context.len != 64 or value.seal.len != 64) return error.InvalidReceipt;
        // Strict parsing rejects duplicate fields; SQLite alone would accept
        // ambiguous documents. Retain only one request-local parse at a time.
        for ([_][]const u8{ request, output }) |document| {
            const parsed = try std.json.parseFromSlice(std.json.Value, allocator, document, .{ .max_value_len = max_document_bytes });
            defer parsed.deinit();
            if (parsed.value != .object) return error.InvalidCompilerDocument;
        }
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        if (self.frozen) return error.FrozenStore;
        try self.db.execNoArgs("BEGIN IMMEDIATE;");
        errdefer self.db.rollback();
        const request_hash = digest(request);
        const output_hash = digest(output);
        try self.db.exec("INSERT INTO compilation(label,origin,request,output,request_sha256,output_sha256) VALUES(?,?,?,?,?,?);", .{ label, @tagName(origin), request, output, &request_hash, &output_hash });
        const id = self.db.lastInsertedRowId();
        try self.db.exec(
            \\INSERT INTO source(compilation,name,content)
            \\SELECT ?,key,json_extract(value,'$.content') FROM json_each(?,'$.sources');
        , .{ id, request });
        // Captured imports are the bytes actually read by the compiler callback.
        // A URL entry may publish under a different source-unit name.
        if (captured.len != 0) {
            const insert = try self.db.prepare("INSERT INTO source(compilation,name,content) VALUES(?,?,?) ON CONFLICT(compilation,name) DO UPDATE SET content=excluded.content WHERE source.content IS NULL;");
            defer insert.deinit();
            const map_url = try self.db.prepare(
                \\UPDATE source SET content=? WHERE compilation=? AND content IS NULL AND name IN (
                \\ SELECT s.key FROM json_each(?,'$.sources') s, json_each(s.value,'$.urls') u WHERE u.value=?);
            );
            defer map_url.deinit();
            var captured_bytes: usize = 0;
            for (captured) |source| {
                captured_bytes = std.math.add(usize, captured_bytes, source.content.len) catch return error.CapturedSourcesTooLarge;
                if (captured_bytes > 64 * 1024 * 1024) return error.CapturedSourcesTooLarge;
                try execPrepared(insert, .{ id, source.name, source.content });
                try execPrepared(map_url, .{ source.content, id, request, source.name });
            }
        }
        try self.db.exec(
            \\INSERT INTO source(compilation,name,compiler_id,ast)
            \\SELECT ?,key,json_extract(value,'$.id'),json_extract(value,'$.ast') FROM json_each(?,'$.sources') WHERE true
            \\ON CONFLICT(compilation,name) DO UPDATE SET compiler_id=excluded.compiler_id,ast=excluded.ast;
        , .{ id, output });
        try self.db.exec(
            \\INSERT INTO contract SELECT ?,s.key,c.key,c.value FROM json_each(?,'$.contracts') s,json_each(s.value) c;
        , .{ id, output });
        try self.db.exec(
            \\INSERT INTO diagnostic SELECT ?,key,json_extract(value,'$.sourceLocation.file'),json_extract(value,'$.severity'),value
            \\FROM json_each(?,'$.errors');
        , .{ id, output });
        // Flatten AST annotations once. Keep scalar navigation fields, never
        // copies of every nested subtree (which would be quadratic in AST size).
        try self.db.exec(
            \\WITH objects AS (
            \\ SELECT s.name,CASE WHEN j.type='object' THEN j.value ELSE '{}' END AS data
            \\ FROM source s,json_tree(s.ast) j WHERE s.compilation=?)
            \\INSERT INTO node SELECT ?,json_extract(data,'$.id'),name,json_extract(data,'$.nodeType'),
            \\ json_extract(data,'$.name'),json_extract(data,'$.src'),
            \\ coalesce(json_extract(data,'$.nameLocation'),json_extract(data,'$.memberLocation')),
            \\ json_extract(data,'$.referencedDeclaration'),json_extract(data,'$.absolutePath')
            \\ FROM objects WHERE json_type(data,'$.id')='integer' AND json_type(data,'$.nodeType')='text';
        , .{ id, id });
        if (self.db.changes() > 2_000_000) return error.AstIndexTooLarge;
        if (receipt) |value| try self.db.exec("INSERT INTO live_receipt VALUES(?,?,?,?);", .{ id, value.context, value.manifest, value.seal });
        try self.db.commit();
        return id;
    }

    /// Copy a candidate while locked, then authenticate/check outside SQL.
    /// Only the latest snapshot can resume; imported/legacy snapshots miss.
    pub fn resumeAlloc(self: *Store, allocator: std.mem.Allocator, context: []const u8) !?Resume {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        const row = (try self.db.row("SELECT c.id,c.request,c.output,r.manifest,r.seal FROM compilation c JOIN live_receipt r ON r.compilation=c.id WHERE c.id=(SELECT max(id) FROM compilation) AND c.origin='compiled' AND r.context=?;", .{context})) orelse return null;
        defer row.deinit();
        if (!snapshotFits(0, row.text(1).len, row.text(2).len) or row.text(3).len > max_manifest_bytes or row.text(4).len != 64) return null;
        const request = try allocator.dupe(u8, row.text(1));
        errdefer allocator.free(request);
        const output = try allocator.dupe(u8, row.text(2));
        errdefer allocator.free(output);
        const manifest = try allocator.dupe(u8, row.text(3));
        errdefer allocator.free(manifest);
        const seal = try allocator.dupe(u8, row.text(4));
        return .{ .id = row.int(0), .request = request, .output = output, .receipt = .{ .context = context, .manifest = manifest, .seal = seal } };
    }

    /// Byte-exact canonical export. The field is selected at compile time.
    pub fn documentAlloc(self: *Store, allocator: std.mem.Allocator, id: i64, comptime field: enum { request, output }) !?[]u8 {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        const row = (try self.db.row("SELECT " ++ @tagName(field) ++ " FROM compilation WHERE id=?;", .{id})) orelse return null;
        defer row.deinit();
        const bytes = row.text(0);
        if (bytes.len > max_document_bytes) return error.CompilerSnapshotTooLarge;
        return try allocator.dupe(u8, bytes);
    }

    pub const File = struct { content: ?[]u8, yul: bool };

    pub fn replaceWorkspace(self: *Store, sources: []const Source) !void {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        if (self.frozen) return error.FrozenStore;
        try self.db.execNoArgs("BEGIN;");
        errdefer self.db.rollback();
        try self.db.execNoArgs("DELETE FROM workspace_source;");
        if (sources.len != 0) {
            const insert = try self.db.prepare("INSERT INTO workspace_source(name,content) VALUES(?,?);");
            defer insert.deinit();
            var bytes: usize = 0;
            for (sources) |source| {
                bytes = std.math.add(usize, bytes, source.content.len) catch return error.CapturedSourcesTooLarge;
                if (bytes > 64 * 1024 * 1024) return error.CapturedSourcesTooLarge;
                try execPrepared(insert, .{ source.name, source.content });
            }
        }
        try self.db.commit();
    }

    /// The caller owns content. A missing source and unavailable source bytes
    /// are separate outcomes (the latter is common for imported output).
    pub fn fileAlloc(self: *Store, allocator: std.mem.Allocator, id: i64, name: []const u8) !?File {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        const row = (try self.db.row("SELECT s.content,json_extract(c.request,'$.language')='Yul' FROM source s JOIN compilation c ON c.id=s.compilation WHERE s.compilation=? AND s.name=? UNION ALL SELECT content,0 FROM workspace_source WHERE ?=0 AND name=?;", .{ id, name, id, name })) orelse return null;
        defer row.deinit();
        const content = row.nullableText(0);
        if (content) |bytes| if (bytes.len > 64 * 1024 * 1024) return error.CapturedSourcesTooLarge;
        return .{ .content = if (content) |bytes| try allocator.dupe(u8, bytes) else null, .yul = row.nullableBoolean(1) orelse false };
    }

    pub fn latest(self: *Store) !?i64 {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        const row = (try self.db.row("SELECT max(id) FROM compilation;", .{})) orelse return null;
        defer row.deinit();
        return row.nullableInt(0);
    }

    pub fn freeze(self: *Store) !void {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        try self.db.execNoArgs("PRAGMA query_only=ON;");
        self.frozen = true;
    }

    /// SQL is application-owned and parameters are bound. No borrowed SQLite
    /// text escapes step/finalize or the lock; errors discard the entire result.
    pub fn queryAlloc(self: *Store, allocator: std.mem.Allocator, sql: [:0]const u8, parameters: anytype, max_rows: usize) ![]u8 {
        try self.mutex.lock(self.io);
        defer self.mutex.unlock(self.io);
        var rows = try self.db.rows(sql, parameters);
        defer rows.deinit();
        var buffer: std.Io.Writer.Allocating = .init(allocator);
        defer buffer.deinit();
        var json: std.json.Stringify = .{ .writer = &buffer.writer };
        json.beginArray() catch return error.OutOfMemory;
        var count: usize = 0;
        while (rows.next()) |row| {
            if (count >= max_rows) return error.ResultTooLarge;
            count += 1;
            json.beginObject() catch return error.OutOfMemory;
            const statement = row.stmt;
            for (0..@intCast(statement.columnCount())) |column| {
                json.objectField(std.mem.span(statement.columnName(column))) catch return error.OutOfMemory;
                switch (statement.columnType(column)) {
                    .int => json.write(statement.int(column)) catch return error.OutOfMemory,
                    .float => json.write(statement.float(column)) catch return error.OutOfMemory,
                    .null => json.write(null) catch return error.OutOfMemory,
                    .text => {
                        const value = statement.text(column);
                        // Conservatively allow for JSON escaping before writing.
                        if (value.len > (max_query_bytes -| buffer.written().len) / 6) return error.ResultTooLarge;
                        json.write(value) catch return error.OutOfMemory;
                    },
                    else => return error.UnexpectedColumnType,
                }
            }
            json.endObject() catch return error.OutOfMemory;
        }
        if (rows.err) |err| return err;
        json.endArray() catch return error.OutOfMemory;
        return buffer.toOwnedSlice();
    }
};

fn execPrepared(statement: zqlite.Stmt, values: anytype) !void {
    try statement.reset();
    try statement.clearBindings();
    try statement.bind(values);
    try statement.stepToCompletion();
}

fn snapshotFits(label: usize, request: usize, output: usize) bool {
    return label <= max_document_bytes and request <= max_document_bytes - label and
        output <= max_document_bytes - label - request;
}

test "snapshot budget includes both documents and label without overflow" {
    try std.testing.expect(snapshotFits(10, 20, max_document_bytes - 30));
    try std.testing.expect(!snapshotFits(10, 20, max_document_bytes - 29));
    try std.testing.expect(!snapshotFits(0, max_document_bytes, max_document_bytes));
    try std.testing.expect(!snapshotFits(std.math.maxInt(usize), 1, 1));
    try std.testing.expect(!snapshotFits(0, std.math.maxInt(usize), 1));
    try std.testing.expect(!snapshotFits(0, 0, std.math.maxInt(usize)));
}

test "snapshots larger than 256 MiB preserve canonical bytes and resume" {
    const allocator = std.testing.allocator;
    var store = try Store.open(allocator, std.testing.io, ":memory:");
    defer store.deinit();
    // Padding exercises the old document boundary without manufacturing a huge
    // semantic fixture or requiring a real project in the unit test suite.
    const output = try allocator.alloc(u8, 256 * 1024 * 1024 + 1);
    defer allocator.free(output);
    @memcpy(output[0..2], "{}");
    @memset(output[2..], ' ');
    const hash = digest("large snapshot");
    const receipt: Receipt = .{ .context = &hash, .manifest = "[]", .seal = &hash };
    const id = try store.publish(allocator, "large", .compiled, "{}", output, &.{}, receipt);
    {
        const exported = (try store.documentAlloc(allocator, id, .output)).?;
        defer allocator.free(exported);
        try std.testing.expectEqualSlices(u8, output, exported);
    }
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const resumed = (try store.resumeAlloc(arena.allocator(), &hash)).?;
    try std.testing.expectEqual(id, resumed.id);
    try std.testing.expectEqualStrings("{}", resumed.request);
    try std.testing.expectEqualSlices(u8, output, resumed.output);
}

fn scalar(db: zqlite.Conn, sql: [:0]const u8) !i64 {
    const row = (try db.row(sql, .{})) orelse return error.InvalidDatabase;
    defer row.deinit();
    return row.int(0);
}

pub fn digest(bytes: []const u8) [64]u8 {
    var hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &hash, .{});
    return std.fmt.bytesToHex(hash, .lower);
}

test "uncompiled SQL workspace stays separate and replacement rolls back" {
    var store = try Store.open(std.testing.allocator, std.testing.io, ":memory:");
    defer store.deinit();
    try store.replaceWorkspace(&.{.{ .name = "C.sol", .content = "contract C {}" }});
    try std.testing.expectEqual(@as(?i64, null), try store.latest());
    try std.testing.expectError(error.ConstraintPrimaryKey, store.replaceWorkspace(&.{ .{ .name = "D.sol", .content = "a" }, .{ .name = "D.sol", .content = "b" } }));
    const file = (try store.fileAlloc(std.testing.allocator, 0, "C.sol")).?;
    defer std.testing.allocator.free(file.content.?);
    try std.testing.expectEqualStrings("contract C {}", file.content.?);
    try std.testing.expect(try store.fileAlloc(std.testing.allocator, 0, "D.sol") == null);
    try store.freeze();
    try std.testing.expectError(error.FrozenStore, store.replaceWorkspace(&.{}));
}

test "browser source loops reuse preparations and preserve source mapping" {
    const PreparationCounts = struct {
        workspace_inserts: usize = 0,
        source_inserts: usize = 0,

        fn authorize(context: ?*anyopaque, action: c_int, table: [*c]const u8, _: [*c]const u8, _: [*c]const u8, _: [*c]const u8) callconv(.c) c_int {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            if (action == c.SQLITE_INSERT and table != null) {
                if (std.mem.eql(u8, std.mem.span(table), "workspace_source")) self.workspace_inserts += 1;
                if (std.mem.eql(u8, std.mem.span(table), "source")) self.source_inserts += 1;
            }
            return c.SQLITE_OK;
        }
    };
    const allocator = std.testing.allocator;
    var store = try Store.open(allocator, std.testing.io, ":memory:");
    defer store.deinit();
    var counts: PreparationCounts = .{};
    try std.testing.expectEqual(c.SQLITE_OK, c.sqlite3_set_authorizer(store.db.conn, PreparationCounts.authorize, &counts));
    defer _ = c.sqlite3_set_authorizer(store.db.conn, null, null);
    const sources = [_]Source{
        .{ .name = "first.sol", .content = "first import" },
        .{ .name = "B.sol", .content = "must not replace inline" },
        .{ .name = "last.sol", .content = "last import" },
    };
    try store.replaceWorkspace(&sources);
    const request =
        \\{"sources":{"A.sol":{"urls":["first.sol"]},"B.sol":{"content":"inline"},"C.sol":{"urls":["last.sol"]}}}
    ;
    const id = try store.importCompilation(allocator, "mapped", .compiled, request, "{}", &sources);
    try std.testing.expectEqual(@as(usize, 1), counts.workspace_inserts);
    // Request sources, one reused captured-source INSERT, and output sources.
    try std.testing.expectEqual(@as(usize, 3), counts.source_inserts);
    for ([_]Source{
        .{ .name = "A.sol", .content = "first import" },
        .{ .name = "B.sol", .content = "inline" },
        .{ .name = "C.sol", .content = "last import" },
    }) |expected| {
        const file = (try store.fileAlloc(allocator, id, expected.name)).?;
        defer allocator.free(file.content.?);
        try std.testing.expectEqualStrings(expected.content, file.content.?);
    }
    for (sources) |expected| {
        const file = (try store.fileAlloc(allocator, 0, expected.name)).?;
        defer allocator.free(file.content.?);
        try std.testing.expectEqualStrings(expected.content, file.content.?);
    }
    try store.db.execNoArgs("CREATE TEMP TRIGGER reject_source BEFORE INSERT ON source WHEN NEW.name='last.sol' BEGIN SELECT RAISE(ABORT,'injected'); END;");
    try std.testing.expectError(error.ConstraintTrigger, store.importCompilation(allocator, "rejected", .compiled, request, "{}", &sources));
    try std.testing.expectEqual(@as(?i64, id), try store.latest());
    try store.db.execNoArgs("DROP TRIGGER reject_source;");
    _ = try store.importCompilation(allocator, "retried", .compiled, request, "{}", &sources);
}

test "live receipt publication rolls back and v1 migration preserves history" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const root = try temporary.dir.realPathFileAlloc(io, ".", allocator);
    defer allocator.free(root);
    const path = try std.Io.Dir.path.join(allocator, &.{ root, "browser.sqlite" });
    defer allocator.free(path);
    {
        var store = try Store.open(allocator, io, path);
        defer store.deinit();
        const hash = digest("test");
        try std.testing.expectError(error.ConstraintCheck, store.publish(allocator, "bad", .compiled, "{}", "{}", &.{}, .{ .context = &hash, .manifest = "{", .seal = &hash }));
        try std.testing.expectEqual(@as(?i64, null), try store.latest());
        _ = try store.importCompilation(allocator, "legacy", .compiled, "{}", "{}", &.{});
        try store.db.execNoArgs("DROP TABLE live_receipt; PRAGMA user_version=1;");
    }
    var reopened = try Store.open(allocator, io, path);
    defer reopened.deinit();
    try std.testing.expectEqual(@as(?i64, 1), try reopened.latest());
    try std.testing.expectEqual(@as(i64, schema.version), try scalar(reopened.db, "PRAGMA user_version;"));
    try std.testing.expect(try reopened.resumeAlloc(allocator, "context") == null);
    const output = (try reopened.documentAlloc(allocator, 1, .output)).?;
    defer allocator.free(output);
    try std.testing.expectEqualStrings("{}", output);
}

test "browser schema upgrades retain old snapshots and opaque historical tables" {
    const allocator = std.testing.allocator;
    const io = std.testing.io;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const root = try temporary.dir.realPathFileAlloc(io, ".", allocator);
    defer allocator.free(root);
    const path = try std.Io.Dir.path.join(allocator, &.{ root, "history.sqlite" });
    defer allocator.free(path);
    for ([_]u8{ 2, 3 }) |version| {
        {
            var store = try Store.open(allocator, io, path);
            defer store.deinit();
            if (version == 2) {
                _ = try store.importCompilation(allocator, "old", .imported, "{}", "{\"future\":true}", &.{});
                try store.db.execNoArgs("CREATE TABLE historical_payload(data TEXT); INSERT INTO historical_payload VALUES('retained');");
            }
            try store.db.execNoArgs(if (version == 2) "PRAGMA user_version=2;" else "PRAGMA user_version=3;");
        }
        var store = try Store.open(allocator, io, path);
        defer store.deinit();
        const output = (try store.documentAlloc(allocator, 1, .output)).?;
        defer allocator.free(output);
        try std.testing.expectEqualStrings("{\"future\":true}", output);
        try std.testing.expectEqual(@as(i64, 1), try scalar(store.db, "SELECT count(*) FROM historical_payload WHERE data='retained';"));
        try std.testing.expectEqual(@as(i64, schema.version), try scalar(store.db, "PRAGMA user_version;"));
    }
}

test "SQL snapshots index actual compiler symbols and references without changing output" {
    const solidity = @import("solidity");
    const request =
        \\{"language":"Solidity","sources":{"C.sol":{"content":"pragma solidity 0.8.36; contract C { function f() public pure { uint x = 1; assert(x == 1); assert(false); } }"}},"settings":{"outputSelection":{"*":{"*":["abi"],"":["ast"]}}}}
    ;
    var session = solidity.CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    var output = try session.compile(std.testing.allocator, .{ .input = request });
    defer output.deinit();
    var store = try Store.open(std.testing.allocator, std.testing.io, ":memory:");
    defer store.deinit();
    const id = try store.importCompilation(std.testing.allocator, "test", .compiled, request, output.bytes, &.{});
    try store.freeze();
    const canonical = (try store.documentAlloc(std.testing.allocator, id, .output)).?;
    defer std.testing.allocator.free(canonical);
    try std.testing.expectEqualStrings(output.bytes, canonical);
    const symbols = try store.queryAlloc(std.testing.allocator, "SELECT name FROM symbol WHERE name=?;", .{"x"}, 10);
    defer std.testing.allocator.free(symbols);
    try std.testing.expectEqualStrings("[{\"name\":\"x\"}]", symbols);
    try std.testing.expect(try scalar(store.db, "SELECT count(*) FROM node r JOIN symbol d ON r.compilation=d.compilation AND r.reference=d.id WHERE d.name='x';") > 0);
    try std.testing.expectError(error.FrozenStore, store.importCompilation(std.testing.allocator, "ignored", .imported, request, output.bytes, &.{}));
    try std.testing.expectError(error.ReadOnly, store.db.execNoArgs("DELETE FROM compilation;"));
}

test "SQL snapshots preserve opaque output and imported source bytes across restart" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const directory = try temporary.dir.realPathFileAlloc(std.testing.io, ".", std.testing.allocator);
    defer std.testing.allocator.free(directory);
    const path = try std.Io.Dir.path.join(std.testing.allocator, &.{ directory, "output.sqlite" });
    defer std.testing.allocator.free(path);
    const request = "{\"sources\":{\"unit.sol\":{\"urls\":[\"import.sol\"]}}}";
    const output =
        \\{ "contracts": {"unit.sol":{"C":{"futureArtifact":{"complete":false}}}},"sources":{"unit.sol":{"id":0}} }
    ;
    {
        var store = try Store.open(std.testing.allocator, std.testing.io, path);
        defer store.deinit();
        _ = try store.importCompilation(std.testing.allocator, "archive", .imported, request, output, &.{.{ .name = "import.sol", .content = "// <script> & unicode: λ\n" }});
    }
    var reopened = try Store.open(std.testing.allocator, std.testing.io, path);
    defer reopened.deinit();
    const id = (try reopened.latest()).?;
    const bytes = (try reopened.documentAlloc(std.testing.allocator, id, .output)).?;
    defer std.testing.allocator.free(bytes);
    try std.testing.expectEqualStrings(output, bytes);
    const source = try reopened.queryAlloc(std.testing.allocator, "SELECT content FROM source WHERE name=?;", .{"unit.sol"}, 1);
    defer std.testing.allocator.free(source);
    try std.testing.expect(std.mem.find(u8, source, "<script>") != null);
    const injection = try reopened.queryAlloc(std.testing.allocator, "SELECT name FROM source WHERE name=?;", .{"' OR 1=1 --"}, 1);
    defer std.testing.allocator.free(injection);
    try std.testing.expectEqualStrings("[]", injection);
}

test "SQL import rolls back malformed indexes and rejects ambiguous JSON" {
    var store = try Store.open(std.testing.allocator, std.testing.io, ":memory:");
    defer store.deinit();
    _ = try store.importCompilation(std.testing.allocator, "valid", .imported, "{}", "{}", &.{});
    try std.testing.expectError(error.ConstraintDatatype, store.importCompilation(std.testing.allocator, "invalid", .imported, "{}", "{\"sources\":{\"C.sol\":{\"id\":\"bad\"}}}", &.{}));
    try std.testing.expectEqual(@as(i64, 1), try scalar(store.db, "SELECT count(*) FROM compilation;"));
    try std.testing.expectError(error.DuplicateField, store.importCompilation(std.testing.allocator, "duplicate", .imported, "{\"sources\":{},\"sources\":{}}", "{}", &.{}));
    try std.testing.expectError(error.ResultTooLarge, store.queryAlloc(std.testing.allocator, "SELECT 1 UNION ALL SELECT 2;", .{}, 1));
}

test "SQL snapshots release partial allocations on import and query failure" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn run(allocator: std.mem.Allocator) !void {
            var store = try Store.open(allocator, std.testing.io, ":memory:");
            defer store.deinit();
            _ = try store.importCompilation(allocator, "oom", .imported, "{\"sources\":{\"C.sol\":{\"content\":\"contract C {}\"}}}", "{}", &.{});
            const result = try store.queryAlloc(allocator, "SELECT name,content FROM source;", .{}, 1);
            defer allocator.free(result);
        }
    }.run, .{});
}

test "SQL inspection store refuses unrelated databases without changing their contents" {
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const directory = try temporary.dir.realPathFileAlloc(std.testing.io, ".", std.testing.allocator);
    defer std.testing.allocator.free(directory);
    const path = try std.Io.Dir.path.join(std.testing.allocator, &.{ directory, "unrelated.sqlite" });
    defer std.testing.allocator.free(path);
    const path_z = try std.testing.allocator.dupeSentinel(u8, path, 0);
    defer std.testing.allocator.free(path_z);
    const unrelated = try zqlite.open(path_z, zqlite.OpenFlags.Create);
    defer unrelated.close();
    try unrelated.execNoArgs("CREATE TABLE user_data(value TEXT); INSERT INTO user_data VALUES('keep');");
    try std.testing.expectError(error.IncompatibleDatabase, Store.open(std.testing.allocator, std.testing.io, path));
    try std.testing.expectEqual(@as(i64, 1), try scalar(unrelated, "SELECT count(*) FROM user_data WHERE value='keep';"));
    try std.testing.expectEqual(@as(i64, 0), try scalar(unrelated, "PRAGMA application_id;"));
}
