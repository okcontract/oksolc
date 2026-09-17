// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Loopback-only, read-only HTTP projection of immutable SQL snapshots.
const std = @import("std");
const httpz = @import("httpz");
const Store = @import("store.zig").Store;
const Highlight = @import("highlight.zig");
const Live = @import("live.zig").Status;

pub fn run(allocator: std.mem.Allocator, io: std.Io, store: *Store, port: u16, live: ?*Live) !void {
    if (port == 0) return error.InvalidPort;
    if (live == null and try store.latest() == null) return error.EmptyDatabase;
    if (live == null) try store.freeze();
    var handler: Handler = .{ .store = store, .port = port, .live = live };
    var server = try httpz.Server(*Handler).init(io, allocator, .{
        .address = .localhost(port),
        .workers = .{ .count = 1, .min_conn = 1, .max_conn = 32, .large_buffer_count = 2, .retain_allocated_bytes = 64 * 1024 },
        .thread_pool = .{ .count = 2, .backlog = 32 },
        .request = .{ .max_body_size = 1024, .max_header_count = 32, .max_query_count = 16, .buffer_size = 16 * 1024 },
        .timeout = .{ .request = 10, .keepalive = 10 },
    }, &handler);
    defer server.deinit();
    var router = try server.router(.{});
    router.get("/", index, .{});
    router.get("/style.css", style, .{});
    router.get("/app.js", script, .{});
    router.get("/api/:route", api, .{});
    var buffer: [256]u8 = undefined;
    try std.Io.File.stderr().writeStreamingAll(io, try std.fmt.bufPrint(&buffer, "oksolc browser: http://127.0.0.1:{d}/\nPress Ctrl+C to stop.\n", .{port}));
    // listen owns and joins the library's bounded workers. The caller joins
    // the single live compiler task before destroying the shared store.
    try server.listen();
}

const Handler = struct {
    store: *Store,
    port: u16,
    live: ?*Live,

    pub fn dispatch(self: *Handler, action: httpz.Action(*Handler), req: *httpz.Request, res: *httpz.Response) !void {
        res.header("X-Content-Type-Options", "nosniff");
        res.header("Referrer-Policy", "no-referrer");
        res.header("Cache-Control", "no-store");
        res.header("Content-Security-Policy", "default-src 'self'; script-src 'self'; style-src 'self'; img-src 'self' data:; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'; form-action 'none'");
        if (!allowedRequest(req.header("host"), req.header("origin"), req.header("sec-fetch-site"), self.port)) {
            res.status = 403;
            return res.json(.{ .@"error" = "Local requests only" }, .{});
        }
        action(self, req, res) catch |err| switch (err) {
            error.InvalidQuery => {
                res.status = 400;
                try res.json(.{ .@"error" = "Invalid query parameter" }, .{});
            },
            else => return err,
        };
    }

    pub fn notFound(_: *Handler, _: *httpz.Request, res: *httpz.Response) !void {
        res.status = 404;
        try res.json(.{ .@"error" = "Not found" }, .{});
    }

    pub fn uncaughtError(_: *Handler, _: *httpz.Request, res: *httpz.Response, err: anyerror) void {
        res.status = 500;
        res.json(.{ .@"error" = @errorName(err) }, .{}) catch {
            res.body = "{\"error\":\"Request failed\"}";
        };
    }
};

fn allowedRequest(host: ?[]const u8, origin: ?[]const u8, site: ?[]const u8, port: u16) bool {
    var ip_buffer: [32]u8 = undefined;
    var name_buffer: [32]u8 = undefined;
    const ip = std.fmt.bufPrint(&ip_buffer, "127.0.0.1:{d}", .{port}) catch return false;
    const name = std.fmt.bufPrint(&name_buffer, "localhost:{d}", .{port}) catch return false;
    const value = host orelse return false;
    if (!std.mem.eql(u8, value, ip) and !std.mem.eql(u8, value, name)) return false;
    if (site) |fetch_site| if (std.mem.eql(u8, fetch_site, "cross-site")) return false;
    if (origin) |from| {
        if (!std.mem.startsWith(u8, from, "http://")) return false;
        if (!std.mem.eql(u8, from[7..], value)) return false;
    }
    return true;
}

fn index(_: *Handler, _: *httpz.Request, res: *httpz.Response) !void {
    res.header("Content-Type", "text/html; charset=utf-8");
    res.body = @embedFile("index.html");
}
fn style(_: *Handler, _: *httpz.Request, res: *httpz.Response) !void {
    res.header("Content-Type", "text/css; charset=utf-8");
    res.body = @embedFile("style.css");
}
fn script(_: *Handler, _: *httpz.Request, res: *httpz.Response) !void {
    res.header("Content-Type", "text/javascript; charset=utf-8");
    res.body = @embedFile("browser_app");
}
const Route = enum { summary, compilations, project, contracts, contract, source, symbols, links, references, diagnostics, search, output, request };
// This is a presentation filter for conventional dependency paths, not source
// ownership metadata. Unknown paths and diagnostics without a location stay
// visible. Use the same classification before counting and before pagination.
const diagnostic_rows =
    \\WITH diagnostics AS (
    \\ SELECT *, source IS NOT NULL AND (
    \\  ltrim(replace(source,char(92),'/'),'./') GLOB 'lib/*' OR
    \\  ltrim(replace(source,char(92),'/'),'./') GLOB 'node_modules/*' OR
    \\  ltrim(replace(source,char(92),'/'),'./') GLOB 'vendor/*' OR
    \\  ltrim(replace(source,char(92),'/'),'./') GLOB '@*/*'
    \\ ) AS library FROM diagnostic WHERE compilation=?
    \\)
;
const routes = std.StaticStringMap(Route).initComptime(.{
    .{ "summary", .summary },
    .{ "compilations", .compilations },
    .{ "project", .project },
    .{ "contracts", .contracts },
    .{ "contract", .contract },
    .{ "source", .source },
    .{ "symbols", .symbols },
    .{ "links", .links },
    .{ "references", .references },
    .{ "diagnostics", .diagnostics },
    .{ "search", .search },
    .{ "output", .output },
    .{ "request", .request },
});

fn number(value: ?[]const u8, default: i64) !i64 {
    const text = value orelse return default;
    const result = std.fmt.parseInt(i64, text, 10) catch return error.InvalidQuery;
    if (result < 0 or result > std.math.maxInt(i32)) return error.InvalidQuery;
    return result;
}

fn api(self: *Handler, req: *httpz.Request, res: *httpz.Response) !void {
    if (std.mem.eql(u8, req.param("route").?, "status")) {
        const snapshot: Live.Snapshot = if (self.live) |live| live.get() else .{};
        const state = snapshot.state;
        return res.json(.{
            .live = self.live != null,
            .phase = state.phase,
            .failure = state.failure,
            .source_path = if (self.live) |live| live.source_path else null,
            .latest = if (self.live != null) snapshot.latest else try self.store.latest(),
            .current = snapshot.current,
            .workspace_revision = snapshot.workspace_revision,
            .reused = snapshot.reused,
            .progress = .{
                .stage = if (state.stage) |stage| @tagName(stage) else @tagName(state.phase),
                .completed_items = state.completed_items,
                .total_items = state.total_items,
                .item_name = state.item[0..state.item_len],
            },
        }, .{});
    }
    const route = routes.get(req.param("route").?) orelse return Handler.notFound(self, req, res);
    const query = try req.query();
    const id = try number(query.get("compilation"), if (query.get("compilation") == null) try self.store.latest() orelse 0 else 0);
    const offset = try number(query.get("offset"), 0);
    const source = query.get("source") orelse "";
    const name = query.get("name") orelse "";
    const term = query.get("q") orelse "";
    const status = query.get("status") orelse "";
    const hide_libraries = try number(query.get("hide_libraries"), 0);
    if (hide_libraries > 1) return error.InvalidQuery;
    if (term.len > 256 or source.len > 16 * 1024 or name.len > 4096) return error.InvalidQuery;
    res.header("Content-Type", "application/json; charset=utf-8");
    const store = self.store;
    res.body = switch (route) {
        .summary => try store.queryAlloc(res.arena, diagnostic_rows ++
            \\SELECT 'diagnostic' AS kind,severity AS status,sum(?=0 OR NOT library) AS total,sum(?=1 AND library) AS hidden
            \\FROM diagnostics GROUP BY severity;
        , .{ id, hide_libraries, hide_libraries }, 32),
        .compilations => try store.queryAlloc(res.arena, "SELECT id,label,origin,created_at,request_sha256,output_sha256 FROM compilation ORDER BY id DESC LIMIT 201 OFFSET ?;", .{offset}, 201),
        .project => if (id == 0) try store.queryAlloc(res.arena, "SELECT name,NULL AS compiler_id,1 AS available,0 AS has_ast,0 AS diagnostics FROM workspace_source ORDER BY name;", .{}, 8192) else try store.queryAlloc(res.arena,
            \\SELECT s.name,s.compiler_id,s.content IS NOT NULL AS available,s.ast IS NOT NULL AS has_ast,
            \\(SELECT count(*) FROM diagnostic d WHERE d.compilation=s.compilation AND d.source=s.name) AS diagnostics
            \\FROM source s WHERE s.compilation=? ORDER BY s.name;
        , .{id}, 8192),
        .contracts => try store.queryAlloc(res.arena, "SELECT source,name FROM contract WHERE compilation=? ORDER BY source,name;", .{id}, 8192),
        .contract => try store.queryAlloc(res.arena, "SELECT data FROM contract WHERE compilation=? AND source=? AND name=?;", .{ id, source, name }, 1),
        .symbols => try store.queryAlloc(res.arena, "SELECT id,source,kind,name,src,name_src FROM symbol WHERE compilation=? AND (?='' OR source=?) AND instr(lower(name),lower(?))>0 ORDER BY source,CAST(src AS INTEGER),id LIMIT 201 OFFSET ?;", .{ id, source, source, term, offset }, 201),
        .links => try store.queryAlloc(res.arena,
            \\SELECT r.src,r.name_src,r.reference,r.import_path,n.source AS target_source,coalesce(n.name_src,n.src) AS target_src,n.name AS target_name
            \\FROM node r LEFT JOIN node n ON r.compilation=n.compilation AND r.reference=n.id
            \\WHERE r.compilation=? AND r.source=? AND (r.reference>=0 OR r.kind='ImportDirective') ORDER BY CAST(r.src AS INTEGER),r.id;
        , .{ id, source }, 100_000),
        .references => try store.queryAlloc(res.arena, "SELECT id,source,kind,src,name_src FROM node WHERE compilation=? AND reference=? ORDER BY source,CAST(src AS INTEGER),id LIMIT 201 OFFSET ?;", .{ id, try number(query.get("symbol"), -1), offset }, 201),
        .diagnostics => try store.queryAlloc(res.arena, diagnostic_rows ++ "SELECT ordinal,source,severity,data FROM diagnostics WHERE (?=0 OR NOT library) AND (?='' OR source=?) AND (?='' OR severity=?) ORDER BY ordinal LIMIT 201 OFFSET ?;", .{ id, hide_libraries, source, source, status, status, offset }, 201),
        .search => try store.queryAlloc(res.arena,
            \\SELECT name,CASE WHEN instr(lower(content),lower(?))>0 THEN length(CAST(substr(content,1,instr(lower(content),lower(?))-1) AS BLOB)) ELSE 0 END AS start,
            \\substr(content,max(1,instr(lower(content),lower(?))-40),160) AS snippet
            \\FROM (SELECT name,content FROM source WHERE compilation=? UNION ALL SELECT name,content FROM workspace_source WHERE ?=0)
            \\WHERE ?<>'' AND (instr(lower(name),lower(?))>0 OR instr(lower(content),lower(?))>0)
            \\ORDER BY name LIMIT 201 OFFSET ?;
        , .{ term, term, term, id, id, term, term, term, offset }, 201),
        .source => {
            const file = try store.fileAlloc(res.arena, id, source) orelse return Handler.notFound(self, req, res);
            var warning: ?[]const u8 = null;
            const spans = if (file.content) |content|
                Highlight.scanAlloc(res.arena, source, content, file.yul, 200_000) catch |err| switch (err) {
                    error.OutOfMemory => return err,
                    else => fallback: {
                        warning = @errorName(err);
                        break :fallback &.{};
                    },
                }
            else
                &.{};
            return res.json(.{ .content = file.content, .tokens = spans, .highlight_warning = warning }, .{});
        },
        .output => try store.documentAlloc(res.arena, id, .output) orelse return Handler.notFound(self, req, res),
        .request => try store.documentAlloc(res.arena, id, .request) orelse return Handler.notFound(self, req, res),
    };
}

test "browser origin guard rejects remote hosts origins and cross-site requests" {
    try std.testing.expect(allowedRequest("127.0.0.1:8080", null, null, 8080));
    try std.testing.expect(allowedRequest("localhost:8080", "http://localhost:8080", "same-origin", 8080));
    try std.testing.expect(!allowedRequest("attacker.example:8080", null, null, 8080));
    try std.testing.expect(!allowedRequest("localhost:8080", "http://attacker.example", null, 8080));
    try std.testing.expect(!allowedRequest("localhost:8080", null, "cross-site", 8080));
    try std.testing.expect(!allowedRequest(null, null, null, 8080));
}

test {
    _ = Highlight;
    _ = @import("capture.zig");
}
