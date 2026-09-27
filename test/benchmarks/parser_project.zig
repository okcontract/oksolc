// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Complete source-corpus parsing; request decoding and AST validation are untimed.
const std = @import("std");
const modules = @import("frontend");
const Parser = modules.libsolidity.@"parsing/parser";
const AST = modules.libsolidity.@"ast/ast";
const Exporter = modules.libsolidity.@"ast/ast_json_exporter";
const Json = modules.libsolutil.json;
const Diagnostics = modules.liblangutil.diagnostics;
const EVMVersion = modules.liblangutil.evm_version.EVMVersion;

const Source = struct { name: []const u8, content: []const u8 };
const Project = struct {
    trees: []Parser.ParseResult,
    reporter: Diagnostics.ErrorReporter,

    fn deinit(self: *Project, allocator: std.mem.Allocator) void {
        self.reporter.deinit();
        for (self.trees) |*tree| tree.deinit();
        allocator.free(self.trees);
    }
};

pub fn main(init: std.process.Init) !void {
    return run(std.heap.c_allocator, init);
}

fn run(allocator: std.mem.Allocator, init: std.process.Init) !void {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len != 3) return error.ExpectedWorkloadAndIterations;
    const iterations = try std.fmt.parseInt(usize, args[2], 10);
    if (iterations == 0) return error.ExpectedPositiveIterations;
    const document = try std.json.parseFromSlice(std.json.Value, allocator, @embedFile("request.json"), .{});
    defer document.deinit();
    const input = document.value.object.get("sources").?.object;
    const sources = try allocator.alloc(Source, input.count());
    defer allocator.free(sources);
    var iterator = input.iterator();
    for (sources) |*source| {
        const item = iterator.next().?;
        source.* = .{ .name = item.key_ptr.*, .content = item.value_ptr.object.get("content").?.string };
    }
    std.mem.sort(Source, sources, {}, struct {
        fn lessThan(_: void, left: Source, right: Source) bool {
            return std.mem.order(u8, left.name, right.name) == .lt;
        }
    }.lessThan);
    const settings = document.value.object.get("settings").?.object;
    const version = EVMVersion.fromString(settings.get("evmVersion").?.string) orelse return error.InvalidEVMVersion;

    if (std.mem.eql(u8, args[1], "validate-project")) return validate(allocator, sources, version);
    const cold = std.mem.eql(u8, args[1], "parse-project-cold");
    if (!cold and !std.mem.eql(u8, args[1], "parse-project")) return error.UnknownWorkload;
    if (!cold) {
        var warmup = try parseProject(allocator, sources, version);
        warmup.deinit(allocator);
    }
    const count = if (cold) 1 else iterations;
    var checksum: u64 = 0;
    const start = std.Io.Clock.awake.now(init.io);
    for (0..count) |_| {
        var project = try parseProject(allocator, sources, version);
        for (project.trees) |tree| checksum +%= tree.tree.nodes.items.len;
        std.mem.doNotOptimizeAway(project.trees);
        project.deinit(allocator);
    }
    const elapsed = start.durationTo(std.Io.Clock.awake.now(init.io)).nanoseconds;
    std.debug.print("{{\"ns_per_op\":{d:.3},\"checksum\":{d}}}\n", .{
        @as(f64, @floatFromInt(elapsed)) / @as(f64, @floatFromInt(count)), checksum,
    });
}

fn parseProject(allocator: std.mem.Allocator, sources: []const Source, version: EVMVersion) !Project {
    const trees = try allocator.alloc(Parser.ParseResult, sources.len);
    var initialized: usize = 0;
    errdefer {
        for (trees[0..initialized]) |*tree| tree.deinit();
        allocator.free(trees);
    }
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    errdefer reporter.deinit();
    var previous_id: i64 = 0;
    for (sources, trees, 0..) |source, *tree, index| {
        tree.* = try Parser.parseSourceWithIdentity(allocator, source.content, source.name, &reporter, version, AST.SourceId.init(@intCast(index)), previous_id);
        initialized += 1;
        if (reporter.hasErrors() or tree.tree.root == null) {
            for (reporter.diagnostics()) |diagnostic|
                std.debug.print("{s}: {s}\n", .{ source.name, diagnostic.description });
            return error.ParseFailed;
        }
        previous_id = tree.tree.next_node_id;
    }
    return .{ .trees = trees, .reporter = reporter };
}

fn validate(allocator: std.mem.Allocator, sources: []const Source, version: EVMVersion) !void {
    var project = try parseProject(allocator, sources, version);
    defer project.deinit(allocator);
    const indices = try allocator.alloc(Exporter.SourceIndex, sources.len);
    defer allocator.free(indices);
    for (sources, indices, 0..) |source, *entry, index| entry.* = .{ .name = source.name, .index = index };
    var hash = std.crypto.hash.sha2.Sha256.init(.{});
    var nodes: usize = 0;
    for (project.trees, sources) |tree, source| {
        var arena = std.heap.ArenaAllocator.init(allocator);
        defer arena.deinit();
        var exporter = Exporter.ASTJsonExporter.init(arena.allocator(), indices, source.name, .legacyNodeIds());
        const ast_json = try exporter.toJson(tree.tree.root.?);
        const bytes = try Json.jsonCompactPrintAlloc(arena.allocator(), &ast_json);
        hash.update(source.name);
        hash.update("\x00");
        hash.update(bytes);
        hash.update("\n");
        nodes += tree.tree.nodes.items.len;
    }
    const digest = std.fmt.bytesToHex(hash.finalResult(), .lower);
    var diagnostic_hash = std.crypto.hash.sha2.Sha256.init(.{});
    for (project.reporter.diagnostics()) |diagnostic| {
        const bytes = try std.json.Stringify.valueAlloc(allocator, .{
            .id = diagnostic.error_id.value,
            .kind = @tagName(diagnostic.error_type),
            .description = diagnostic.description,
            .location = diagnostic.location,
            .secondary = diagnostic.secondary.infos.items,
        }, .{});
        defer allocator.free(bytes);
        diagnostic_hash.update(bytes);
        diagnostic_hash.update("\n");
    }
    const diagnostic_digest = std.fmt.bytesToHex(diagnostic_hash.finalResult(), .lower);
    std.debug.print("{{\"sources\":{d},\"nodes\":{d},\"errors\":0,\"warnings\":{d},\"infos\":{d},\"ast_sha256\":\"{s}\",\"diagnostics_sha256\":\"{s}\"}}\n", .{
        sources.len, nodes, project.reporter.warningCount(), project.reporter.infoCount(), digest, diagnostic_digest,
    });
}
