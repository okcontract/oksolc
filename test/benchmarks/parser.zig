// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Standalone frontend probes, built by parser_compare.py against source snapshots.
const std = @import("std");
const modules = @import("frontend");
const Token = modules.liblangutil.token;
const Parser = modules.libsolidity.@"parsing/parser";
const Diagnostics = modules.liblangutil.diagnostics;
const EVMVersion = modules.liblangutil.evm_version.EVMVersion;
const EVMDialect = modules.libyul.@"backends/evm/evm_dialect".EVMDialect;
const YulParser = modules.libyul.asm_parser;

const keyword_words = [_][]const u8{
    "function", "contract", "returns", "memory", "calldata", "public", "external", "uint",
    "address",  "if",       "else",    "return", "mapping",  "event",  "emit",     "revert",
};
const identifier_words = [_][]const u8{
    "balance",   "owner",  "msg",       "sender",           "transfer", "totalSupply", "allowance", "recipient",
    "_balances", "amount", "balanceOf", "safeTransferFrom", "account1", "v2",          "value123",  "_0",
};
const sized_words = [_][]const u8{
    "uint256",  "int128",  "bytes32", "uint8",         "bytes4", "fixed128x18", "ufixed256x80", "int256",
    "uint0256", "uint257", "bytes33", "ufixed128x081", "int8x2", "bytes0",      "fixed8x0",     "uint256_value",
};
const reserved_words = [_][]const u8{
    "add",   "basefee", "prevrandao",     "difficulty",  "tload",  "clz",   "datasize", "verbatim_bad",
    "total", "value",   "customFunction", "memoryguard", "push32", "mcopy", "ADD",      "loadimmutable",
};

pub fn main(init: std.process.Init) !void {
    const allocator = std.heap.c_allocator;
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len != 2) return error.ExpectedWorkload;
    const workload = args[1];
    if (std.mem.eql(u8, workload, "tokens-keywords")) return tokens(allocator, init.io, &keyword_words);
    if (std.mem.eql(u8, workload, "tokens-identifiers")) return tokens(allocator, init.io, &identifier_words);
    if (std.mem.eql(u8, workload, "tokens-sized")) return tokens(allocator, init.io, &sized_words);
    if (std.mem.eql(u8, workload, "tokens-corpus")) {
        const source = @embedFile("chains.sol") ++ @embedFile("verifier.sol") ++ @embedFile("OptimizorClub.sol");
        var words: std.ArrayList([]const u8) = .empty;
        defer words.deinit(allocator);
        var index: usize = 0;
        while (index < source.len) {
            if (!std.ascii.isAlphabetic(source[index]) and source[index] != '_') {
                index += 1;
                continue;
            }
            const start = index;
            while (index < source.len and (std.ascii.isAlphanumeric(source[index]) or source[index] == '_')) : (index += 1) {}
            try words.append(allocator, source[start..index]);
        }
        return tokens(allocator, init.io, words.items);
    }
    if (std.mem.eql(u8, workload, "parse-chains")) return parse(allocator, init.io, @embedFile("chains.sol"));
    if (std.mem.eql(u8, workload, "parse-verifier")) return parse(allocator, init.io, @embedFile("verifier.sol"));
    if (std.mem.eql(u8, workload, "parse-club")) return parse(allocator, init.io, @embedFile("OptimizorClub.sol"));
    if (std.mem.eql(u8, workload, "dialect-init")) return dialectInit(allocator, init.io);
    if (std.mem.eql(u8, workload, "reserved-lookup")) return reservedLookup(allocator, init.io);
    if (std.mem.eql(u8, workload, "parse-yul")) return parseYul(allocator, init.io);
    return error.UnknownWorkload;
}

fn report(io: std.Io, start: std.Io.Timestamp, operations: usize, checksum: u64) void {
    const ns = start.durationTo(std.Io.Clock.awake.now(io)).nanoseconds;
    std.debug.print("{{\"ns_per_op\":{d:.3},\"checksum\":{d}}}\n", .{
        @as(f64, @floatFromInt(ns)) / @as(f64, @floatFromInt(operations)), checksum,
    });
}

fn tokens(allocator: std.mem.Allocator, io: std.Io, input: []const []const u8) !void {
    const words = try allocator.dupe([]const u8, input);
    defer allocator.free(words);
    var random = std.Random.DefaultPrng.init(173);
    random.random().shuffle([]const u8, words);
    std.mem.doNotOptimizeAway(words);
    const iterations = @max(1, 4_000_000 / words.len);
    var checksum: u64 = 0;
    const start = std.Io.Clock.awake.now(io);
    for (0..iterations) |_| for (words) |word| {
        const result = Token.fromIdentifierOrKeyword(word);
        checksum +%= @intFromEnum(result.token) + result.first_number + result.second_number;
    };
    report(io, start, iterations * words.len, checksum);
}

fn parse(allocator: std.mem.Allocator, io: std.Io, source: []const u8) !void {
    const iterations = 150;
    var checksum: u64 = 0;
    const start = std.Io.Clock.awake.now(io);
    for (0..iterations) |_| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var result = try Parser.parseSource(allocator, source, "benchmark.sol", &reporter, EVMVersion.current());
        defer result.deinit();
        if (reporter.hasErrors()) return error.ParseFailed;
        const root = result.tree.root orelse return error.ParseFailed;
        checksum +%= root.payload.source_unit.nodes.len;
        std.mem.doNotOptimizeAway(root);
    }
    report(io, start, iterations, checksum);
}

fn dialectInit(allocator: std.mem.Allocator, io: std.Io) !void {
    var counter = std.testing.FailingAllocator.init(allocator, .{});
    var counted = try EVMDialect.init(counter.allocator(), EVMVersion.current(), true);
    counted.deinit();
    std.debug.print("{{\"allocations\":{d},\"allocated_bytes\":{d}}}\n", .{ counter.allocations, counter.allocated_bytes });
    const iterations = 1000;
    var checksum: u64 = 0;
    const start = std.Io.Clock.awake.now(io);
    for (0..iterations) |_| {
        var dialect = try EVMDialect.init(allocator, EVMVersion.current(), true);
        defer dialect.deinit();
        checksum +%= dialect.findBuiltin("add").?.id;
        std.mem.doNotOptimizeAway(&dialect);
    }
    report(io, start, iterations, checksum);
}

fn reservedLookup(allocator: std.mem.Allocator, io: std.Io) !void {
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), true);
    defer dialect.deinit();
    const words = try allocator.dupe([]const u8, &reserved_words);
    defer allocator.free(words);
    std.mem.doNotOptimizeAway(words);
    const iterations = 250_000;
    var checksum: u64 = 0;
    const start = std.Io.Clock.awake.now(io);
    for (0..iterations) |_| for (words) |word| {
        checksum +%= @intFromBool(dialect.reservedIdentifier(word));
    };
    report(io, start, iterations * words.len, checksum);
}

fn parseYul(allocator: std.mem.Allocator, io: std.Io) !void {
    var dialect = try EVMDialect.init(allocator, EVMVersion.current(), true);
    defer dialect.deinit();
    const source = "{ let total := 0 let value := 7\n" ++ "total := add(total, mul(value, 3))\n" ** 200 ++ "}";
    const iterations = 400;
    var checksum: u64 = 0;
    const start = std.Io.Clock.awake.now(io);
    for (0..iterations) |_| {
        var reporter = Diagnostics.ErrorReporter.init(allocator);
        defer reporter.deinit();
        var result = (try YulParser.Parser.parseSource(allocator, source, "benchmark.yul", &reporter, dialect.dialect(), .{})) orelse return error.ParseFailed;
        defer result.deinit();
        if (reporter.hasErrors()) return error.ParseFailed;
        checksum +%= result.root_block.statements.items.len;
        std.mem.doNotOptimizeAway(&result);
    }
    report(io, start, iterations, checksum);
}
