// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Frozen solc IR predates direct Yul-tree generation. Compare only contract
//! `ir` strings as Yul token streams; every byte outside those strings remains
//! exact, including optimized IR, bytecode, diagnostics, and JSON field order.
const std = @import("std");
const solidity = @import("solidity");
const Scanner = solidity.liblangutil.scanner.Scanner;
const CharStream = solidity.liblangutil.char_stream.CharStream;

const Span = struct { start: usize, end: usize, text: []const u8 };

pub fn compare(allocator: std.mem.Allocator, expected: []const u8, actual: []const u8) !void {
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    const scratch = arena.allocator();
    const expected_spans = try irSpans(scratch, expected);
    const actual_spans = try irSpans(scratch, actual);
    if (expected_spans.len != actual_spans.len) return error.OutputMismatch;
    var expected_end: usize = 0;
    var actual_end: usize = 0;
    for (expected_spans, actual_spans) |left, right| {
        try solidity.standard_json.compareExact(expected[expected_end..left.start], actual[actual_end..right.start]);
        try compareYul(scratch, left.text, right.text);
        expected_end = left.end;
        actual_end = right.end;
    }
    try solidity.standard_json.compareExact(expected[expected_end..], actual[actual_end..]);
}

fn compareYul(allocator: std.mem.Allocator, expected: []const u8, actual: []const u8) !void {
    var left_source = CharStream.initBorrowed(expected, "expected");
    var right_source = CharStream.initBorrowed(actual, "actual");
    var left = try Scanner.init(allocator, &left_source, .Yul);
    defer left.deinit();
    var right = try Scanner.init(allocator, &right_source, .Yul);
    defer right.deinit();
    while (true) {
        if (left.currentError() != .NoError or right.currentError() != .NoError)
            return error.InvalidYul;
        if (left.currentToken() != right.currentToken()) return error.OutputMismatch;
        try solidity.standard_json.compareExact(left.currentLiteral(), right.currentLiteral());
        if (left.currentToken() == .EOS) return;
        _ = try left.next();
        _ = try right.next();
    }
}

fn irSpans(allocator: std.mem.Allocator, bytes: []const u8) ![]const Span {
    var scanner = std.json.Scanner.initCompleteInput(allocator, bytes);
    defer scanner.deinit();
    var spans: std.ArrayList(Span) = .empty;
    errdefer spans.deinit(allocator);
    try collectValue(allocator, &scanner, 0, false, &spans);
    if (try scanner.next() != .end_of_document) return error.InvalidJson;
    return spans.toOwnedSlice(allocator);
}

fn string(token: std.json.Token) ![]const u8 {
    return switch (token) {
        .string, .allocated_string => |text| text,
        else => error.InvalidJson,
    };
}

fn collectValue(
    allocator: std.mem.Allocator,
    scanner: *std.json.Scanner,
    depth: usize,
    in_contracts: bool,
    spans: *std.ArrayList(Span),
) anyerror!void {
    switch (try scanner.nextAlloc(allocator, .alloc_if_needed)) {
        .object_begin => {
            while (try scanner.peekNextTokenType() != .object_end) {
                const key = try string(try scanner.nextAlloc(allocator, .alloc_if_needed));
                if (in_contracts and depth == 3 and std.mem.eql(u8, key, "ir")) {
                    if (try scanner.peekNextTokenType() != .string) return error.InvalidJson;
                    const start = scanner.cursor;
                    const text = try string(try scanner.nextAlloc(allocator, .alloc_if_needed));
                    try spans.append(allocator, .{ .start = start, .end = scanner.cursor, .text = text });
                } else {
                    try collectValue(allocator, scanner, depth + 1, in_contracts or
                        (depth == 0 and std.mem.eql(u8, key, "contracts")), spans);
                }
            }
            _ = try scanner.next();
        },
        .array_begin => {
            while (try scanner.peekNextTokenType() != .array_end)
                try collectValue(allocator, scanner, depth + 1, false, spans);
            _ = try scanner.next();
        },
        .object_end, .array_end, .end_of_document => return error.InvalidJson,
        else => {},
    }
}

test "IR comparison ignores only unoptimized Yul whitespace and comments" {
    const prefix = "{\"contracts\":{\"C.sol\":{\"C\":{\"ir\":";
    const suffix = ",\"irOptimized\":\"exact\",\"evm\":{\"bytecode\":{\"object\":\"00\"}}}}}}\n";
    const expected = prefix ++ "\"{ let x := 1 /* original */ pop(x) }\"" ++ suffix;
    try compare(std.testing.allocator, expected, prefix ++ "\"{let x:=1 pop(x)}\"" ++ suffix);
    try std.testing.expectError(error.OutputMismatch, compare(std.testing.allocator, expected, prefix ++ "\"{let x:=2 pop(x)}\"" ++ suffix));
    try std.testing.expectError(error.OutputMismatch, compare(std.testing.allocator, expected, prefix ++ "\"{let x:=1 pop(y)}\"" ++ suffix));
    try std.testing.expectError(error.InvalidYul, compare(std.testing.allocator, expected, prefix ++ "\"{let x:=1 /*\"" ++ suffix));
    const changed_bytecode = try std.mem.replaceOwned(u8, std.testing.allocator, expected, "00", "01");
    defer std.testing.allocator.free(changed_bytecode);
    try std.testing.expectError(error.OutputMismatch, compare(std.testing.allocator, expected, changed_bytecode));
    const changed_optimized = try std.mem.replaceOwned(u8, std.testing.allocator, expected, "exact", " exact");
    defer std.testing.allocator.free(changed_optimized);
    try std.testing.expectError(error.OutputMismatch, compare(std.testing.allocator, expected, changed_optimized));
    try std.testing.expectError(error.OutputMismatch, compare(std.testing.allocator, "{\"ir\":\"x\"}", "{\"ir\":\" x\"}"));
    try std.testing.expectError(error.OutputMismatch, compare(std.testing.allocator, expected, expected[0 .. expected.len - 1]));
    try std.testing.expectError(error.OutputMismatch, compareYul(std.testing.allocator, "{pop(\"a b\")}", "{pop(\"ab\")}"));
}
