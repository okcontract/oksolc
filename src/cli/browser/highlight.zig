// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Byte spans from the compiler scanner, not a second Solidity lexer. Skipped
//! gaps contain whitespace/comments and retain their original bytes.
const std = @import("std");
const lang = @import("solidity").liblangutil;
const Token = lang.token.Token;
pub const Kind = enum { keyword, type, number, string, comment, identifier, punctuation, invalid };
pub const Span = struct { start: u32, end: u32, kind: Kind };

pub fn scanAlloc(allocator: std.mem.Allocator, name: []const u8, content: []const u8, yul: bool, max_tokens: usize) ![]Span {
    var stream = lang.char_stream.CharStream.initBorrowed(content, name);
    var scanner = try lang.scanner.Scanner.init(allocator, &stream, if (yul) .Yul else .Solidity);
    defer scanner.deinit();
    var spans: std.ArrayList(Span) = .empty;
    errdefer spans.deinit(allocator);
    var end: u32 = 0;
    while (scanner.currentToken() != .EOS) {
        const location = scanner.currentLocation();
        const start = std.math.cast(u32, location.start) orelse return error.InvalidTokenRange;
        const next = std.math.cast(u32, location.end) orelse return error.InvalidTokenRange;
        if (start < end or next <= start or next > content.len) return error.InvalidTokenRange;
        if (spans.items.len + 2 > max_tokens) return error.HighlightingLimit;
        if (start > end) try spans.append(allocator, .{ .start = end, .end = start, .kind = .comment });
        try spans.append(allocator, .{ .start = start, .end = next, .kind = classify(scanner.currentToken()) });
        end = next;
        _ = try scanner.next();
    }
    if (end < content.len) {
        if (spans.items.len == max_tokens) return error.HighlightingLimit;
        try spans.append(allocator, .{ .start = end, .end = @intCast(content.len), .kind = .comment });
    }
    return spans.toOwnedSlice(allocator);
}

fn classify(token: Token) Kind {
    if (lang.token.isElementaryTypeName(token)) return .type;
    return switch (token) {
        .Number => .number,
        .StringLiteral, .UnicodeStringLiteral, .HexStringLiteral => .string,
        .CommentLiteral => .comment,
        .Identifier => .identifier,
        .Illegal => .invalid,
        else => if (@intFromEnum(token) >= @intFromEnum(Token.Delete)) .keyword else .punctuation,
    };
}

test "compiler highlighting covers original bytes including unicode comments strings and invalid input" {
    const source = "// λ <script>\r\ncontract C { string s = unicode\"λ\"; uint x = 0xff; @ } /* end */";
    const spans = try scanAlloc(std.testing.allocator, "C.sol", source, false, 1000);
    defer std.testing.allocator.free(spans);
    var position: usize = 0;
    var strings: usize = 0;
    var invalid: usize = 0;
    for (spans) |span| {
        try std.testing.expectEqual(position, span.start);
        position = span.end;
        strings += @intFromBool(span.kind == .string);
        invalid += @intFromBool(span.kind == .invalid);
    }
    try std.testing.expectEqual(source.len, position);
    try std.testing.expect(strings > 0 and invalid > 0);
    try std.testing.expectError(error.HighlightingLimit, scanAlloc(std.testing.allocator, "C.sol", source, false, 1));
}

test "compiler highlighting supports Yul and allocation failure cleanup" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, struct {
        fn run(allocator: std.mem.Allocator) !void {
            const spans = try scanAlloc(allocator, "A.yul", "{ let x := add(1, 2) }", true, 1000);
            defer allocator.free(spans);
            try std.testing.expect(spans.len > 0);
        }
    }.run, .{});
}
