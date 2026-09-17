// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Coherent structural translation of `Scanner.h/.cpp`.
//!
//! The scanner borrows its `CharStream`; the stream and its source/name bytes
//! must outlive the scanner and every `SourceLocation` copied from it.

const std = @import("std");
const common = @import("common.zig");
const token_module = @import("token.zig");
const char_stream = @import("char_stream.zig");
const source_location = @import("source_location.zig");

pub const Token = token_module.Token;
pub const CharStream = char_stream.CharStream;
pub const SourceLocation = source_location.SourceLocation;

pub const ScannerKind = enum(c_int) {
    Solidity,
    Yul,
    ExperimentalSolidity,
    SpecialComment,
};

pub const ScannerError = enum(c_int) {
    NoError,
    IllegalToken,
    IllegalHexString,
    IllegalHexDigit,
    IllegalCommentTerminator,
    IllegalEscapeSequence,
    UnicodeCharacterInNonUnicodeString,
    IllegalCharacterInString,
    IllegalStringEndQuote,
    IllegalNumberSeparator,
    IllegalExponent,
    IllegalNumberEnd,
    DirectionalOverrideUnderflow,
    DirectionalOverrideMismatch,
    OctalNotAllowed,
};

pub fn errorMessage(scanner_error: ScannerError) []const u8 {
    return switch (scanner_error) {
        .NoError => "No error.",
        .IllegalToken => "Invalid token.",
        .IllegalHexString => "Expected even number of hex-nibbles.",
        .IllegalHexDigit => "Hexadecimal digit missing or invalid.",
        .IllegalCommentTerminator => "Expected multi-line comment-terminator.",
        .IllegalEscapeSequence => "Invalid escape sequence.",
        .UnicodeCharacterInNonUnicodeString => "Invalid character in string. If you are trying to use Unicode characters, use a unicode\"...\" string literal.",
        .IllegalCharacterInString => "Invalid character in string.",
        .IllegalStringEndQuote => "Expected string end-quote.",
        .IllegalNumberSeparator => "Invalid use of number separator '_'.",
        .IllegalExponent => "Invalid exponent.",
        .IllegalNumberEnd => "Identifier-start is not allowed at end of a number.",
        .OctalNotAllowed => "Octal numbers not allowed.",
        .DirectionalOverrideUnderflow => "Unicode direction override underflow in comment or string literal.",
        .DirectionalOverrideMismatch => "Mismatching directional override markers in comment or string literal.",
    };
}

pub const ScanFailure = std.mem.Allocator.Error || char_stream.PositionError || error{
    SourceTooLarge,
};

const TokenInfo = struct {
    first: u32 = 0,
    second: u32 = 0,
};

const TokenDesc = struct {
    token: Token = .EOS,
    location: SourceLocation = .{},
    literal: std.ArrayList(u8) = .empty,
    scanner_error: ScannerError = .NoError,
    extended_token_info: TokenInfo = .{},

    fn resetRetainingCapacity(self: *TokenDesc) void {
        self.token = .EOS;
        self.location = .{};
        self.literal.clearRetainingCapacity();
        self.scanner_error = .NoError;
        self.extended_token_info = .{};
    }

    fn deinit(self: *TokenDesc, allocator: std.mem.Allocator) void {
        self.literal.deinit(allocator);
        self.* = undefined;
    }
};

const current_index = 0;
const next_index = 1;
const next_next_index = 2;

pub const Scanner = struct {
    allocator: std.mem.Allocator,
    source_stream: *CharStream,
    skipped_comments: [3]TokenDesc = .{ .{}, .{}, .{} },
    tokens: [3]TokenDesc = .{ .{}, .{}, .{} },
    kind: ScannerKind = .Solidity,
    current_char: u8 = 0,

    pub fn init(
        allocator: std.mem.Allocator,
        source_stream: *CharStream,
        kind: ScannerKind,
    ) ScanFailure!Scanner {
        if (source_stream.size() > std.math.maxInt(i32)) return error.SourceTooLarge;
        var result: Scanner = .{
            .allocator = allocator,
            .source_stream = source_stream,
        };
        errdefer result.deinit();
        try result.reset();
        if (kind != .Solidity) try result.setScannerMode(kind);
        return result;
    }

    pub fn deinit(self: *Scanner) void {
        for (&self.tokens) |*token| token.deinit(self.allocator);
        for (&self.skipped_comments) |*comment| comment.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn reset(self: *Scanner) ScanFailure!void {
        self.source_stream.reset();
        self.kind = .Solidity;
        self.current_char = try self.source_stream.get(0);
        _ = self.skipWhitespace();
        _ = try self.next();
        _ = try self.next();
        _ = try self.next();
    }

    pub fn setScannerMode(self: *Scanner, kind: ScannerKind) ScanFailure!void {
        self.kind = kind;
        try self.rescan();
    }

    pub fn scannerKind(self: *const Scanner) ScannerKind {
        return self.kind;
    }

    pub fn charStream(self: *const Scanner) *const CharStream {
        return self.source_stream;
    }

    /// Advances the three-token lookahead. On allocation failure the scanner
    /// remains valid but its stream/lookahead have partially advanced.
    pub fn next(self: *Scanner) ScanFailure!Token {
        std.mem.swap(TokenDesc, &self.tokens[current_index], &self.tokens[next_index]);
        std.mem.swap(TokenDesc, &self.tokens[next_index], &self.tokens[next_next_index]);
        std.mem.swap(
            TokenDesc,
            &self.skipped_comments[current_index],
            &self.skipped_comments[next_index],
        );
        std.mem.swap(
            TokenDesc,
            &self.skipped_comments[next_index],
            &self.skipped_comments[next_next_index],
        );
        try self.scanToken();
        return self.tokens[current_index].token;
    }

    pub fn setPosition(self: *Scanner, offset: usize) ScanFailure!void {
        self.current_char = try self.source_stream.setPosition(offset);
        try self.scanToken();
        _ = try self.next();
        _ = try self.next();
    }

    pub fn currentToken(self: *const Scanner) Token {
        return self.tokens[current_index].token;
    }

    pub fn currentElementaryTypeNameToken(
        self: *const Scanner,
    ) token_module.ElementaryTypeError!token_module.ElementaryTypeNameToken {
        const descriptor = self.tokens[current_index];
        return token_module.ElementaryTypeNameToken.init(
            descriptor.token,
            descriptor.extended_token_info.first,
            descriptor.extended_token_info.second,
        );
    }

    pub fn currentLocation(self: *const Scanner) SourceLocation {
        return self.tokens[current_index].location;
    }

    pub fn currentLiteral(self: *const Scanner) []const u8 {
        return self.tokens[current_index].literal.items;
    }

    pub fn currentTokenInfo(self: *const Scanner) TokenInfo {
        return self.tokens[current_index].extended_token_info;
    }

    pub fn currentError(self: *const Scanner) ScannerError {
        return self.tokens[current_index].scanner_error;
    }

    pub fn currentCommentLocation(self: *const Scanner) SourceLocation {
        return self.skipped_comments[current_index].location;
    }

    pub fn currentCommentLiteral(self: *const Scanner) []const u8 {
        return self.skipped_comments[current_index].literal.items;
    }

    pub fn clearCurrentCommentLiteral(self: *Scanner) void {
        self.skipped_comments[current_index].literal.clearRetainingCapacity();
    }

    pub fn peekNextToken(self: *const Scanner) Token {
        return self.tokens[next_index].token;
    }

    pub fn peekLocation(self: *const Scanner) SourceLocation {
        return self.tokens[next_index].location;
    }

    pub fn peekLiteral(self: *const Scanner) []const u8 {
        return self.tokens[next_index].literal.items;
    }

    pub fn peekNextNextToken(self: *const Scanner) Token {
        return self.tokens[next_next_index].token;
    }

    fn setError(self: *Scanner, scanner_error: ScannerError) Token {
        self.tokens[next_next_index].scanner_error = scanner_error;
        return .Illegal;
    }

    fn addLiteralChar(self: *Scanner, c: u8) std.mem.Allocator.Error!void {
        try self.tokens[next_next_index].literal.append(self.allocator, c);
    }

    fn addCommentLiteralChar(self: *Scanner, c: u8) std.mem.Allocator.Error!void {
        try self.skipped_comments[next_next_index].literal.append(self.allocator, c);
    }

    fn addLiteralCharAndAdvance(self: *Scanner) std.mem.Allocator.Error!void {
        try self.addLiteralChar(self.current_char);
        _ = self.advance();
    }

    fn advance(self: *Scanner) bool {
        self.current_char = self.source_stream.advanceAndGet(1);
        return !self.source_stream.isPastEndOfInput(0);
    }

    fn rollback(self: *Scanner, amount: usize) char_stream.PositionError!void {
        self.current_char = try self.source_stream.rollback(amount);
    }

    fn rescan(self: *Scanner) ScanFailure!void {
        const rollback_to: usize = if (self.skipped_comments[current_index].literal.items.len == 0)
            @intCast(self.tokens[current_index].location.start)
        else
            @intCast(self.skipped_comments[current_index].location.start);
        self.current_char = try self.source_stream.rollback(
            self.source_stream.position() - rollback_to,
        );
        _ = try self.next();
        _ = try self.next();
        _ = try self.next();
    }

    fn selectErrorToken(self: *Scanner, scanner_error: ScannerError) Token {
        _ = self.advance();
        return self.setError(scanner_error);
    }

    fn selectToken(self: *Scanner, token: Token) Token {
        _ = self.advance();
        return token;
    }

    fn selectTokenIf(
        self: *Scanner,
        expected_next: u8,
        then_token: Token,
        else_token: Token,
    ) Token {
        _ = self.advance();
        if (self.current_char == expected_next) return self.selectToken(then_token);
        return else_token;
    }

    fn scanHexByte(self: *Scanner, output: *u8) char_stream.PositionError!bool {
        var value: u8 = 0;
        for (0..2) |index| {
            const digit = common.hexValue(self.current_char);
            if (digit < 0) {
                try self.rollback(index);
                return false;
            }
            value = value *% 16 +% @as(u8, @intCast(digit));
            _ = self.advance();
        }
        output.* = value;
        return true;
    }

    fn scanUnicode(self: *Scanner) char_stream.PositionError!?u32 {
        var value: u32 = 0;
        for (0..4) |index| {
            const digit = common.hexValue(self.current_char);
            if (digit < 0) {
                try self.rollback(index);
                return null;
            }
            value = value * 16 + @as(u32, @intCast(digit));
            _ = self.advance();
        }
        return value;
    }

    fn addUnicodeAsUTF8(
        self: *Scanner,
        codepoint: u32,
    ) std.mem.Allocator.Error!void {
        if (codepoint <= 0x7f) {
            try self.addLiteralChar(@intCast(codepoint));
        } else if (codepoint <= 0x7ff) {
            try self.addLiteralChar(@intCast(0xc0 | (codepoint >> 6)));
            try self.addLiteralChar(@intCast(0x80 | (codepoint & 0x3f)));
        } else {
            try self.addLiteralChar(@intCast(0xe0 | (codepoint >> 12)));
            try self.addLiteralChar(@intCast(0x80 | ((codepoint >> 6) & 0x3f)));
            try self.addLiteralChar(@intCast(0x80 | (codepoint & 0x3f)));
        }
    }

    fn skipWhitespace(self: *Scanner) bool {
        const start_position = self.sourcePos();
        while (common.isWhiteSpace(self.current_char)) _ = self.advance();
        return self.sourcePos() != start_position;
    }

    fn skipWhitespaceExceptUnicodeLinebreak(self: *Scanner) ScanFailure!bool {
        const start_position = self.sourcePos();
        while (common.isWhiteSpace(self.current_char) and !(try self.isUnicodeLinebreak())) {
            _ = self.advance();
        }
        return self.sourcePos() != start_position;
    }

    fn skipSingleLineComment(self: *Scanner) ScanFailure!Token {
        const start_position = self.source_stream.position();
        while (!(try self.isUnicodeLinebreak())) {
            if (!self.advance()) break;
        }
        const bidi_error = try validateBiDiMarkup(self.source_stream, start_position);
        if (bidi_error != .NoError) return self.setError(bidi_error);
        return .Whitespace;
    }

    fn atEndOfLine(self: *const Scanner) bool {
        return self.current_char == '\n' or self.current_char == '\r';
    }

    fn tryScanEndOfLine(self: *Scanner) bool {
        if (self.current_char == '\n') {
            _ = self.advance();
            return true;
        }
        if (self.current_char == '\r') {
            if (self.advance() and self.current_char == '\n') _ = self.advance();
            return true;
        }
        return false;
    }

    fn scanSingleLineDocComment(self: *Scanner) ScanFailure!usize {
        var literal = &self.skipped_comments[next_next_index].literal;
        literal.clearRetainingCapacity();
        var complete = false;
        defer if (!complete) literal.clearRetainingCapacity();

        var end_position = self.source_stream.position();
        _ = try self.skipWhitespaceExceptUnicodeLinebreak();
        while (!self.isSourcePastEndOfInput()) {
            end_position = self.source_stream.position();
            if (self.tryScanEndOfLine()) {
                if (!(try self.skipWhitespaceExceptUnicodeLinebreak())) {
                    end_position = self.source_stream.position();
                }
                if (!self.source_stream.isPastEndOfInput(3) and
                    (try self.source_stream.get(0)) == '/' and
                    (try self.source_stream.get(1)) == '/' and
                    (try self.source_stream.get(2)) == '/')
                {
                    if (!self.source_stream.isPastEndOfInput(4) and
                        (try self.source_stream.get(3)) == '/') break;
                    self.current_char = self.source_stream.advanceAndGet(3);
                    if (self.atEndOfLine()) continue;
                    try self.addCommentLiteralChar('\n');
                } else break;
            } else if (try self.isUnicodeLinebreak()) {
                break;
            }
            try self.addCommentLiteralChar(self.current_char);
            _ = self.advance();
        }
        complete = true;
        return end_position;
    }

    fn skipMultiLineComment(self: *Scanner) ScanFailure!Token {
        const start_position = self.source_stream.position();
        while (!self.isSourcePastEndOfInput()) {
            const previous = self.current_char;
            _ = self.advance();
            if (previous == '*' and self.current_char == '/') {
                const bidi_error = try validateBiDiMarkup(
                    self.source_stream,
                    start_position,
                );
                if (bidi_error != .NoError) return self.setError(bidi_error);
                self.current_char = ' ';
                return .Whitespace;
            }
        }
        return self.setError(.IllegalCommentTerminator);
    }

    fn scanMultiLineDocComment(self: *Scanner) ScanFailure!Token {
        self.skipped_comments[next_next_index].literal.clearRetainingCapacity();
        var end_found = false;
        var chars_added = false;

        while (common.isWhiteSpace(self.current_char) and !self.atEndOfLine()) {
            _ = self.advance();
        }
        while (!self.isSourcePastEndOfInput()) {
            if (self.atEndOfLine()) {
                _ = self.skipWhitespace();
                if (!self.source_stream.isPastEndOfInput(1) and
                    (try self.source_stream.get(0)) == '*' and
                    (try self.source_stream.get(1)) == '*')
                {
                    try self.addCommentLiteralChar('*');
                    _ = self.advance();
                } else if (!self.source_stream.isPastEndOfInput(1) and
                    (try self.source_stream.get(0)) == '*' and
                    (try self.source_stream.get(1)) != '/')
                {
                    self.current_char = self.source_stream.advanceAndGet(1);
                    if (self.atEndOfLine()) continue;
                    if (chars_added) try self.addCommentLiteralChar('\n');
                } else if (!self.source_stream.isPastEndOfInput(1) and
                    (try self.source_stream.get(0)) == '*' and
                    (try self.source_stream.get(1)) == '/')
                {
                    self.current_char = self.source_stream.advanceAndGet(2);
                    end_found = true;
                    break;
                } else if (chars_added) {
                    try self.addCommentLiteralChar('\n');
                }
            }

            if (!self.source_stream.isPastEndOfInput(1) and
                (try self.source_stream.get(0)) == '*' and
                (try self.source_stream.get(1)) == '/')
            {
                self.current_char = self.source_stream.advanceAndGet(2);
                end_found = true;
                break;
            }
            try self.addCommentLiteralChar(self.current_char);
            chars_added = true;
            _ = self.advance();
        }
        if (!end_found) return self.setError(.IllegalCommentTerminator);
        return .CommentLiteral;
    }

    fn scanSlash(self: *Scanner) ScanFailure!Token {
        const first_slash_position: i32 = @intCast(self.sourcePos());
        _ = self.advance();
        if (self.current_char == '/') {
            if (!self.advance()) {
                return .Whitespace;
            } else if (self.current_char == '/') {
                _ = self.advance();
                if (self.current_char == '/') return self.skipSingleLineComment();
                self.skipped_comments[next_next_index].location.start = first_slash_position;
                self.skipped_comments[next_next_index].location.source_name = self.source_stream.name();
                self.skipped_comments[next_next_index].token = .CommentLiteral;
                self.skipped_comments[next_next_index].location.end = @intCast(
                    try self.scanSingleLineDocComment(),
                );
                return .Whitespace;
            } else return self.skipSingleLineComment();
        } else if (self.current_char == '*') {
            if (!self.advance()) {
                return self.setError(.IllegalCommentTerminator);
            } else if (self.current_char == '*') {
                _ = self.advance();
                if (self.current_char == '/') {
                    _ = self.advance();
                    return .Whitespace;
                }
                if (self.current_char == '*') return self.skipMultiLineComment();
                self.skipped_comments[next_next_index].location.start = first_slash_position;
                self.skipped_comments[next_next_index].location.source_name = self.source_stream.name();
                const comment = try self.scanMultiLineDocComment();
                self.skipped_comments[next_next_index].location.end = @intCast(self.sourcePos());
                self.skipped_comments[next_next_index].token = comment;
                if (comment == .Illegal) return .Illegal;
                return .Whitespace;
            } else return self.skipMultiLineComment();
        } else if (self.current_char == '=') {
            return self.selectToken(.AssignDiv);
        }
        return .Div;
    }

    fn scanToken(self: *Scanner) ScanFailure!void {
        self.tokens[next_next_index].resetRetainingCapacity();
        self.skipped_comments[next_next_index].resetRetainingCapacity();

        var token: Token = undefined;
        var first_number: u32 = 0;
        var second_number: u32 = 0;
        while (true) {
            self.tokens[next_next_index].location.start = @intCast(self.sourcePos());
            token = switch (self.current_char) {
                '"', '\'' => try self.scanString(false),
                '<' => blk: {
                    _ = self.advance();
                    if (self.current_char == '=') break :blk self.selectToken(.LessThanOrEqual);
                    if (self.current_char == '<') {
                        break :blk self.selectTokenIf('=', .AssignShl, .SHL);
                    }
                    break :blk .LessThan;
                },
                '>' => blk: {
                    _ = self.advance();
                    if (self.current_char == '=') break :blk self.selectToken(.GreaterThanOrEqual);
                    if (self.current_char == '>') {
                        _ = self.advance();
                        if (self.current_char == '=') break :blk self.selectToken(.AssignSar);
                        if (self.current_char == '>') {
                            break :blk self.selectTokenIf('=', .AssignShr, .SHR);
                        }
                        break :blk .SAR;
                    }
                    break :blk .GreaterThan;
                },
                '=' => blk: {
                    _ = self.advance();
                    if (self.current_char == '=') break :blk self.selectToken(.Equal);
                    if (self.current_char == '>') break :blk self.selectToken(.DoubleArrow);
                    break :blk .Assign;
                },
                '!' => blk: {
                    _ = self.advance();
                    if (self.current_char == '=') break :blk self.selectToken(.NotEqual);
                    break :blk .Not;
                },
                '+' => blk: {
                    _ = self.advance();
                    if (self.current_char == '+') break :blk self.selectToken(.Inc);
                    if (self.current_char == '=') break :blk self.selectToken(.AssignAdd);
                    break :blk .Add;
                },
                '-' => blk: {
                    _ = self.advance();
                    if (self.current_char == '-') break :blk self.selectToken(.Dec);
                    if (self.current_char == '=') break :blk self.selectToken(.AssignSub);
                    if (self.current_char == '>') break :blk self.selectToken(.RightArrow);
                    break :blk .Sub;
                },
                '*' => blk: {
                    _ = self.advance();
                    if (self.current_char == '*') break :blk self.selectToken(.Exp);
                    if (self.current_char == '=') break :blk self.selectToken(.AssignMul);
                    break :blk .Mul;
                },
                '%' => self.selectTokenIf('=', .AssignMod, .Mod),
                '/' => try self.scanSlash(),
                '&' => blk: {
                    _ = self.advance();
                    if (self.current_char == '&') break :blk self.selectToken(.And);
                    if (self.current_char == '=') break :blk self.selectToken(.AssignBitAnd);
                    break :blk .BitAnd;
                },
                '|' => blk: {
                    _ = self.advance();
                    if (self.current_char == '|') break :blk self.selectToken(.Or);
                    if (self.current_char == '=') break :blk self.selectToken(.AssignBitOr);
                    break :blk .BitOr;
                },
                '^' => self.selectTokenIf('=', .AssignBitXor, .BitXor),
                '.' => blk: {
                    _ = self.advance();
                    if (self.kind != .ExperimentalSolidity and
                        common.isDecimalDigit(self.current_char))
                    {
                        break :blk try self.scanNumber('.');
                    }
                    break :blk .Period;
                },
                ':' => blk: {
                    _ = self.advance();
                    if (self.current_char == '=') break :blk self.selectToken(.AssemblyAssign);
                    break :blk .Colon;
                },
                ';' => self.selectToken(.Semicolon),
                ',' => self.selectToken(.Comma),
                '(' => self.selectToken(.LParen),
                ')' => self.selectToken(.RParen),
                '[' => self.selectToken(.LBrack),
                ']' => self.selectToken(.RBrack),
                '{' => self.selectToken(.LBrace),
                '}' => self.selectToken(.RBrace),
                '?' => self.selectToken(.Conditional),
                '~' => self.selectToken(.BitNot),
                else => blk: {
                    if (common.isIdentifierStart(self.current_char)) {
                        const identifier = try self.scanIdentifierOrKeyword();
                        first_number = identifier.first_number;
                        second_number = identifier.second_number;
                        var identifier_token = identifier.token;
                        if (identifier_token == .Hex) {
                            first_number = 0;
                            second_number = 0;
                            if (self.current_char == '"' or self.current_char == '\'') {
                                identifier_token = try self.scanHexString();
                            } else identifier_token = self.setError(.IllegalToken);
                        } else if (identifier_token == .Unicode and self.kind != .Yul) {
                            first_number = 0;
                            second_number = 0;
                            if (self.current_char == '"' or self.current_char == '\'') {
                                identifier_token = try self.scanString(true);
                            } else identifier_token = self.setError(.IllegalToken);
                        }
                        break :blk identifier_token;
                    }
                    if (common.isDecimalDigit(self.current_char)) {
                        break :blk try self.scanNumber(0);
                    }
                    if (self.skipWhitespace()) break :blk .Whitespace;
                    if (self.isSourcePastEndOfInput()) break :blk .EOS;
                    break :blk self.selectErrorToken(.IllegalToken);
                },
            };
            if (token != .Whitespace) break;
        }
        self.tokens[next_next_index].location.end = @intCast(self.sourcePos());
        self.tokens[next_next_index].location.source_name = self.source_stream.name();
        self.tokens[next_next_index].token = token;
        self.tokens[next_next_index].extended_token_info = .{
            .first = first_number,
            .second = second_number,
        };
    }

    fn scanEscape(self: *Scanner) ScanFailure!bool {
        var c = self.current_char;
        if (self.tryScanEndOfLine()) return true;
        _ = self.advance();
        switch (c) {
            '\'', '"', '\\' => {},
            'n' => c = '\n',
            'r' => c = '\r',
            't' => c = '\t',
            'u' => {
                if (try self.scanUnicode()) |codepoint| {
                    try self.addUnicodeAsUTF8(codepoint);
                } else return false;
                return true;
            },
            'x' => if (!(try self.scanHexByte(&c))) return false,
            else => return false,
        }
        try self.addLiteralChar(c);
        return true;
    }

    fn isUnicodeLinebreak(self: *const Scanner) char_stream.PositionError!bool {
        if (self.current_char >= 0x0a and self.current_char <= 0x0d) return true;
        if (!self.source_stream.isPastEndOfInput(1) and
            (try self.source_stream.get(0)) == 0xc2 and
            (try self.source_stream.get(1)) == 0x85) return true;
        if (!self.source_stream.isPastEndOfInput(2) and
            (try self.source_stream.get(0)) == 0xe2 and
            (try self.source_stream.get(1)) == 0x80)
        {
            const third = try self.source_stream.get(2);
            if (third == 0xa8 or third == 0xa9) return true;
        }
        return false;
    }

    fn scanString(self: *Scanner, is_unicode: bool) ScanFailure!Token {
        const start_position = self.source_stream.position();
        const quote = self.current_char;
        _ = self.advance();
        var literal = &self.tokens[next_next_index].literal;
        literal.clearRetainingCapacity();
        var complete = false;
        defer if (!complete) literal.clearRetainingCapacity();

        while (self.current_char != quote and
            !self.isSourcePastEndOfInput() and
            (!(try self.isUnicodeLinebreak()) or self.kind == .SpecialComment))
        {
            const c = self.current_char;
            _ = self.advance();
            if (self.kind == .SpecialComment) {
                if (c == '\\') {
                    if (self.isSourcePastEndOfInput()) {
                        return self.setError(.IllegalEscapeSequence);
                    }
                    _ = self.advance();
                } else try self.addLiteralChar(c);
            } else if (c == '\\') {
                if (self.isSourcePastEndOfInput() or !(try self.scanEscape())) {
                    return self.setError(.IllegalEscapeSequence);
                }
            } else {
                if (!is_unicode and (c <= 0x1f or c >= 0x7f)) {
                    if (self.kind == .Yul) return self.setError(.IllegalCharacterInString);
                    return self.setError(.UnicodeCharacterInNonUnicodeString);
                }
                try self.addLiteralChar(c);
            }
        }
        if (self.current_char != quote) return self.setError(.IllegalStringEndQuote);
        if (is_unicode) {
            const bidi_error = try validateBiDiMarkup(self.source_stream, start_position);
            if (bidi_error != .NoError) return self.setError(bidi_error);
        }
        complete = true;
        _ = self.advance();
        return if (is_unicode) .UnicodeStringLiteral else .StringLiteral;
    }

    fn scanHexString(self: *Scanner) ScanFailure!Token {
        const quote = self.current_char;
        _ = self.advance();
        var literal = &self.tokens[next_next_index].literal;
        literal.clearRetainingCapacity();
        var complete = false;
        defer if (!complete) literal.clearRetainingCapacity();
        var allow_underscore = false;

        while (self.current_char != quote and !self.isSourcePastEndOfInput()) {
            var c = self.current_char;
            if (try self.scanHexByte(&c)) {
                try self.addLiteralChar(c);
                allow_underscore = true;
            } else if (c == '_') {
                _ = self.advance();
                if (!allow_underscore or self.current_char == quote) {
                    return self.setError(.IllegalNumberSeparator);
                }
                allow_underscore = false;
            } else return self.setError(.IllegalHexString);
        }
        if (self.current_char != quote) return self.setError(.IllegalStringEndQuote);
        complete = true;
        _ = self.advance();
        return .HexStringLiteral;
    }

    fn scanDecimalDigits(self: *Scanner) std.mem.Allocator.Error!void {
        if (!common.isDecimalDigit(self.current_char)) return;
        while (true) {
            try self.addLiteralCharAndAdvance();
            if (self.source_stream.isPastEndOfInput(0) or
                (!common.isDecimalDigit(self.current_char) and self.current_char != '_')) break;
        }
    }

    fn scanNumber(self: *Scanner, char_seen: u8) ScanFailure!Token {
        const NumberKind = enum { decimal, hex, binary };
        var number_kind: NumberKind = .decimal;
        var literal = &self.tokens[next_next_index].literal;
        literal.clearRetainingCapacity();
        var complete = false;
        defer if (!complete) literal.clearRetainingCapacity();

        if (char_seen == '.') {
            try self.addLiteralChar('.');
            if (self.current_char == '_') return self.setError(.IllegalToken);
            try self.scanDecimalDigits();
        } else {
            std.debug.assert(char_seen == 0);
            if (self.current_char == '0') {
                try self.addLiteralCharAndAdvance();
                if (self.current_char == 'x') {
                    number_kind = .hex;
                    try self.addLiteralCharAndAdvance();
                    if (!common.isHexDigit(self.current_char)) {
                        return self.setError(.IllegalHexDigit);
                    }
                    while (common.isHexDigit(self.current_char) or self.current_char == '_') {
                        try self.addLiteralCharAndAdvance();
                    }
                } else if (common.isDecimalDigit(self.current_char)) {
                    return self.setError(.OctalNotAllowed);
                }
            }
            if (number_kind == .decimal) {
                try self.scanDecimalDigits();
                if (self.current_char == '.') {
                    if (!self.source_stream.isPastEndOfInput(1) and
                        (try self.source_stream.get(1)) == '_')
                    {
                        try self.addLiteralCharAndAdvance();
                        try self.addLiteralCharAndAdvance();
                        try self.scanDecimalDigits();
                    }
                    if (self.source_stream.isPastEndOfInput(0) or
                        !common.isDecimalDigit(try self.source_stream.get(1)))
                    {
                        complete = true;
                        return .Number;
                    }
                    try self.addLiteralCharAndAdvance();
                    try self.scanDecimalDigits();
                }
            }
        }

        if (self.current_char == 'e' or self.current_char == 'E') {
            std.debug.assert(number_kind != .hex);
            if (number_kind != .decimal) return self.setError(.IllegalExponent);
            if (!self.source_stream.isPastEndOfInput(1) and
                (try self.source_stream.get(1)) == '_')
            {
                try self.addLiteralCharAndAdvance();
                try self.addLiteralCharAndAdvance();
                try self.scanDecimalDigits();
                complete = true;
                return .Number;
            }
            try self.addLiteralCharAndAdvance();
            if (self.current_char == '+' or self.current_char == '-') {
                try self.addLiteralCharAndAdvance();
            }
            if (!common.isDecimalDigit(self.current_char)) {
                return self.setError(.IllegalExponent);
            }
            try self.scanDecimalDigits();
        }
        if (common.isDecimalDigit(self.current_char) or
            common.isIdentifierStart(self.current_char))
        {
            return self.setError(.IllegalNumberEnd);
        }
        complete = true;
        return .Number;
    }

    fn scanIdentifierOrKeyword(self: *Scanner) ScanFailure!token_module.IdentifierToken {
        std.debug.assert(common.isIdentifierStart(self.current_char));
        var literal = &self.tokens[next_next_index].literal;
        literal.clearRetainingCapacity();
        var complete = false;
        defer if (!complete) literal.clearRetainingCapacity();
        try self.addLiteralCharAndAdvance();
        while (common.isIdentifierPart(self.current_char) or
            (self.current_char == '.' and self.kind == .Yul))
        {
            try self.addLiteralCharAndAdvance();
        }
        complete = true;

        const recognized = token_module.fromIdentifierOrKeyword(literal.items);
        switch (self.kind) {
            .SpecialComment => return .{ .token = .Identifier },
            .Solidity => if (token_module.isExperimentalSolidityOnlyKeyword(recognized.token)) {
                return .{ .token = .Identifier };
            },
            .Yul => {
                if (std.mem.eql(u8, literal.items, "leave")) return .{ .token = .Leave };
                if (!token_module.isYulKeywordToken(recognized.token)) {
                    return .{ .token = .Identifier };
                }
            },
            .ExperimentalSolidity => if (!token_module.isExperimentalSolidityKeyword(
                recognized.token,
            )) {
                return .{ .token = .Identifier };
            },
        }
        return recognized;
    }

    fn sourcePos(self: *const Scanner) usize {
        return self.source_stream.position();
    }

    fn isSourcePastEndOfInput(self: *const Scanner) bool {
        return self.source_stream.isPastEndOfInput(0);
    }
};

fn validateBiDiMarkup(
    stream: *CharStream,
    start_position: usize,
) char_stream.PositionError!ScannerError {
    const DirectionalSequence = struct {
        bytes: []const u8,
        depth_change: i32,
    };
    const directional_sequences = [_]DirectionalSequence{
        .{ .bytes = "\xE2\x80\xAD", .depth_change = 1 },
        .{ .bytes = "\xE2\x80\xAE", .depth_change = 1 },
        .{ .bytes = "\xE2\x80\xAA", .depth_change = 1 },
        .{ .bytes = "\xE2\x80\xAB", .depth_change = 1 },
        .{ .bytes = "\xE2\x80\xAC", .depth_change = -1 },
    };
    const end_position = stream.position();
    _ = try stream.setPosition(start_position);
    var depth: i32 = 0;
    var current_position = start_position;
    while (current_position < end_position) : (current_position += 1) {
        _ = try stream.setPosition(current_position);
        for (directional_sequences) |sequence| {
            if (stream.prefixMatch(sequence.bytes)) depth += sequence.depth_change;
        }
        if (depth < 0) return .DirectionalOverrideUnderflow;
    }
    _ = try stream.setPosition(end_position);
    return if (depth > 0) .DirectionalOverrideMismatch else .NoError;
}

fn expectTokenSequence(
    input: []const u8,
    kind: ScannerKind,
    expected: []const Token,
) !void {
    var stream = CharStream.initBorrowed(input, "test.sol");
    var scanner = try Scanner.init(std.testing.allocator, &stream, kind);
    defer scanner.deinit();
    for (expected, 0..) |expected_token, index| {
        if (index != 0) _ = try scanner.next();
        try std.testing.expectEqual(expected_token, scanner.currentToken());
    }
}

test "scanner smoke stream, literals, and lookahead" {
    var stream = CharStream.initBorrowed(
        "function break;765  \t  \"string1\",'string2'\nidentifier1",
        "test.sol",
    );
    var scanner = try Scanner.init(std.testing.allocator, &stream, .Solidity);
    defer scanner.deinit();
    try std.testing.expectEqual(Token.Function, scanner.currentToken());
    try std.testing.expectEqual(Token.Break, scanner.peekNextToken());
    _ = try scanner.next();
    _ = try scanner.next();
    try std.testing.expectEqual(Token.Semicolon, scanner.currentToken());
    _ = try scanner.next();
    try std.testing.expectEqual(Token.Number, scanner.currentToken());
    try std.testing.expectEqualStrings("765", scanner.currentLiteral());
    _ = try scanner.next();
    try std.testing.expectEqualStrings("string1", scanner.currentLiteral());
}

test "scanner operators, modes, locations, and errors" {
    try expectTokenSequence(
        "<=<+ +=a++ =><<>> >>=>>>>>>= >>>>>=><<=",
        .Solidity,
        &.{
            .LessThanOrEqual, .LessThan,  .Add,         .AssignAdd, .Identifier, .Inc,
            .DoubleArrow,     .SHL,       .SAR,         .AssignSar, .SHR,        .AssignShr,
            .SHR,             .AssignSar, .GreaterThan, .AssignShl,
        },
    );
    try expectTokenSequence(
        "function a...a(",
        .Yul,
        &.{ .Function, .Identifier, .LParen, .EOS },
    );

    var stream = CharStream.initBorrowed("0X1234", "test.sol");
    var scanner = try Scanner.init(std.testing.allocator, &stream, .Solidity);
    defer scanner.deinit();
    try std.testing.expectEqual(Token.Illegal, scanner.currentToken());
    try std.testing.expectEqual(ScannerError.IllegalNumberEnd, scanner.currentError());
    try std.testing.expectEqual(@as(i32, 0), scanner.currentLocation().start);
}

fn scannerAllocationFailure(allocator: std.mem.Allocator) !void {
    var stream = CharStream.initBorrowed(
        "contract C { string s = unicode\"hello 😃\"; bytes32 x = hex\"00112233\"; }",
        "C.sol",
    );
    var scanner = try Scanner.init(allocator, &stream, .Solidity);
    defer scanner.deinit();
    while (scanner.currentToken() != .EOS) _ = try scanner.next();
}

test "scanner releases partial literals on every allocation failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        scannerAllocationFailure,
        .{},
    );
}
