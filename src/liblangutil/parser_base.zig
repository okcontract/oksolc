// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared parser mechanics translated from `ParserBase.h/.cpp`.

const std = @import("std");
const ScannerModule = @import("scanner.zig");
const TokenModule = @import("token.zig");
const Diagnostics = @import("diagnostics.zig");
const SourceLocation = @import("source_location.zig").SourceLocation;

pub const ParserFailure = ScannerModule.ScanFailure ||
    Diagnostics.ReportError ||
    TokenModule.ElementaryTypeError;

pub const ParserBase = struct {
    allocator: std.mem.Allocator,
    scanner: *ScannerModule.Scanner,
    error_reporter: *Diagnostics.ErrorReporter,
    recursion_depth: usize = 0,

    pub fn init(
        allocator: std.mem.Allocator,
        scanner: *ScannerModule.Scanner,
        error_reporter: *Diagnostics.ErrorReporter,
    ) ParserBase {
        return .{
            .allocator = allocator,
            .scanner = scanner,
            .error_reporter = error_reporter,
        };
    }

    pub fn currentLocation(self: *const ParserBase) SourceLocation {
        return self.scanner.currentLocation();
    }

    pub fn currentToken(self: *const ParserBase) TokenModule.Token {
        return self.scanner.currentToken();
    }

    pub fn peekNextToken(self: *const ParserBase) TokenModule.Token {
        return self.scanner.peekNextToken();
    }

    pub fn currentLiteral(self: *const ParserBase) []const u8 {
        return self.scanner.currentLiteral();
    }

    pub fn advance(self: *ParserBase) ScannerModule.ScanFailure!TokenModule.Token {
        return self.scanner.next();
    }

    pub fn tokenNameAlloc(
        self: *const ParserBase,
        token: TokenModule.Token,
    ) ![]u8 {
        if (token == .Identifier) return self.allocator.dupe(u8, "identifier");
        if (token == .EOS) return self.allocator.dupe(u8, "end of source");
        if (TokenModule.isReservedKeyword(token)) {
            return std.fmt.allocPrint(
                self.allocator,
                "reserved keyword '{s}'",
                .{TokenModule.friendlyName(token)},
            );
        }
        if (TokenModule.isElementaryTypeName(token)) {
            const elementary = try self.scanner.currentElementaryTypeNameToken();
            const name = try elementary.renderAlloc(self.allocator, false);
            defer self.allocator.free(name);
            return std.fmt.allocPrint(self.allocator, "'{s}'", .{name});
        }
        return std.fmt.allocPrint(self.allocator, "'{s}'", .{TokenModule.friendlyName(token)});
    }

    pub fn expectToken(
        self: *ParserBase,
        expected: TokenModule.Token,
        should_advance: bool,
    ) ParserFailure!void {
        const actual = self.currentToken();
        if (actual != expected) {
            const expected_name = try self.tokenNameAlloc(expected);
            defer self.allocator.free(expected_name);
            const actual_name = try self.tokenNameAlloc(actual);
            defer self.allocator.free(actual_name);
            const description = try std.fmt.allocPrint(
                self.allocator,
                "Expected {s} but got {s}",
                .{ expected_name, actual_name },
            );
            defer self.allocator.free(description);
            try self.fatalParserError(.{ .value = 2314 }, self.currentLocation(), description);
        }
        if (should_advance) _ = try self.advance();
    }

    pub fn increaseRecursionDepth(self: *ParserBase) Diagnostics.ReportError!void {
        self.recursion_depth += 1;
        if (self.recursion_depth >= 1200) {
            try self.fatalParserError(
                .{ .value = 7319 },
                self.currentLocation(),
                "Maximum recursion depth reached during parsing.",
            );
        }
    }

    pub fn decreaseRecursionDepth(self: *ParserBase) void {
        std.debug.assert(self.recursion_depth > 0);
        self.recursion_depth -= 1;
    }

    pub fn recursionGuard(self: *ParserBase) Diagnostics.ReportError!RecursionGuard {
        try self.increaseRecursionDepth();
        return .{ .parser = self };
    }

    pub fn parserError(
        self: *ParserBase,
        error_id: Diagnostics.ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) Diagnostics.ReportError!void {
        try self.error_reporter.parserError(error_id, location, description);
    }

    pub fn parserWarning(
        self: *ParserBase,
        error_id: Diagnostics.ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) Diagnostics.ReportError!void {
        try self.error_reporter.warning(error_id, location, description);
    }

    pub fn fatalParserError(
        self: *ParserBase,
        error_id: Diagnostics.ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) Diagnostics.ReportError!void {
        try self.error_reporter.fatal(
            error_id,
            .ParserError,
            location,
            null,
            description,
        );
    }
};

pub const RecursionGuard = struct {
    parser: *ParserBase,

    pub fn deinit(self: *RecursionGuard) void {
        self.parser.decreaseRecursionDepth();
        self.* = undefined;
    }
};

test "parser base advances and reports fatal token mismatches in order" {
    var stream = ScannerModule.CharStream.initBorrowed("identifier;", "a.sol");
    var scanner = try ScannerModule.Scanner.init(std.testing.allocator, &stream, .Solidity);
    defer scanner.deinit();
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parser = ParserBase.init(std.testing.allocator, &scanner, &reporter);
    try parser.expectToken(.Identifier, true);
    try std.testing.expectError(error.FatalDiagnostic, parser.expectToken(.RBrace, true));
    try std.testing.expectEqual(@as(usize, 1), reporter.diagnostics().len);
    try std.testing.expectEqual(@as(u64, 2314), reporter.diagnostics()[0].error_id.value);
}
