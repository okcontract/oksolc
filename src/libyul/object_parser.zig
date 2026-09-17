// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Parser for Yul code/data object containers.

const std = @import("std");
const AST = @import("ast.zig");
const AsmParser = @import("asm_parser.zig");
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const ObjectModule = @import("object.zig");
const ParserBase = @import("../liblangutil/parser_base.zig");
const ScannerModule = @import("../liblangutil/scanner.zig");
const StringUtils = @import("../libsolutil/string_utils.zig");
const Token = @import("../liblangutil/token.zig").Token;

pub const ParseError = AsmParser.ParseError || ParserBase.ParserFailure || error{
    MissingCodeAfterParseFailure,
};

pub const ObjectParser = struct {
    allocator: std.mem.Allocator,
    base: ParserBase.ParserBase,
    dialect: AST.Dialect,

    pub fn init(
        allocator: std.mem.Allocator,
        scanner: *ScannerModule.Scanner,
        error_reporter: *Diagnostics.ErrorReporter,
        dialect: AST.Dialect,
    ) ObjectParser {
        return .{
            .allocator = allocator,
            .base = ParserBase.ParserBase.init(allocator, scanner, error_reporter),
            .dialect = dialect,
        };
    }

    pub fn parseSource(
        allocator: std.mem.Allocator,
        source: []const u8,
        source_name: []const u8,
        error_reporter: *Diagnostics.ErrorReporter,
        dialect: AST.Dialect,
    ) ParseError!?*ObjectModule.Object {
        var stream = ScannerModule.CharStream.initBorrowed(source, source_name);
        var scanner = try ScannerModule.Scanner.init(allocator, &stream, .Solidity);
        defer scanner.deinit();
        var parser = ObjectParser.init(allocator, &scanner, error_reporter, dialect);
        return parser.parse(false);
    }

    /// Parses either a full object or the code-only `{ ... }` form.  A fatal
    /// diagnostic is represented by `null`, matching the upstream shared_ptr.
    pub fn parse(
        self: *ObjectParser,
        reuse_scanner: bool,
    ) ParseError!?*ObjectModule.Object {
        self.base.recursion_depth = 0;
        return self.parseImpl(reuse_scanner) catch |err| switch (err) {
            error.FatalDiagnostic, error.MissingCodeAfterParseFailure => null,
            else => return err,
        };
    }

    fn parseImpl(self: *ObjectParser, reuse_scanner: bool) ParseError!*ObjectModule.Object {
        const object = if (self.base.currentToken() == .LBrace)
            try self.parseCodeOnly()
        else
            try self.parseObject(null);
        errdefer object.destroy();
        if (!reuse_scanner) try self.base.expectToken(.EOS, true);
        return object;
    }

    fn parseCodeOnly(self: *ObjectParser) ParseError!*ObjectModule.Object {
        const object = try ObjectModule.Object.create(self.allocator, "object");
        errdefer object.destroy();
        object.debug_data = .{ .source_names = try self.tryParseSourceNameMapping() };
        const code = (try self.parseBlock(
            if (object.debug_data.?.source_names) |*source_names| source_names else null,
        )) orelse return error.MissingCodeAfterParseFailure;
        object.setCode(code, null);
        return object;
    }

    fn parseObject(
        self: *ObjectParser,
        containing_object: ?*const ObjectModule.Object,
    ) ParseError!*ObjectModule.Object {
        var recursion_guard = try self.base.recursionGuard();
        defer recursion_guard.deinit();

        const source_names = try self.tryParseSourceNameMapping();
        var source_names_owned = true;
        errdefer if (source_names_owned) {
            if (source_names) |value| {
                var mutable_value = value;
                mutable_value.deinit(self.allocator);
            }
        };

        if (self.base.currentToken() != .Identifier or
            !std.mem.eql(u8, self.base.currentLiteral(), "object"))
        {
            try self.base.fatalParserError(
                .{ .value = 4294 },
                self.base.currentLocation(),
                "Expected keyword \"object\".",
            );
        }
        _ = try self.base.advance();

        const name = try self.parseUniqueName(containing_object);
        defer self.allocator.free(name);
        const object = try ObjectModule.Object.create(self.allocator, name);
        errdefer object.destroy();
        object.debug_data = .{ .source_names = source_names };
        source_names_owned = false;

        try self.base.expectToken(.LBrace, true);
        if (try self.parseCode(
            if (object.debug_data.?.source_names) |*mapping| mapping else null,
        )) |code| object.setCode(code, null);

        while (self.base.currentToken() != .RBrace) {
            if (self.base.currentToken() == .Identifier and
                std.mem.eql(u8, self.base.currentLiteral(), "object"))
            {
                const child = try self.parseObject(object);
                object.addSubObject(.{ .object = child }) catch |err| {
                    child.destroy();
                    return err;
                };
            } else if (self.base.currentToken() == .Identifier and
                std.mem.eql(u8, self.base.currentLiteral(), "data"))
            {
                try self.parseData(object);
            } else {
                try self.base.fatalParserError(
                    .{ .value = 8143 },
                    self.base.currentLocation(),
                    "Expected keyword \"data\" or \"object\" or \"}\".",
                );
            }
        }
        try self.base.expectToken(.RBrace, true);
        return object;
    }

    fn parseCode(
        self: *ObjectParser,
        source_names: ?*const ObjectModule.SourceNameMap,
    ) ParseError!?AST.AST {
        if (self.base.currentToken() != .Identifier or
            !std.mem.eql(u8, self.base.currentLiteral(), "code"))
        {
            try self.base.fatalParserError(
                .{ .value = 4846 },
                self.base.currentLocation(),
                "Expected keyword \"code\".",
            );
        }
        _ = try self.base.advance();
        return self.parseBlock(source_names);
    }

    fn parseBlock(
        self: *ObjectParser,
        source_names: ?*const ObjectModule.SourceNameMap,
    ) ParseError!?AST.AST {
        const parser_entries = if (source_names) |mapping|
            try mapping.parserEntriesAlloc(self.allocator)
        else
            null;
        defer if (parser_entries) |entries| self.allocator.free(entries);
        var parser = AsmParser.Parser.init(
            self.allocator,
            self.base.scanner,
            self.base.error_reporter,
            self.dialect,
            .{ .source_names = parser_entries },
        );
        const block = (try parser.parseInline()) orelse return null;
        return AST.AST.init(self.allocator, self.dialect, block);
    }

    fn tryParseSourceNameMapping(
        self: *ObjectParser,
    ) ParseError!?ObjectModule.SourceNameMap {
        const comment = self.base.scanner.currentCommentLiteral();
        const tag_end = findUseSrcTagEnd(comment) orelse return null;
        const arguments = comment[tag_end..];
        var stream = ScannerModule.CharStream.initBorrowed(arguments, "");
        var scanner = try ScannerModule.Scanner.init(self.allocator, &stream, .Solidity);
        defer scanner.deinit();
        var source_names: ObjectModule.SourceNameMap = .{};
        errdefer source_names.deinit(self.allocator);
        if (scanner.currentToken() == .EOS) return source_names;

        while (scanner.currentToken() != .EOS) {
            if (scanner.currentToken() != .Number) break;
            const source_index = StringUtils.toUnsignedInt(scanner.currentLiteral()) orelse break;
            if (try scanner.next() != .Colon) break;
            if (try scanner.next() != .StringLiteral) break;
            try source_names.put(self.allocator, source_index, scanner.currentLiteral());
            const next = try scanner.next();
            if (next == .EOS) return source_names;
            if (next != .Comma) break;
            _ = try scanner.next();
        }

        source_names.deinit(self.allocator);
        source_names = .{};
        try self.base.error_reporter.syntaxError(
            .{ .value = 9804 },
            self.base.scanner.currentCommentLocation(),
            "Error parsing arguments to @use-src. Expected: <number> \":\" \"<filename>\", ...",
        );
        return null;
    }

    fn parseData(self: *ObjectParser, containing_object: *ObjectModule.Object) ParseError!void {
        std.debug.assert(self.base.currentToken() == .Identifier);
        std.debug.assert(std.mem.eql(u8, self.base.currentLiteral(), "data"));
        _ = try self.base.advance();

        const name = try self.parseUniqueName(containing_object);
        var name_owned = true;
        errdefer if (name_owned) self.allocator.free(name);
        if (self.base.currentToken() == .HexStringLiteral)
            try self.base.expectToken(.HexStringLiteral, false)
        else
            try self.base.expectToken(.StringLiteral, false);
        const data = try self.allocator.dupe(u8, self.base.currentLiteral());
        var data_owned = true;
        errdefer if (data_owned) self.allocator.free(data);
        var node: ObjectModule.ObjectNode = .{
            .data = ObjectModule.Data.initOwned(name, data),
        };
        containing_object.addSubObject(node) catch |err| {
            node.deinit(self.allocator);
            name_owned = false;
            data_owned = false;
            return err;
        };
        name_owned = false;
        data_owned = false;
        _ = try self.base.advance();
    }

    fn parseUniqueName(
        self: *ObjectParser,
        containing_object: ?*const ObjectModule.Object,
    ) ParseError![]const u8 {
        try self.base.expectToken(.StringLiteral, false);
        const name = try self.allocator.dupe(u8, self.base.currentLiteral());
        errdefer self.allocator.free(name);
        if (name.len == 0) {
            try self.base.parserError(
                .{ .value = 3287 },
                self.base.currentLocation(),
                "Object name cannot be empty.",
            );
        } else if (containing_object) |container| {
            if (std.mem.eql(u8, container.name, name)) {
                try self.base.parserError(
                    .{ .value = 8311 },
                    self.base.currentLocation(),
                    "Object name cannot be the same as the name of the containing object.",
                );
            } else if (container.sub_index_by_name.contains(name)) {
                const description = try std.fmt.allocPrint(
                    self.allocator,
                    "Object name \"{s}\" already exists inside the containing object.",
                    .{name},
                );
                defer self.allocator.free(description);
                try self.base.parserError(
                    .{ .value = 8794 },
                    self.base.currentLocation(),
                    description,
                );
            }
        }
        _ = try self.base.advance();
        return name;
    }
};

fn findUseSrcTagEnd(comment: []const u8) ?usize {
    const tag = "@use-src";
    var start: usize = 0;
    while (std.mem.findPos(u8, comment, start, tag)) |position| {
        const valid_start = position == 0 or std.ascii.isWhitespace(comment[position - 1]);
        const end = position + tag.len;
        const valid_end = end == comment.len or !isWordCharacter(comment[end]);
        if (valid_start and valid_end) return end;
        start = position + 1;
    }
    return null;
}

fn isWordCharacter(character: u8) bool {
    return std.ascii.isAlphanumeric(character) or character == '_';
}

test "object parser handles source mappings, nested objects, and data" {
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const object = (try ObjectParser.parseSource(
        allocator,
        \\/// @use-src 2:"two.sol", 0:"zero.sol"
        \\object "A" {
        \\    code { let x := 1 }
        \\    object "B" { code { } data "payload" hex"0102" }
        \\    data "text" "abc"
        \\}
    ,
        "input.yul",
        &reporter,
        .{},
    )).?;
    defer object.destroy();
    try std.testing.expect(!reporter.hasErrors());
    try std.testing.expectEqual(@as(usize, 2), object.sub_objects.items.len);
    try std.testing.expectEqual(@as(usize, 0), object.sub_index_by_name.get("B").?);
    try std.testing.expectEqual(@as(usize, 1), object.sub_index_by_name.get("text").?);
    try std.testing.expect(!(try object.hasContiguousSourceIndices()));
    const rendered = try object.toStringAlloc(.noneValue(), null);
    defer allocator.free(rendered);
    try std.testing.expectEqualStrings(
        \\/// @use-src 0:"zero.sol", 2:"two.sol"
        \\object "A" {
        \\    code { let x := 1 }
        \\    object "B" {
        \\        code { }
        \\        data "payload" hex"0102"
        \\    }
        \\    data "text" hex"616263"
        \\}
    ,
        rendered,
    );
}

test "object parser diagnoses duplicate names but retains the first lookup" {
    const allocator = std.testing.allocator;
    var reporter = Diagnostics.ErrorReporter.init(allocator);
    defer reporter.deinit();
    const object = (try ObjectParser.parseSource(
        allocator,
        "object \"A\" { code { } data \"x\" \"a\" data \"x\" \"b\" }",
        "input.yul",
        &reporter,
        .{},
    )).?;
    defer object.destroy();
    try std.testing.expectEqual(@as(usize, 2), object.sub_objects.items.len);
    try std.testing.expectEqual(@as(usize, 0), object.sub_index_by_name.get("x").?);
    try std.testing.expectEqual(@as(usize, 1), reporter.diagnostics().len);
    try std.testing.expectEqual(@as(u64, 8794), reporter.diagnostics()[0].error_id.value);
}
