// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! NatSpec tag lexer translated from `DocStringParser.cpp`.

const std = @import("std");
const ASTAnnotations = @import("../ast/ast_annotations.zig");
const Common = @import("../../liblangutil/common.zig");
const Diagnostics = @import("../../liblangutil/diagnostics.zig");

pub const ParseError = std.mem.Allocator.Error || Diagnostics.ReportError;

pub const DocStringParser = struct {
    allocator: std.mem.Allocator,
    text: []const u8,
    location: Diagnostics.SourceLocation,
    reporter: *Diagnostics.ErrorReporter,
    doc_tags: std.ArrayList(ASTAnnotations.DocTagEntry) = .empty,
    last_tag: ?usize = null,

    pub fn init(
        allocator: std.mem.Allocator,
        text: []const u8,
        location: Diagnostics.SourceLocation,
        reporter: *Diagnostics.ErrorReporter,
    ) DocStringParser {
        return .{
            .allocator = allocator,
            .text = text,
            .location = location,
            .reporter = reporter,
        };
    }

    pub fn parse(self: *DocStringParser) ParseError!std.ArrayList(ASTAnnotations.DocTagEntry) {
        self.last_tag = null;
        self.doc_tags = .empty;

        var position: usize = 0;
        while (position != self.text.len) {
            const relative_tag = std.mem.findScalar(u8, self.text[position..], '@');
            const tag_position = if (relative_tag) |offset| position + offset else self.text.len;
            const relative_newline = std.mem.findScalar(u8, self.text[position..], '\n');
            const newline_position = if (relative_newline) |offset| position + offset else self.text.len;

            if (tag_position != self.text.len and tag_position < newline_position) {
                const tag_name_end = firstWhitespaceOrNewline(self.text, tag_position);
                const tag_name = self.text[tag_position + 1 .. tag_name_end];
                const tag_data = if (tag_name_end != self.text.len)
                    tag_name_end + 1
                else
                    tag_name_end;
                position = try self.parseDocTag(tag_data, tag_name);
            } else if (self.last_tag != null) {
                position = try self.parseDocTagLine(position, true);
            } else if (position != self.text.len) {
                if (position == 0) {
                    position = try self.parseDocTag(position, "notice");
                } else if (newline_position == self.text.len) {
                    break;
                } else {
                    position = newline_position + 1;
                }
            }
        }

        std.sort.insertion(
            ASTAnnotations.DocTagEntry,
            self.doc_tags.items,
            {},
            docTagLessThan,
        );
        const result = self.doc_tags;
        self.doc_tags = .empty;
        self.last_tag = null;
        return result;
    }

    fn parseDocTagLine(
        self: *DocStringParser,
        start: usize,
        appending: bool,
    ) ParseError!usize {
        const index = self.last_tag.?;
        var position = start;
        const newline = if (std.mem.findScalar(u8, self.text[position..], '\n')) |offset|
            position + offset
        else
            self.text.len;
        var prefix: []const u8 = "";
        if (appending and position != self.text.len and
            self.text[position] != ' ' and self.text[position] != '\t')
        {
            prefix = " ";
        } else if (!appending) {
            position = skipWhitespace(self.text, position);
        }
        const previous = self.doc_tags.items[index].tag.content;
        const content = try self.allocator.alloc(
            u8,
            previous.len + prefix.len + newline - position,
        );
        @memcpy(content[0..previous.len], previous);
        @memcpy(content[previous.len .. previous.len + prefix.len], prefix);
        @memcpy(content[previous.len + prefix.len ..], self.text[position..newline]);
        self.doc_tags.items[index].tag.content = content;
        return skipLineOrEnd(newline, self.text.len);
    }

    fn parseDocTagParam(
        self: *DocStringParser,
        start: usize,
    ) ParseError!usize {
        const name_start = skipWhitespace(self.text, start);
        if (name_start == self.text.len) {
            try self.reporter.docstringParsingError(
                errorId(3335),
                self.location,
                "No param name given",
            );
            return self.text.len;
        }
        const name_end = firstNonIdentifier(self.text, name_start);
        const parameter_name = self.text[name_start..name_end];
        const description_start = skipWhitespace(self.text, name_end);
        const newline = if (std.mem.findScalar(
            u8,
            self.text[description_start..],
            '\n',
        )) |offset| description_start + offset else self.text.len;
        if (description_start == newline) {
            const message = try std.fmt.allocPrint(
                self.allocator,
                "No description given for param {s}",
                .{parameter_name},
            );
            try self.reporter.docstringParsingError(errorId(9942), self.location, message);
            return self.text.len;
        }

        try self.newTag("param");
        const index = self.last_tag.?;
        self.doc_tags.items[index].tag.parameter_name = try self.allocator.dupe(
            u8,
            parameter_name,
        );
        self.doc_tags.items[index].tag.content = try self.allocator.dupe(
            u8,
            self.text[description_start..newline],
        );
        return skipLineOrEnd(newline, self.text.len);
    }

    fn parseDocTag(
        self: *DocStringParser,
        start: usize,
        tag_name: []const u8,
    ) ParseError!usize {
        if (self.last_tag == null or tag_name.len != 0) {
            if (std.mem.eql(u8, tag_name, "param"))
                return self.parseDocTagParam(start);
            try self.newTag(tag_name);
            return self.parseDocTagLine(start, false);
        }
        return self.parseDocTagLine(start, true);
    }

    fn newTag(self: *DocStringParser, tag_name: []const u8) ParseError!void {
        try self.doc_tags.append(self.allocator, .{
            .name = try self.allocator.dupe(u8, tag_name),
            .tag = .{ .content = "" },
        });
        self.last_tag = self.doc_tags.items.len - 1;
    }
};

pub fn parseDocString(
    allocator: std.mem.Allocator,
    text: []const u8,
    location: Diagnostics.SourceLocation,
    reporter: *Diagnostics.ErrorReporter,
) ParseError!std.ArrayList(ASTAnnotations.DocTagEntry) {
    var parser = DocStringParser.init(allocator, text, location, reporter);
    return parser.parse();
}

fn skipLineOrEnd(newline: usize, end: usize) usize {
    return if (newline == end) end else newline + 1;
}

fn firstWhitespaceOrNewline(text: []const u8, start: usize) usize {
    var position = start;
    while (position != text.len) : (position += 1)
        if (text[position] == ' ' or text[position] == '\t' or text[position] == '\n')
            return position;
    return text.len;
}

fn skipWhitespace(text: []const u8, start: usize) usize {
    var position = start;
    while (position != text.len and
        (text[position] == ' ' or text[position] == '\t')) : (position += 1)
    {}
    return position;
}

fn firstNonIdentifier(text: []const u8, start: usize) usize {
    if (start == text.len or !Common.isIdentifierStart(text[start])) return start;
    var position = start + 1;
    while (position != text.len and Common.isIdentifierPart(text[position])) : (position += 1) {}
    return position;
}

fn docTagLessThan(
    _: void,
    left: ASTAnnotations.DocTagEntry,
    right: ASTAnnotations.DocTagEntry,
) bool {
    return std.mem.order(u8, left.name, right.name) == .lt;
}

fn errorId(value: u64) Diagnostics.ErrorId {
    return .{ .value = value };
}

test "docstring parser preserves multimap order and continuation spacing" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    const tags = try parseDocString(
        arena.allocator(),
        "A notice\ncontinued\n@param value first line\n second line\n@dev details",
        .{},
        &reporter,
    );
    try std.testing.expectEqual(@as(usize, 3), tags.items.len);
    try std.testing.expectEqualStrings("dev", tags.items[0].name);
    try std.testing.expectEqualStrings("notice", tags.items[1].name);
    try std.testing.expectEqualStrings("A notice continued", tags.items[1].tag.content);
    try std.testing.expectEqualStrings("param", tags.items[2].name);
    try std.testing.expectEqualStrings("value", tags.items[2].tag.parameter_name);
    try std.testing.expectEqualStrings("first line second line", tags.items[2].tag.content);
}
