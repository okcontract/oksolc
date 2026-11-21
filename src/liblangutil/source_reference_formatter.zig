// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Byte-for-byte diagnostic frame formatting translated from
//! `SourceReferenceFormatter.h/.cpp`.

const std = @import("std");
const Diagnostics = @import("diagnostics.zig");
const Extractor = @import("source_reference_extractor.zig");
const providers = @import("char_stream_provider.zig");
const ansi = @import("../libsolutil/ansi_colorized.zig");

const FormatError = std.mem.Allocator.Error || providers.ProviderError || error{
    InvalidSourceReference,
};

pub fn errorTextColor(severity: Diagnostics.Severity) []const u8 {
    return switch (severity) {
        .Error => ansi.formatting.red,
        .Warning => ansi.formatting.yellow,
        .Info => ansi.formatting.white,
    };
}

pub fn errorHighlightColor(severity: Diagnostics.Severity) []const u8 {
    return switch (severity) {
        .Error => ansi.formatting.red_background,
        .Warning => ansi.formatting.orange_background_256,
        .Info => ansi.formatting.gray_background,
    };
}

fn appendColorized(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    colored: bool,
    codes: []const []const u8,
    text: []const u8,
) !void {
    if (colored) for (codes) |code| try output.appendSlice(allocator, code);
    try output.appendSlice(allocator, text);
    if (colored) try output.appendSlice(allocator, ansi.formatting.reset);
}

fn appendRepeated(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    byte: u8,
    count: usize,
) !void {
    try output.ensureUnusedCapacity(allocator, count);
    for (0..count) |_| output.appendAssumeCapacity(byte);
}

fn replaceNonTabsAlloc(
    allocator: std.mem.Allocator,
    input: []const u8,
    filler: u8,
) ![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    for (input) |byte| {
        if ((byte & 0xc0) != 0x80) {
            try output.append(allocator, if (byte == '\t') '\t' else filler);
        }
    }
    return output.toOwnedSlice(allocator);
}

fn elideInvalidUtf8Alloc(
    allocator: std.mem.Allocator,
    text: []const u8,
    start: *usize,
    end: *usize,
) std.mem.Allocator.Error![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    var removed_before_start: usize = 0;
    var removed_before_end: usize = 0;
    var index: usize = 0;
    while (index < text.len) {
        const remaining = text[index..];
        const width = std.unicode.utf8ByteSequenceLength(remaining[0]) catch 0;
        if (width != 0 and width <= remaining.len and std.unicode.utf8ValidateSlice(remaining[0..width])) {
            try output.appendSlice(allocator, remaining[0..width]);
            index += width;
        } else {
            removed_before_start += @intFromBool(index < start.*);
            removed_before_end += @intFromBool(index < end.*);
            index += 1;
        }
    }
    const sanitized = try output.toOwnedSlice(allocator);
    // The caret uses offsets into the displayed excerpt.
    start.* -= removed_before_start;
    end.* -= removed_before_end;
    return sanitized;
}

fn appendSourceLocation(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    provider: providers.CharStreamProvider,
    reference: *const Extractor.SourceReference,
    colored: bool,
) FormatError!void {
    const frame_codes = &.{ ansi.formatting.bold, ansi.formatting.blue };
    const highlight_codes = &.{ansi.formatting.yellow};
    const diagnostic_codes = &.{ ansi.formatting.bold, ansi.formatting.yellow };
    if (reference.position.line < 0) {
        if (reference.source_name.len == 0) return;
        try appendColorized(output, allocator, colored, frame_codes, "-->");
        try output.append(allocator, ' ');
        try output.appendSlice(allocator, reference.source_name);
        try output.append(allocator, '\n');
        return;
    }

    const line_number = try allocator.print(
        "{d}",
        .{reference.position.line + 1},
    );
    defer allocator.free(line_number);
    try appendRepeated(output, allocator, ' ', line_number.len);
    try appendColorized(output, allocator, colored, frame_codes, "-->");
    try output.append(allocator, ' ');
    try output.appendSlice(allocator, reference.source_name);
    try output.append(allocator, ':');
    try output.appendSlice(allocator, line_number);
    try output.append(allocator, ':');
    const column = try allocator.print("{d}:\n", .{reference.position.column + 1});
    defer allocator.free(column);
    try output.appendSlice(allocator, column);

    const stream = try provider.charStream(reference.source_name);
    if (stream.isImportedFromAST()) return;
    var start = std.math.cast(usize, reference.start_column) orelse return error.InvalidSourceReference;
    var end = if (reference.multiline)
        reference.text.len
    else
        std.math.cast(usize, reference.end_column) orelse return error.InvalidSourceReference;
    if (start > end or end > reference.text.len) return error.InvalidSourceReference;
    const sanitized = if (std.unicode.utf8ValidateSlice(reference.text))
        null
    else
        try elideInvalidUtf8Alloc(allocator, reference.text, &start, &end);
    defer if (sanitized) |owned| allocator.free(owned);
    const text: []const u8 = sanitized orelse reference.text;

    try appendRepeated(output, allocator, ' ', line_number.len);
    try output.append(allocator, ' ');
    try appendColorized(output, allocator, colored, frame_codes, "|");
    try output.append(allocator, '\n');

    const numbered_frame = try allocator.print("{s} |", .{line_number});
    defer allocator.free(numbered_frame);
    try appendColorized(output, allocator, colored, frame_codes, numbered_frame);
    try output.append(allocator, ' ');
    try output.appendSlice(allocator, text[0..start]);
    if (!reference.multiline) {
        try appendColorized(
            output,
            allocator,
            colored,
            highlight_codes,
            text[start..end],
        );
        try output.appendSlice(allocator, text[end..]);
        try output.append(allocator, '\n');

        try appendRepeated(output, allocator, ' ', line_number.len);
        try output.append(allocator, ' ');
        try appendColorized(output, allocator, colored, frame_codes, "|");
        try output.append(allocator, ' ');
        const prefix = try replaceNonTabsAlloc(allocator, text[0..start], ' ');
        defer allocator.free(prefix);
        try output.appendSlice(allocator, prefix);
        const selected = text[start..end];
        if (selected.len == 0) {
            try appendColorized(output, allocator, colored, diagnostic_codes, "^");
        } else {
            const carets = try replaceNonTabsAlloc(allocator, selected, '^');
            defer allocator.free(carets);
            try appendColorized(output, allocator, colored, diagnostic_codes, carets);
        }
        try output.append(allocator, '\n');
    } else {
        try appendColorized(
            output,
            allocator,
            colored,
            highlight_codes,
            text[start..],
        );
        try output.append(allocator, '\n');
        try appendRepeated(output, allocator, ' ', line_number.len);
        try output.append(allocator, ' ');
        try appendColorized(output, allocator, colored, frame_codes, "|");
        try output.append(allocator, ' ');
        const prefix = try replaceNonTabsAlloc(allocator, text[0..start], ' ');
        defer allocator.free(prefix);
        try output.appendSlice(allocator, prefix);
        try appendColorized(
            output,
            allocator,
            colored,
            diagnostic_codes,
            "^ (Relevant source part starts here and spans across multiple lines).",
        );
        try output.append(allocator, '\n');
    }
}

fn appendPrimaryMessage(
    output: *std.ArrayList(u8),
    allocator: std.mem.Allocator,
    message: []const u8,
    type_or_severity: Diagnostics.TypeOrSeverity,
    error_id: ?Diagnostics.ErrorId,
    colored: bool,
    with_error_ids: bool,
) !void {
    const severity = Diagnostics.errorSeverityOrType(type_or_severity);
    const error_codes = &.{ ansi.formatting.bold, errorTextColor(severity) };
    try appendColorized(
        output,
        allocator,
        colored,
        error_codes,
        Diagnostics.formatTypeOrSeverity(type_or_severity),
    );
    if (with_error_ids) if (error_id) |id| {
        const formatted_id = try allocator.print(" ({d})", .{id.value});
        defer allocator.free(formatted_id);
        try appendColorized(output, allocator, colored, error_codes, formatted_id);
    };
    const full_message = try allocator.print(": {s}\n", .{message});
    defer allocator.free(full_message);
    try appendColorized(
        output,
        allocator,
        colored,
        &.{ ansi.formatting.bold, ansi.formatting.white },
        full_message,
    );
}

pub fn formatMessageAlloc(
    allocator: std.mem.Allocator,
    provider: providers.CharStreamProvider,
    message: *const Extractor.Message,
    colored: bool,
    with_error_ids: bool,
) FormatError![]u8 {
    var output: std.ArrayList(u8) = .empty;
    errdefer output.deinit(allocator);
    try appendPrimaryMessage(
        &output,
        allocator,
        message.primary.message,
        message.type_or_severity,
        message.error_id,
        colored,
        with_error_ids,
    );
    try appendSourceLocation(&output, allocator, provider, &message.primary, colored);
    for (message.secondary.items) |*secondary| {
        try appendColorized(
            &output,
            allocator,
            colored,
            &.{ ansi.formatting.bold, ansi.formatting.cyan },
            "Note",
        );
        const note = if (secondary.message.len == 0)
            try allocator.dupe(u8, ":")
        else
            try allocator.print(": {s}", .{secondary.message});
        defer allocator.free(note);
        try appendColorized(
            &output,
            allocator,
            colored,
            &.{ ansi.formatting.bold, ansi.formatting.white },
            note,
        );
        try output.append(allocator, '\n');
        try appendSourceLocation(&output, allocator, provider, secondary, colored);
    }
    try output.append(allocator, '\n');
    return output.toOwnedSlice(allocator);
}

pub fn formatDiagnosticAlloc(
    allocator: std.mem.Allocator,
    provider: providers.CharStreamProvider,
    diagnostic: *const Diagnostics.Diagnostic,
    colored: bool,
    with_error_ids: bool,
) (FormatError || Extractor.ExtractError)![]u8 {
    var message = try Extractor.extractDiagnostic(
        allocator,
        provider,
        diagnostic,
        .{ .severity = diagnostic.severity() },
    );
    defer message.deinit();
    return formatMessageAlloc(allocator, provider, &message, colored, with_error_ids);
}

/// Formats a diagnostic using its concrete error type rather than its
/// severity. `StandardCompiler::formatErrorWithException` uses this form, so
/// a parser diagnostic begins with `ParserError:` rather than `Error:`.
pub fn formatTypedDiagnosticAlloc(
    allocator: std.mem.Allocator,
    provider: providers.CharStreamProvider,
    diagnostic: *const Diagnostics.Diagnostic,
    colored: bool,
    with_error_ids: bool,
) (FormatError || Extractor.ExtractError)![]u8 {
    var message = try Extractor.extractDiagnostic(
        allocator,
        provider,
        diagnostic,
        .{ .error_type = diagnostic.error_type },
    );
    defer message.deinit();
    return formatMessageAlloc(allocator, provider, &message, colored, with_error_ids);
}

test "diagnostic formatter emits the upstream source frame layout" {
    const CharStream = @import("char_stream.zig").CharStream;
    const source = "contract C {\n\tfunction f() {}\n}\n";
    const stream = CharStream.initBorrowed(source, "a.sol");
    const singleton = providers.SingletonCharStreamProvider.init(&stream);
    const provider = singleton.provider();
    var diagnostic = try Diagnostics.Diagnostic.init(
        std.testing.allocator,
        .{ .value = 1234 },
        .ParserError,
        "expected token",
        .{ .start = 14, .end = 22, .source_name = "a.sol" },
        null,
    );
    defer diagnostic.deinit();
    const formatted = try formatDiagnosticAlloc(
        std.testing.allocator,
        provider,
        &diagnostic,
        false,
        true,
    );
    defer std.testing.allocator.free(formatted);
    try std.testing.expect(std.mem.startsWith(u8, formatted, "Error (1234): expected token\n"));
    try std.testing.expect(std.mem.find(u8, formatted, "--> a.sol:2:2:") != null);
    try std.testing.expect(std.mem.findScalar(u8, formatted, '^') != null);
}

test "diagnostic frames elide malformed UTF-8 and keep the highlight aligned" {
    const allocator = std.testing.allocator;
    const prefix = "\tp\xffé ";
    const suffix = "\xff;\n";
    const cases = .{
        .{ .span = "\xe2\x82word\x80", .visible = "word", .carets = "^^^^" },
        .{ .span = "\x80\xff", .visible = "", .carets = "^" },
    };
    inline for (cases) |case| {
        const stream = @import("char_stream.zig").CharStream.initBorrowed(prefix ++ case.span ++ suffix, "a.sol");
        const singleton = providers.SingletonCharStreamProvider.init(&stream);
        var diagnostic = try Diagnostics.Diagnostic.init(
            allocator,
            .{ .value = 8452 },
            .SyntaxError,
            "invalid UTF-8",
            .{ .start = prefix.len, .end = prefix.len + case.span.len, .source_name = "a.sol" },
            null,
        );
        defer diagnostic.deinit();
        const formatted = try formatTypedDiagnosticAlloc(allocator, singleton.provider(), &diagnostic, false, false);
        defer allocator.free(formatted);
        try std.testing.expectEqualStrings(
            "SyntaxError: invalid UTF-8\n" ++
                " --> a.sol:1:7:\n" ++
                "  |\n" ++
                "1 | \tpé " ++ case.visible ++ ";\n" ++
                "  | \t   " ++ case.carets ++ "\n\n",
            formatted,
        );
    }
}

test "multiline diagnostic frames ignore closing-line indentation" {
    const CharStream = @import("char_stream.zig").CharStream;
    for ([_][]const u8{ "    {\n}\n", "    {\n        }\n" }) |source| {
        const stream = CharStream.initBorrowed(source, "a.sol");
        const singleton = providers.SingletonCharStreamProvider.init(&stream);
        var diagnostic = try Diagnostics.Diagnostic.init(
            std.testing.allocator,
            .{ .value = 5740 },
            .Warning,
            "Unreachable code.",
            .{ .start = 4, .end = @intCast(source.len - 1), .source_name = "a.sol" },
            null,
        );
        defer diagnostic.deinit();
        const formatted = try formatDiagnosticAlloc(
            std.testing.allocator,
            singleton.provider(),
            &diagnostic,
            false,
            false,
        );
        defer std.testing.allocator.free(formatted);
        try std.testing.expectEqualStrings(
            "Warning: Unreachable code.\n" ++
                " --> a.sol:1:5:\n" ++
                "  |\n" ++
                "1 |     {\n" ++
                "  |     ^ (Relevant source part starts here and spans across multiple lines).\n\n",
            formatted,
        );
    }
}
