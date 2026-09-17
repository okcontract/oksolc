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

    const line_number = try std.fmt.allocPrint(
        allocator,
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
    const column = try std.fmt.allocPrint(allocator, "{d}:\n", .{reference.position.column + 1});
    defer allocator.free(column);
    try output.appendSlice(allocator, column);

    const stream = try provider.charStream(reference.source_name);
    if (stream.isImportedFromAST()) return;
    if (reference.start_column < 0 or reference.end_column < reference.start_column or
        @as(usize, @intCast(reference.end_column)) > reference.text.len)
    {
        return error.InvalidSourceReference;
    }
    const start: usize = @intCast(reference.start_column);
    const end: usize = @intCast(reference.end_column);

    try appendRepeated(output, allocator, ' ', line_number.len);
    try output.append(allocator, ' ');
    try appendColorized(output, allocator, colored, frame_codes, "|");
    try output.append(allocator, '\n');

    const numbered_frame = try std.fmt.allocPrint(allocator, "{s} |", .{line_number});
    defer allocator.free(numbered_frame);
    try appendColorized(output, allocator, colored, frame_codes, numbered_frame);
    try output.append(allocator, ' ');
    try output.appendSlice(allocator, reference.text[0..start]);
    if (!reference.multiline) {
        try appendColorized(
            output,
            allocator,
            colored,
            highlight_codes,
            reference.text[start..end],
        );
        try output.appendSlice(allocator, reference.text[end..]);
        try output.append(allocator, '\n');

        try appendRepeated(output, allocator, ' ', line_number.len);
        try output.append(allocator, ' ');
        try appendColorized(output, allocator, colored, frame_codes, "|");
        try output.append(allocator, ' ');
        const prefix = try replaceNonTabsAlloc(allocator, reference.text[0..start], ' ');
        defer allocator.free(prefix);
        try output.appendSlice(allocator, prefix);
        const selected = reference.text[start..end];
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
            reference.text[start..],
        );
        try output.append(allocator, '\n');
        try appendRepeated(output, allocator, ' ', line_number.len);
        try output.append(allocator, ' ');
        try appendColorized(output, allocator, colored, frame_codes, "|");
        try output.append(allocator, ' ');
        const prefix = try replaceNonTabsAlloc(allocator, reference.text[0..start], ' ');
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
        const formatted_id = try std.fmt.allocPrint(allocator, " ({d})", .{id.value});
        defer allocator.free(formatted_id);
        try appendColorized(output, allocator, colored, error_codes, formatted_id);
    };
    const full_message = try std.fmt.allocPrint(allocator, ": {s}\n", .{message});
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
            try std.fmt.allocPrint(allocator, ": {s}", .{secondary.message});
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
