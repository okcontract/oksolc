// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Source-window extraction for diagnostics and exception payloads.

const std = @import("std");
const locations = @import("source_location.zig");
const Diagnostics = @import("diagnostics.zig");
const providers = @import("char_stream_provider.zig");
const UtilExceptions = @import("../libsolutil/exceptions.zig");

pub const ExtractError = std.mem.Allocator.Error || providers.ProviderError || error{
    InvalidSourceLocation,
};

pub const SourceReference = struct {
    allocator: std.mem.Allocator,
    message: []u8,
    source_name: []u8,
    position: locations.LineColumn = .{},
    multiline: bool = false,
    text: []u8,
    start_column: i32 = -1,
    end_column: i32 = -1,

    pub fn messageOnly(
        allocator: std.mem.Allocator,
        message: []const u8,
        source_name: []const u8,
    ) !SourceReference {
        const owned_message = try allocator.dupe(u8, message);
        errdefer allocator.free(owned_message);
        const owned_source = try allocator.dupe(u8, source_name);
        errdefer allocator.free(owned_source);
        const text = try allocator.alloc(u8, 0);
        return .{
            .allocator = allocator,
            .message = owned_message,
            .source_name = owned_source,
            .text = text,
        };
    }

    pub fn deinit(self: *SourceReference) void {
        self.allocator.free(self.message);
        self.allocator.free(self.source_name);
        self.allocator.free(self.text);
        self.* = undefined;
    }
};

pub const Message = struct {
    allocator: std.mem.Allocator,
    primary: SourceReference,
    type_or_severity: Diagnostics.TypeOrSeverity,
    secondary: std.ArrayList(SourceReference) = .empty,
    error_id: ?Diagnostics.ErrorId = null,

    pub fn deinit(self: *Message) void {
        self.primary.deinit();
        for (self.secondary.items) |*reference| reference.deinit();
        self.secondary.deinit(self.allocator);
        self.* = undefined;
    }
};

pub fn extractReference(
    allocator: std.mem.Allocator,
    provider: providers.CharStreamProvider,
    location_optional: ?*const locations.SourceLocation,
    message: []const u8,
) ExtractError!SourceReference {
    const location = location_optional orelse
        return SourceReference.messageOnly(allocator, message, "");
    const source_name = location.source_name orelse
        return SourceReference.messageOnly(allocator, message, "");
    if (!location.hasText()) {
        return SourceReference.messageOnly(allocator, message, source_name);
    }

    const stream = try provider.charStream(source_name);
    const interest = stream.translatePositionToLineColumn(location.start);
    var start = interest;
    var end = stream.translatePositionToLineColumn(location.end);
    const is_multiline = start.line != end.line;
    var line = try stream.lineAtPositionAlloc(allocator, location.start);
    errdefer allocator.free(line);

    if (start.column < 0 or end.column < 0) return error.InvalidSourceLocation;
    var location_length: i32 = if (is_multiline)
        @as(i32, @intCast(line.len)) - start.column
    else
        end.column - start.column;
    if (location_length < 0) return error.InvalidSourceLocation;

    if (location_length > 150) {
        const left_end: usize = @intCast(start.column + 35);
        const source_end: usize = if (is_multiline) line.len else @intCast(end.column);
        if (left_end > line.len or source_end < 35 or source_end - 35 > line.len) {
            return error.InvalidSourceLocation;
        }
        const right_start = source_end - 35;
        const replacement = try std.fmt.allocPrint(
            allocator,
            "{s} ... {s}",
            .{ line[0..left_end], line[right_start..] },
        );
        allocator.free(line);
        line = replacement;
        end.column = start.column + 75;
        location_length = 75;
    }

    if (line.len > 150) {
        const line_length: i32 = @intCast(line.len);
        const slice_start_i32 = @max(0, start.column - 35);
        const slice_length_i32 = @min(start.column, 35) +
            @min(location_length + 35, line_length - start.column);
        if (slice_length_i32 < 0) return error.InvalidSourceLocation;
        const slice_start: usize = @intCast(slice_start_i32);
        const slice_length: usize = @intCast(slice_length_i32);
        if (slice_start > line.len or slice_length > line.len - slice_start) {
            return error.InvalidSourceLocation;
        }
        var replacement: std.ArrayList(u8) = .empty;
        errdefer replacement.deinit(allocator);
        try replacement.appendSlice(allocator, line[slice_start..][0..slice_length]);
        if (start.column + location_length + 35 < line_length) {
            try replacement.appendSlice(allocator, " ...");
        }
        if (start.column > 35) {
            try replacement.insertSlice(allocator, 0, " ... ");
            start.column = 40;
        }
        allocator.free(line);
        line = try replacement.toOwnedSlice(allocator);
        end.column = start.column + location_length;
    }

    const owned_message = try allocator.dupe(u8, message);
    errdefer allocator.free(owned_message);
    const owned_source = try allocator.dupe(u8, source_name);
    return .{
        .allocator = allocator,
        .message = owned_message,
        .source_name = owned_source,
        .position = interest,
        .multiline = is_multiline,
        .text = line,
        .start_column = @min(start.column, @as(i32, @intCast(line.len))),
        .end_column = @min(end.column, @as(i32, @intCast(line.len))),
    };
}

pub fn extractDiagnostic(
    allocator: std.mem.Allocator,
    provider: providers.CharStreamProvider,
    diagnostic: *const Diagnostics.Diagnostic,
    type_or_severity: Diagnostics.TypeOrSeverity,
) ExtractError!Message {
    const location_pointer: ?*const locations.SourceLocation = if (diagnostic.location) |*location|
        location
    else
        null;
    var primary = try extractReference(
        allocator,
        provider,
        location_pointer,
        diagnostic.description,
    );
    errdefer primary.deinit();
    var result: Message = .{
        .allocator = allocator,
        .primary = primary,
        .type_or_severity = type_or_severity,
        .error_id = diagnostic.error_id,
    };
    errdefer result.deinit();
    for (diagnostic.secondary.infos.items) |*info| {
        var reference = try extractReference(allocator, provider, &info.location, info.message);
        errdefer reference.deinit();
        try result.secondary.append(allocator, reference);
    }
    return result;
}

pub fn extractException(
    allocator: std.mem.Allocator,
    provider: providers.CharStreamProvider,
    exception: *const UtilExceptions.Exception,
    type_or_severity: Diagnostics.TypeOrSeverity,
) ExtractError!Message {
    const location = exception.source_location;
    const location_pointer: ?*const locations.SourceLocation = if (location.isValid()) &location else null;
    return .{
        .allocator = allocator,
        .primary = try extractReference(
            allocator,
            provider,
            location_pointer,
            exception.comment() orelse "",
        ),
        .type_or_severity = type_or_severity,
    };
}

test "source extraction truncates long context while preserving highlight" {
    const source = "prefix prefix prefix prefix prefix prefix " ++
        "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789" ++
        " suffix suffix suffix suffix suffix suffix suffix suffix suffix suffix suffix";
    const stream = @import("char_stream.zig").CharStream.initBorrowed(source, "a.sol");
    const singleton = providers.SingletonCharStreamProvider.init(&stream);
    const provider = singleton.provider();
    const location: locations.SourceLocation = .{
        .start = 40,
        .end = 102,
        .source_name = "a.sol",
    };
    var reference = try extractReference(
        std.testing.allocator,
        provider,
        &location,
        "message",
    );
    defer reference.deinit();
    try std.testing.expect(reference.text.len <= 155);
    try std.testing.expect(reference.start_column >= 0);
    try std.testing.expect(reference.end_column >= reference.start_column);
}
