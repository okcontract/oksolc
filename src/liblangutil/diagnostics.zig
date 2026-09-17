// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Owned Zig representation of the diagnostic contracts in
//! `Exceptions.h/.cpp`, `ErrorReporter.h/.cpp`, and
//! `UniqueErrorReporter.h`.

const std = @import("std");
const source_location = @import("source_location.zig");

pub const SourceLocation = source_location.SourceLocation;

pub const ErrorId = struct {
    value: u64 = 0,

    pub fn eql(self: ErrorId, other: ErrorId) bool {
        return self.value == other.value;
    }

    pub fn lessThan(self: ErrorId, other: ErrorId) bool {
        return self.value < other.value;
    }
};

pub const ErrorType = enum(c_int) {
    Info,
    Warning,
    CodeGenerationError,
    DeclarationError,
    DocstringParsingError,
    ParserError,
    TypeError,
    SyntaxError,
    IOError,
    FatalError,
    JSONError,
    InternalCompilerError,
    CompilerError,
    Exception,
    UnimplementedFeatureError,
    YulException,
    SMTLogicException,
};

pub const Severity = enum(c_int) {
    Info,
    Warning,
    Error,
};

pub const TypeOrSeverity = union(enum) {
    error_type: ErrorType,
    severity: Severity,
};

pub fn errorSeverity(error_type: ErrorType) Severity {
    return switch (error_type) {
        .Info => .Info,
        .Warning => .Warning,
        else => .Error,
    };
}

pub fn errorSeverityOrType(value: TypeOrSeverity) Severity {
    return switch (value) {
        .error_type => |error_type| errorSeverity(error_type),
        .severity => |severity| severity,
    };
}

pub fn isErrorSeverity(severity: Severity) bool {
    return severity == .Error;
}

pub fn isErrorType(error_type: ErrorType) bool {
    return isErrorSeverity(errorSeverity(error_type));
}

pub fn formatErrorSeverity(severity: Severity) []const u8 {
    return switch (severity) {
        .Info => "Info",
        .Warning => "Warning",
        .Error => "Error",
    };
}

pub fn formatErrorSeverityLowercase(severity: Severity) []const u8 {
    return switch (severity) {
        .Info => "info",
        .Warning => "warning",
        .Error => "error",
    };
}

pub fn formatErrorType(error_type: ErrorType) []const u8 {
    return @tagName(error_type);
}

pub fn parseErrorType(name: []const u8) ?ErrorType {
    inline for (std.meta.fields(ErrorType)) |field| {
        if (std.mem.eql(u8, name, field.name)) return @enumFromInt(field.value);
    }
    return null;
}

pub fn formatTypeOrSeverity(value: TypeOrSeverity) []const u8 {
    return switch (value) {
        .error_type => |error_type| formatErrorType(error_type),
        .severity => |severity| formatErrorSeverity(severity),
    };
}

pub const SecondaryInfo = struct {
    message: []u8,
    location: SourceLocation,

    fn clone(
        self: SecondaryInfo,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!SecondaryInfo {
        return .{
            .message = try allocator.dupe(u8, self.message),
            .location = self.location,
        };
    }

    fn deinit(self: *SecondaryInfo, allocator: std.mem.Allocator) void {
        allocator.free(self.message);
        self.* = undefined;
    }
};

pub const SecondarySourceLocation = struct {
    infos: std.ArrayList(SecondaryInfo) = .empty,

    pub fn deinit(
        self: *SecondarySourceLocation,
        allocator: std.mem.Allocator,
    ) void {
        for (self.infos.items) |*info| info.deinit(allocator);
        self.infos.deinit(allocator);
        self.* = undefined;
    }

    pub fn append(
        self: *SecondarySourceLocation,
        allocator: std.mem.Allocator,
        message: []const u8,
        location: SourceLocation,
    ) std.mem.Allocator.Error!void {
        const owned_message = try allocator.dupe(u8, message);
        errdefer allocator.free(owned_message);
        try self.infos.append(allocator, .{
            .message = owned_message,
            .location = location,
        });
    }

    pub fn appendClone(
        self: *SecondarySourceLocation,
        allocator: std.mem.Allocator,
        other: *const SecondarySourceLocation,
    ) std.mem.Allocator.Error!void {
        const initial_len = self.infos.items.len;
        errdefer {
            for (self.infos.items[initial_len..]) |*info| info.deinit(allocator);
            self.infos.shrinkRetainingCapacity(initial_len);
        }
        for (other.infos.items) |info| {
            var cloned = try info.clone(allocator);
            errdefer cloned.deinit(allocator);
            try self.infos.append(allocator, cloned);
        }
    }

    pub fn clone(
        self: *const SecondarySourceLocation,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!SecondarySourceLocation {
        var result: SecondarySourceLocation = .{};
        errdefer result.deinit(allocator);
        try result.appendClone(allocator, self);
        return result;
    }

    /// Truncates to 32 entries and atomically replaces an allocator-owned
    /// message with the upstream truncation notice.
    pub fn limitSize(
        self: *SecondarySourceLocation,
        allocator: std.mem.Allocator,
        message: *[]u8,
    ) std.mem.Allocator.Error!void {
        const occurrences = self.infos.items.len;
        if (occurrences <= 32) return;
        const replacement = try std.fmt.allocPrint(
            allocator,
            "{s} Truncated from {d} to the first 32 occurrences.",
            .{ message.*, occurrences },
        );
        allocator.free(message.*);
        message.* = replacement;
        for (self.infos.items[32..]) |*info| info.deinit(allocator);
        self.infos.shrinkRetainingCapacity(32);
    }
};

pub const Diagnostic = struct {
    allocator: std.mem.Allocator,
    error_id: ErrorId,
    error_type: ErrorType,
    description: []u8,
    location: ?SourceLocation,
    secondary: SecondarySourceLocation,

    pub fn init(
        allocator: std.mem.Allocator,
        error_id: ErrorId,
        error_type: ErrorType,
        description: []const u8,
        location: SourceLocation,
        secondary: ?*const SecondarySourceLocation,
    ) std.mem.Allocator.Error!Diagnostic {
        const owned_description = try allocator.dupe(u8, description);
        errdefer allocator.free(owned_description);
        var owned_secondary: SecondarySourceLocation = if (secondary) |value|
            try value.clone(allocator)
        else
            .{};
        errdefer owned_secondary.deinit(allocator);
        return .{
            .allocator = allocator,
            .error_id = error_id,
            .error_type = error_type,
            .description = owned_description,
            .location = if (location.isValid()) location else null,
            .secondary = owned_secondary,
        };
    }

    pub fn deinit(self: *Diagnostic) void {
        self.allocator.free(self.description);
        self.secondary.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn clone(
        self: *const Diagnostic,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!Diagnostic {
        return init(
            allocator,
            self.error_id,
            self.error_type,
            self.description,
            self.location orelse .{},
            &self.secondary,
        );
    }

    pub fn severity(self: *const Diagnostic) Severity {
        return errorSeverity(self.error_type);
    }
};

pub fn containsErrorOfType(
    diagnostics: []const Diagnostic,
    error_type: ErrorType,
) ?*const Diagnostic {
    for (diagnostics) |*diagnostic| {
        if (diagnostic.error_type == error_type) return diagnostic;
    }
    return null;
}

pub fn containsErrors(diagnostics: []const Diagnostic) bool {
    for (diagnostics) |diagnostic| {
        if (isErrorType(diagnostic.error_type)) return true;
    }
    return false;
}

pub const ReportError = std.mem.Allocator.Error || error{FatalDiagnostic};

pub const ErrorReporter = struct {
    allocator: std.mem.Allocator,
    diagnostic_list: std.ArrayList(Diagnostic) = .empty,
    error_count: u32 = 0,
    warning_count: u32 = 0,
    info_count: u32 = 0,

    pub const max_warnings_allowed: u32 = 256;
    pub const max_errors_allowed: u32 = 256;
    pub const max_infos_allowed: u32 = 256;

    pub fn init(allocator: std.mem.Allocator) ErrorReporter {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *ErrorReporter) void {
        for (self.diagnostic_list.items) |*diagnostic| diagnostic.deinit();
        self.diagnostic_list.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn append(
        self: *ErrorReporter,
        incoming_diagnostics: []const Diagnostic,
    ) std.mem.Allocator.Error!void {
        const initial_len = self.diagnostic_list.items.len;
        errdefer {
            for (self.diagnostic_list.items[initial_len..]) |*diagnostic| diagnostic.deinit();
            self.diagnostic_list.shrinkRetainingCapacity(initial_len);
        }
        for (incoming_diagnostics) |*diagnostic| {
            var cloned = try diagnostic.clone(self.allocator);
            errdefer cloned.deinit();
            try self.diagnostic_list.append(self.allocator, cloned);
        }
    }

    pub fn diagnostics(self: *const ErrorReporter) []const Diagnostic {
        return self.diagnostic_list.items;
    }

    /// Releases stored diagnostic values but intentionally preserves counters,
    /// matching the upstream `clear()` behavior.
    pub fn clear(self: *ErrorReporter) void {
        for (self.diagnostic_list.items) |*diagnostic| diagnostic.deinit();
        self.diagnostic_list.clearRetainingCapacity();
    }

    pub fn hasErrors(self: *const ErrorReporter) bool {
        return self.error_count > 0;
    }

    pub fn hasErrorsWarningsOrInfos(self: *const ErrorReporter) bool {
        return self.error_count + self.warning_count + self.info_count > 0;
    }

    pub fn errorCount(self: *const ErrorReporter) u32 {
        return self.error_count;
    }

    pub fn warningCount(self: *const ErrorReporter) u32 {
        return self.warning_count;
    }

    pub fn infoCount(self: *const ErrorReporter) u32 {
        return self.info_count;
    }

    pub fn hasExcessiveErrors(self: *const ErrorReporter) bool {
        return self.error_count > max_errors_allowed;
    }

    pub fn hasError(self: *const ErrorReporter, error_id: ErrorId) bool {
        for (self.diagnostic_list.items) |diagnostic| {
            if (diagnostic.error_id.eql(error_id)) return true;
        }
        return false;
    }

    pub fn report(
        self: *ErrorReporter,
        error_id: ErrorId,
        error_type: ErrorType,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        return self.reportWithSecondary(
            error_id,
            error_type,
            location,
            null,
            description,
        );
    }

    pub fn reportWithSecondary(
        self: *ErrorReporter,
        error_id: ErrorId,
        error_type: ErrorType,
        location: SourceLocation,
        secondary: ?*const SecondarySourceLocation,
        description: []const u8,
    ) ReportError!void {
        if (try self.checkForExcessiveErrors(error_type)) return;
        try self.appendOne(error_id, error_type, location, secondary, description);
    }

    pub fn warning(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .Warning, location, description);
    }

    /// Stores a caller-provided truncation summary while warning capacity
    /// remains, including in the final slot where `warning` would substitute
    /// the generic limit sentinel. Returns false once the limit is exhausted.
    pub fn warningSummary(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) std.mem.Allocator.Error!bool {
        if (self.warning_count >= max_warnings_allowed) return false;
        try self.appendOne(error_id, .Warning, location, null, description);
        self.warning_count += 1;
        return true;
    }

    pub fn warningWithSecondary(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
        secondary: *const SecondarySourceLocation,
    ) ReportError!void {
        try self.reportWithSecondary(error_id, .Warning, location, secondary, description);
    }

    pub fn info(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .Info, location, description);
    }

    pub fn declarationError(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .DeclarationError, location, description);
    }

    pub fn parserError(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .ParserError, location, description);
    }

    pub fn syntaxError(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .SyntaxError, location, description);
    }

    pub fn typeError(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .TypeError, location, description);
    }

    pub fn docstringParsingError(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .DocstringParsingError, location, description);
    }

    pub fn unimplementedFeatureError(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .UnimplementedFeatureError, location, description);
    }

    pub fn codeGenerationError(
        self: *ErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.report(error_id, .CodeGenerationError, location, description);
    }

    pub fn fatal(
        self: *ErrorReporter,
        error_id: ErrorId,
        error_type: ErrorType,
        location: SourceLocation,
        secondary: ?*const SecondarySourceLocation,
        description: []const u8,
    ) ReportError!void {
        try self.reportWithSecondary(error_id, error_type, location, secondary, description);
        return error.FatalDiagnostic;
    }

    pub fn errorWatcher(self: *const ErrorReporter) ErrorWatcher {
        return .{
            .reporter = self,
            .initial_error_count = self.error_count,
        };
    }

    fn appendOne(
        self: *ErrorReporter,
        error_id: ErrorId,
        error_type: ErrorType,
        location: SourceLocation,
        secondary: ?*const SecondarySourceLocation,
        description: []const u8,
    ) std.mem.Allocator.Error!void {
        var diagnostic = try Diagnostic.init(
            self.allocator,
            error_id,
            error_type,
            description,
            location,
            secondary,
        );
        errdefer diagnostic.deinit();
        try self.diagnostic_list.append(self.allocator, diagnostic);
    }

    fn checkForExcessiveErrors(
        self: *ErrorReporter,
        error_type: ErrorType,
    ) ReportError!bool {
        if (error_type == .Warning) {
            self.warning_count += 1;
            if (self.warning_count == max_warnings_allowed) {
                try self.appendOne(
                    .{ .value = 4591 },
                    .Warning,
                    .{},
                    null,
                    "There are more than 256 warnings. Ignoring the rest.",
                );
            }
            return self.warning_count >= max_warnings_allowed;
        }
        if (error_type == .Info) {
            self.info_count += 1;
            if (self.info_count == max_infos_allowed) {
                try self.appendOne(
                    .{ .value = 2833 },
                    .Info,
                    .{},
                    null,
                    "There are more than 256 infos. Ignoring the rest.",
                );
            }
            return self.info_count >= max_infos_allowed;
        }

        self.error_count += 1;
        if (self.error_count > max_errors_allowed) {
            try self.appendOne(
                .{ .value = 4013 },
                .Warning,
                .{},
                null,
                "There are more than 256 errors. Aborting.",
            );
            return error.FatalDiagnostic;
        }
        return false;
    }
};

pub const ErrorWatcher = struct {
    reporter: *const ErrorReporter,
    initial_error_count: u32,

    pub fn ok(self: ErrorWatcher) bool {
        std.debug.assert(self.initial_error_count <= self.reporter.error_count);
        return self.initial_error_count == self.reporter.error_count;
    }
};

const SeenDiagnostic = struct {
    error_id: ErrorId,
    location: SourceLocation,
    description: []u8,

    fn deinit(self: *SeenDiagnostic, allocator: std.mem.Allocator) void {
        allocator.free(self.description);
        self.* = undefined;
    }
};

pub const UniqueReportError = ReportError || error{ConflictingDuplicateDescription};

pub const UniqueErrorReporter = struct {
    allocator: std.mem.Allocator,
    reporter: ErrorReporter,
    seen_diagnostics: std.ArrayList(SeenDiagnostic) = .empty,

    pub fn init(allocator: std.mem.Allocator) UniqueErrorReporter {
        return .{
            .allocator = allocator,
            .reporter = ErrorReporter.init(allocator),
        };
    }

    pub fn deinit(self: *UniqueErrorReporter) void {
        self.reporter.deinit();
        for (self.seen_diagnostics.items) |*entry| entry.deinit(self.allocator);
        self.seen_diagnostics.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn append(
        self: *UniqueErrorReporter,
        other: *const UniqueErrorReporter,
    ) std.mem.Allocator.Error!void {
        try self.reporter.append(other.reporter.diagnostics());
    }

    pub fn warning(
        self: *UniqueErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) UniqueReportError!void {
        if (try self.seen(error_id, location, description)) return;
        try self.reporter.warning(error_id, location, description);
        try self.markAsSeen(error_id, location, description);
    }

    pub fn info(
        self: *UniqueErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) UniqueReportError!void {
        if (try self.seen(error_id, location, description)) return;
        try self.reporter.info(error_id, location, description);
        try self.markAsSeen(error_id, location, description);
    }

    pub fn seen(
        self: *const UniqueErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) error{ConflictingDuplicateDescription}!bool {
        for (self.seen_diagnostics.items) |entry| {
            if (entry.error_id.eql(error_id) and entry.location.eql(location)) {
                if (!std.mem.eql(u8, entry.description, description)) {
                    return error.ConflictingDuplicateDescription;
                }
                return true;
            }
        }
        return false;
    }

    pub fn markAsSeen(
        self: *UniqueErrorReporter,
        error_id: ErrorId,
        location: SourceLocation,
        description: []const u8,
    ) std.mem.Allocator.Error!void {
        if (location.eql(.{})) return;
        const owned_description = try self.allocator.dupe(u8, description);
        errdefer self.allocator.free(owned_description);
        try self.seen_diagnostics.append(self.allocator, .{
            .error_id = error_id,
            .location = location,
            .description = owned_description,
        });
    }

    pub fn diagnostics(self: *const UniqueErrorReporter) []const Diagnostic {
        return self.reporter.diagnostics();
    }

    /// Like upstream, clearing emitted diagnostics does not clear the dedupe
    /// history.
    pub fn clear(self: *UniqueErrorReporter) void {
        self.reporter.clear();
    }
};

test "diagnostics preserve insertion order, ownership, and severities" {
    var reporter = ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    const location: SourceLocation = .{
        .start = 1,
        .end = 4,
        .source_name = "a.sol",
    };
    const watcher = reporter.errorWatcher();
    try reporter.warning(.{ .value = 100 }, location, "first");
    try std.testing.expect(watcher.ok());
    try reporter.parserError(.{ .value = 200 }, location, "second");
    try std.testing.expect(!watcher.ok());
    try std.testing.expectEqual(@as(usize, 2), reporter.diagnostics().len);
    try std.testing.expectEqualStrings("first", reporter.diagnostics()[0].description);
    try std.testing.expectEqualStrings("second", reporter.diagnostics()[1].description);
    try std.testing.expectEqual(Severity.Warning, reporter.diagnostics()[0].severity());
    try std.testing.expectEqual(Severity.Error, reporter.diagnostics()[1].severity());
    try std.testing.expectEqual(@as(u32, 1), reporter.warningCount());
    try std.testing.expectEqual(@as(u32, 0), reporter.infoCount());
}

test "warning limit sentinel occupies the 256th ordered slot" {
    var reporter = ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    for (0..300) |index| {
        try reporter.warning(.{ .value = @intCast(index) }, .{}, "warning");
    }
    try std.testing.expectEqual(@as(usize, 256), reporter.diagnostics().len);
    try std.testing.expectEqual(@as(u64, 4591), reporter.diagnostics()[255].error_id.value);
}

test "caller summary can occupy the final warning slot" {
    var reporter = ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    for (0..ErrorReporter.max_warnings_allowed - 1) |index|
        try reporter.warning(.{ .value = @intCast(index) }, .{}, "warning");

    try std.testing.expectEqual(@as(u32, 255), reporter.warningCount());
    try std.testing.expect(try reporter.warningSummary(
        .{ .value = 65_012 },
        .{},
        "analysis diagnostics omitted",
    ));
    try std.testing.expectEqual(
        ErrorReporter.max_warnings_allowed,
        reporter.warningCount(),
    );
    try std.testing.expectEqual(@as(usize, 256), reporter.diagnostics().len);
    try std.testing.expectEqual(
        @as(u64, 65_012),
        reporter.diagnostics()[255].error_id.value,
    );
    try std.testing.expect(!(try reporter.warningSummary(
        .{ .value = 65_013 },
        .{},
        "second summary",
    )));
}

fn diagnosticAllocationFailure(allocator: std.mem.Allocator) !void {
    var secondary: SecondarySourceLocation = .{};
    defer secondary.deinit(allocator);
    try secondary.append(allocator, "other declaration", .{
        .start = 1,
        .end = 2,
        .source_name = "a.sol",
    });
    var reporter = ErrorReporter.init(allocator);
    defer reporter.deinit();
    try reporter.reportWithSecondary(
        .{ .value = 1234 },
        .TypeError,
        .{ .start = 3, .end = 4, .source_name = "a.sol" },
        &secondary,
        "type mismatch",
    );
    _ = try reporter.warningSummary(
        .{ .value = 65_012 },
        .{},
        "analysis diagnostics omitted",
    );
}

test "diagnostic construction releases every partial allocation" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        diagnosticAllocationFailure,
        .{},
    );
}
