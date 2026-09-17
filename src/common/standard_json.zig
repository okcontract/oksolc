// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");
const execution = @import("execution.zig");

pub const SourceReadError = error{
    OutOfMemory,
    InvalidPath,
    InternalFailure,
};

/// An owned response from a Standard JSON source callback.
pub const SourceReadResult = union(enum) {
    contents: []u8,
    failure: []u8,
    unsupported: void,

    pub fn deinit(self: SourceReadResult, allocator: std.mem.Allocator) void {
        switch (self) {
            .contents => |bytes| allocator.free(bytes),
            .failure => |bytes| allocator.free(bytes),
            .unsupported => {},
        }
    }
};

/// Type-erased source loader corresponding to libsolc's read callback.
/// A stateful compiler may retain internal revision locks while invoking a
/// loader. Consult that compiler's API before making reentrant calls.
pub const SourceLoader = struct {
    context: ?*anyopaque,
    read_fn: *const fn (
        context: ?*anyopaque,
        allocator: std.mem.Allocator,
        kind: []const u8,
        data: []const u8,
    ) SourceReadError!SourceReadResult,

    pub fn read(
        self: SourceLoader,
        allocator: std.mem.Allocator,
        kind: []const u8,
        data: []const u8,
    ) SourceReadError!SourceReadResult {
        return self.read_fn(self.context, allocator, kind, data);
    }
};

/// Observable stages of one Standard JSON compilation. Sources and contracts
/// use real item counts; stages without a reliable denominator remain
/// indeterminate rather than reporting guessed percentages.
pub const ProgressStage = enum {
    parsing_sources,
    analyzing_sources,
    generating_contracts,
    compiling_yul,
    writing_output,
};

/// A borrowed, allocation-free progress update. `item_name` remains valid only
/// for the duration of the callback.
pub const ProgressUpdate = struct {
    stage: ProgressStage,
    completed_items: usize = 0,
    estimated_total_items: usize = 0,
    item_name: []const u8 = "",
};

/// Type-erased progress sink for frontends such as the CLI. Compiler behavior
/// and output do not depend on whether a reporter is present.
pub const ProgressReporter = struct {
    /// Callbacks may run on compiler worker threads when parallel compilation is
    /// enabled. Calls are serialized for a compilation, but consumers must be
    /// thread-safe and must not require invocation from the initiating thread.
    /// A stateful compiler may retain revision locks while reporting progress;
    /// consult that compiler's API before making reentrant calls.
    context: ?*anyopaque = null,
    report_fn: *const fn (context: ?*anyopaque, update: ProgressUpdate) void,

    pub fn report(self: ProgressReporter, update: ProgressUpdate) void {
        self.report_fn(self.context, update);
    }
};

pub const Request = struct {
    /// Borrowed UTF-8 Standard Input JSON bytes. A terminator is not required.
    input: []const u8,
    /// Root-selected Zig 0.16 I/O backend. When absent, compilation retains
    /// the deterministic sequential implementation.
    io: ?std.Io = null,
    source_loader: ?SourceLoader = null,
    progress: ?ProgressReporter = null,
};

pub const RequestLanguage = enum {
    unknown,
    solidity,
    yul,
    other,
};

/// Workflow-only features discovered without constructing a Standard JSON DOM.
/// The compiler still performs authoritative envelope and settings validation.
pub const RequestFeatures = struct {
    language: RequestLanguage = .unknown,
    may_load_sources: bool = false,
};

/// Inspects the final top-level `language` and `sources` members.
/// Duplicate top-level members follow the Standard JSON parser's last-wins
/// behavior. Within a source entry, an earlier `urls` member may conservatively
/// produce `may_load_sources = true`; false positives only disable response
/// hits and never suppress a source callback.
pub fn inspectRequestFeatures(
    allocator: std.mem.Allocator,
    input: []const u8,
) !RequestFeatures {
    var scanner = std.json.Scanner.initCompleteInput(allocator, input);
    defer scanner.deinit();
    switch (try scanner.next()) {
        .object_begin => {},
        else => return error.SyntaxError,
    }

    var features: RequestFeatures = .{};
    while (true) {
        switch (try nextFeatureKey(&scanner, allocator, input.len)) {
            .end => break,
            .language => features.language = try inspectLanguage(
                &scanner,
                allocator,
                input.len,
            ),
            .sources => features.may_load_sources = try inspectSourceFeatures(
                &scanner,
                allocator,
                input.len,
            ),
            else => try scanner.skipValue(),
        }
    }
    switch (try scanner.next()) {
        .end_of_document => {},
        else => return error.SyntaxError,
    }
    return features;
}

const FeatureKey = enum {
    end,
    language,
    sources,
    content,
    urls,
    other,
};

fn nextFeatureKey(
    scanner: *std.json.Scanner,
    allocator: std.mem.Allocator,
    max_len: usize,
) !FeatureKey {
    const token = try scanner.nextAllocMax(
        allocator,
        .alloc_if_needed,
        max_len,
    );
    return switch (token) {
        .object_end => .end,
        .string => |key| classifyFeatureKey(key),
        .allocated_string => |key| classified: {
            defer allocator.free(key);
            break :classified classifyFeatureKey(key);
        },
        else => error.SyntaxError,
    };
}

fn classifyFeatureKey(key: []const u8) FeatureKey {
    if (std.mem.eql(u8, key, "language")) return .language;
    if (std.mem.eql(u8, key, "sources")) return .sources;
    if (std.mem.eql(u8, key, "content")) return .content;
    if (std.mem.eql(u8, key, "urls")) return .urls;
    return .other;
}

fn inspectLanguage(
    scanner: *std.json.Scanner,
    allocator: std.mem.Allocator,
    max_len: usize,
) !RequestLanguage {
    if (try scanner.peekNextTokenType() != .string) {
        try scanner.skipValue();
        return .unknown;
    }
    const token = try scanner.nextAllocMax(
        allocator,
        .alloc_if_needed,
        max_len,
    );
    return switch (token) {
        .string => |language| classifyLanguage(language),
        .allocated_string => |language| classified: {
            defer allocator.free(language);
            break :classified classifyLanguage(language);
        },
        else => unreachable,
    };
}

fn classifyLanguage(language: []const u8) RequestLanguage {
    if (std.mem.eql(u8, language, "Solidity")) return .solidity;
    if (std.mem.eql(u8, language, "Yul")) return .yul;
    return .other;
}

fn inspectSourceFeatures(
    scanner: *std.json.Scanner,
    allocator: std.mem.Allocator,
    max_len: usize,
) !bool {
    if (try scanner.peekNextTokenType() != .object_begin) {
        try scanner.skipValue();
        return false;
    }
    _ = try scanner.next();
    var may_load_sources = false;
    while (true) {
        if (try nextFeatureKey(scanner, allocator, max_len) == .end) break;
        may_load_sources = (try inspectSourceEntry(
            scanner,
            allocator,
            max_len,
        )) or may_load_sources;
    }
    return may_load_sources;
}

fn inspectSourceEntry(
    scanner: *std.json.Scanner,
    allocator: std.mem.Allocator,
    max_len: usize,
) !bool {
    if (try scanner.peekNextTokenType() != .object_begin) {
        try scanner.skipValue();
        return false;
    }
    _ = try scanner.next();
    var has_string_content = false;
    var saw_urls = false;
    while (true) {
        switch (try nextFeatureKey(scanner, allocator, max_len)) {
            .end => break,
            .content => {
                has_string_content = try scanner.peekNextTokenType() == .string;
                try scanner.skipValue();
            },
            .urls => {
                saw_urls = true;
                try scanner.skipValue();
            },
            else => try scanner.skipValue(),
        }
    }
    return !has_string_content and saw_urls;
}

/// Owned Standard Output JSON plus machine-visible implementation provenance.
pub const Output = struct {
    allocator: std.mem.Allocator,
    bytes: []u8,
    execution: execution.Execution = .{},

    pub fn deinit(self: *Output) void {
        self.allocator.free(self.bytes);
        self.* = undefined;
    }
};

pub const CompileError = error{
    OutOfMemory,
    InvalidInput,
    UnsupportedInput,
    /// A callback attempted to compile recursively through the same stateful
    /// compiler session. The outer compilation remains valid.
    ReentrantCompilation,
    InternalFailure,
};

pub const ComparisonError = error{OutputMismatch};

/// Compares Standard JSON output byte-for-byte, including field order and the
/// trailing newline. Normalization belongs in an explicitly named comparator.
pub fn compareExact(expected: []const u8, actual: []const u8) ComparisonError!void {
    if (!std.mem.eql(u8, expected, actual)) return error.OutputMismatch;
}

/// Stable type-erased compiler interface. Implementations return owned bytes
/// allocated by the supplied allocator.
pub const Compiler = struct {
    context: *anyopaque,
    compile_fn: *const fn (
        context: *anyopaque,
        allocator: std.mem.Allocator,
        request: Request,
    ) CompileError!Output,

    pub fn compile(
        self: Compiler,
        allocator: std.mem.Allocator,
        request: Request,
    ) CompileError!Output {
        return self.compile_fn(self.context, allocator, request);
    }
};

test "progress reporters receive borrowed allocation-free updates" {
    const Recorder = struct {
        saw_expected_update: bool = false,

        fn report(context: ?*anyopaque, update: ProgressUpdate) void {
            const self: *@This() = @ptrCast(@alignCast(context.?));
            self.saw_expected_update = update.stage == .parsing_sources and
                update.completed_items == 2 and
                update.estimated_total_items == 3 and
                std.mem.eql(u8, update.item_name, "Imported.sol");
        }
    };

    var recorder: Recorder = .{};
    const reporter: ProgressReporter = .{
        .context = &recorder,
        .report_fn = Recorder.report,
    };
    reporter.report(.{
        .stage = .parsing_sources,
        .completed_items = 2,
        .estimated_total_items = 3,
        .item_name = "Imported.sol",
    });

    try std.testing.expect(recorder.saw_expected_update);
}

test "exact output comparison includes whitespace and trailing bytes" {
    try compareExact("{}\n", "{}\n");
    try std.testing.expectError(error.OutputMismatch, compareExact("{}", "{}\n"));
    try std.testing.expectError(error.OutputMismatch, compareExact("{ }\n", "{}\n"));
}

test "request feature inspection follows workflow and callback semantics" {
    const inline_features = try inspectRequestFeatures(std.testing.allocator,
        \\{"language":"Yul","sources":{"A.yul":{"urls":["ignored"],"content":"object {}"}}}
    );
    try std.testing.expectEqual(RequestLanguage.yul, inline_features.language);
    try std.testing.expect(!inline_features.may_load_sources);

    const callback_features = try inspectRequestFeatures(std.testing.allocator,
        \\{"langu\u0061ge":"Solidity","sources":{"A.sol":{"urls":["A.sol"]}}}
    );
    try std.testing.expectEqual(RequestLanguage.solidity, callback_features.language);
    try std.testing.expect(callback_features.may_load_sources);

    const final_members = try inspectRequestFeatures(std.testing.allocator,
        \\{"language":"Solidity","language":"Other","sources":{"A.sol":{"urls":["A.sol"]}},"sources":{"A.sol":{"content":""}}}
    );
    try std.testing.expectEqual(RequestLanguage.other, final_members.language);
    try std.testing.expect(!final_members.may_load_sources);
}

test "request feature inspection rejects incomplete JSON" {
    try std.testing.expectError(
        error.UnexpectedEndOfInput,
        inspectRequestFeatures(std.testing.allocator, "{\"language\":"),
    );
}
