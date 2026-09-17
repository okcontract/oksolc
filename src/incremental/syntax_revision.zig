// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Immutable, per-source syntax ownership shared across frontend revisions.

const std = @import("std");
const Diagnostics = @import("../liblangutil/diagnostics.zig");
const EVMVersion = @import("../liblangutil/evm_version.zig").EVMVersion;
const FixedHash = @import("../libsolutil/fixed_hash.zig");
const Parser = @import("../libsolidity/parsing/parser.zig");
const Identity = @import("identity.zig");
const SemanticFingerprint = @import("semantic_fingerprint.zig");

pub const SourceId = Identity.SourceId;
pub const H256 = FixedHash.H256;

pub const SyntaxCompleteness = enum {
    parsed,
    failed,
};

/// Reference-counted because a candidate revision borrows unchanged sources
/// until commit or abort resolves ownership of the preceding revision.
pub const SyntaxSource = struct {
    allocator: std.mem.Allocator,
    reference_count: usize = 1,
    content_digest: H256,
    semantic_fingerprints: SemanticFingerprint.SourceFingerprints,
    evm_version: EVMVersion,
    completeness: SyntaxCompleteness,
    parse_diagnostics: []Diagnostics.Diagnostic,
    parsed: Parser.ParseResult,

    pub fn create(
        allocator: std.mem.Allocator,
        parsed: *Parser.ParseResult,
        content_digest: H256,
        evm_version: EVMVersion,
        parse_diagnostics: []const Diagnostics.Diagnostic,
    ) std.mem.Allocator.Error!*SyntaxSource {
        const result = try allocator.create(SyntaxSource);
        errdefer allocator.destroy(result);
        const owned_diagnostics = try allocator.alloc(
            Diagnostics.Diagnostic,
            parse_diagnostics.len,
        );
        errdefer allocator.free(owned_diagnostics);
        var initialized_diagnostics: usize = 0;
        errdefer for (owned_diagnostics[0..initialized_diagnostics]) |*diagnostic|
            diagnostic.deinit();
        for (parse_diagnostics, owned_diagnostics) |*diagnostic, *target| {
            target.* = try diagnostic.clone(allocator);
            initialized_diagnostics += 1;
        }
        result.* = .{
            .allocator = allocator,
            .content_digest = content_digest,
            .semantic_fingerprints = SemanticFingerprint.computeWithContentDigest(
                &parsed.tree,
                &content_digest,
            ),
            .evm_version = evm_version,
            .completeness = if (parsed.root() == null) .failed else .parsed,
            .parse_diagnostics = owned_diagnostics,
            .parsed = parsed.*,
        };
        parsed.* = undefined;
        return result;
    }

    pub fn retain(self: *SyntaxSource) void {
        std.debug.assert(self.reference_count != std.math.maxInt(usize));
        self.reference_count += 1;
    }

    pub fn release(self: *SyntaxSource) void {
        std.debug.assert(self.reference_count != 0);
        self.reference_count -= 1;
        if (self.reference_count != 0) return;
        const allocator = self.allocator;
        for (self.parse_diagnostics) |*diagnostic| diagnostic.deinit();
        allocator.free(self.parse_diagnostics);
        self.parsed.deinit();
        allocator.destroy(self);
    }

    pub fn replayParseDiagnostics(
        self: *const SyntaxSource,
        reporter: *Diagnostics.ErrorReporter,
    ) Diagnostics.ReportError!void {
        for (self.parse_diagnostics) |*diagnostic|
            try reporter.reportWithSecondary(
                diagnostic.error_id,
                diagnostic.error_type,
                diagnostic.location orelse .{},
                &diagnostic.secondary,
                diagnostic.description,
            );
    }

    pub fn reusableFor(
        self: *const SyntaxSource,
        content_digest: *const H256,
        evm_version: EVMVersion,
    ) bool {
        return self.completeness == .parsed and
            self.content_digest.eql(content_digest) and
            self.evm_version.eql(evm_version);
    }
};

pub const SyntaxRevision = struct {
    allocator: std.mem.Allocator,
    sources: []?*SyntaxSource,
    parsed_sources: usize = 0,
    reused_sources: usize = 0,

    pub fn init(
        allocator: std.mem.Allocator,
        known_source_count: usize,
    ) std.mem.Allocator.Error!SyntaxRevision {
        const sources = try allocator.alloc(?*SyntaxSource, known_source_count);
        @memset(sources, null);
        return .{ .allocator = allocator, .sources = sources };
    }

    pub fn deinit(self: *SyntaxRevision) void {
        for (self.sources) |source| if (source) |value| value.release();
        self.allocator.free(self.sources);
        self.* = undefined;
    }

    pub fn ensureSourceCapacity(
        self: *SyntaxRevision,
        known_source_count: usize,
    ) std.mem.Allocator.Error!void {
        if (known_source_count <= self.sources.len) return;
        const previous_len = self.sources.len;
        self.sources = try self.allocator.realloc(self.sources, known_source_count);
        @memset(self.sources[previous_len..], null);
    }

    /// Transfers the caller's existing reference into this revision.
    pub fn adoptParsed(
        self: *SyntaxRevision,
        source_id: SourceId,
        source: *SyntaxSource,
    ) error{ InvalidSourceId, DuplicateSource }!void {
        const index: usize = @intCast(source_id.index());
        if (index >= self.sources.len) return error.InvalidSourceId;
        if (self.sources[index] != null) return error.DuplicateSource;
        self.sources[index] = source;
        self.parsed_sources += 1;
    }

    /// Adds one reference borrowed from the preceding committed revision.
    pub fn retainReused(
        self: *SyntaxRevision,
        source_id: SourceId,
        source: *SyntaxSource,
    ) error{ InvalidSourceId, DuplicateSource }!void {
        try self.adoptParsed(source_id, source);
        source.retain();
        self.parsed_sources -= 1;
        self.reused_sources += 1;
    }

    pub fn get(self: *const SyntaxRevision, source_id: SourceId) ?*SyntaxSource {
        const index: usize = @intCast(source_id.index());
        if (index >= self.sources.len) return null;
        return self.sources[index];
    }
};

test "syntax revisions retain reused trees and release candidates transactionally" {
    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSourceWithIdentity(
        std.testing.allocator,
        "contract A {}",
        "A.sol",
        &reporter,
        EVMVersion.current(),
        SourceId.init(3),
        0,
    );
    const digest = @import("../libsolutil/keccak256.zig").keccak256("contract A {}");
    const source = try SyntaxSource.create(
        std.testing.allocator,
        &parsed,
        digest,
        EVMVersion.current(),
        reporter.diagnostics(),
    );

    var committed = try SyntaxRevision.init(std.testing.allocator, 4);
    defer committed.deinit();
    try committed.adoptParsed(SourceId.init(3), source);
    try std.testing.expectEqual(@as(usize, 1), source.reference_count);

    var candidate = try SyntaxRevision.init(std.testing.allocator, 4);
    try candidate.retainReused(SourceId.init(3), source);
    try std.testing.expectEqual(@as(usize, 2), source.reference_count);
    try std.testing.expect(candidate.get(SourceId.init(3)).? == source);
    candidate.deinit();

    try std.testing.expectEqual(@as(usize, 1), source.reference_count);
    try std.testing.expect(source.reusableFor(&digest, EVMVersion.current()));
}
