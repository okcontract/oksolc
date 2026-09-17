// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

const std = @import("std");
const solidity = @import("solidity");

const corpus_json = @embedFile("standard-json/corpus.json");
const frozen_merkle_root = @embedFile("standard-json/merkle-root.txt");
const Digest = [std.crypto.hash.sha2.Sha256.digest_length]u8;

const input_cases = [_]struct { path: []const u8, contents: []const u8 }{
    .{
        .path = "test/zig/standard-json/empty-sources.json",
        .contents = @embedFile("standard-json/empty-sources.json"),
    },
    .{
        .path = "test/zig/standard-json/solidity-abi.json",
        .contents = @embedFile("standard-json/solidity-abi.json"),
    },
    .{
        .path = "test/zig/standard-json/via-ir-smoke.json",
        .contents = @embedFile("standard-json/via-ir-smoke.json"),
    },
    .{
        .path = "test/zig/standard-json/parser-error.json",
        .contents = @embedFile("standard-json/parser-error.json"),
    },
    .{
        .path = "test/zig/standard-json/type-error.json",
        .contents = @embedFile("standard-json/type-error.json"),
    },
};

const reference_outputs = [_]struct { path: []const u8, contents: []const u8 }{
    .{
        .path = "test/zig/standard-json/expected/empty-sources.json",
        .contents = @embedFile("standard-json/expected/empty-sources.json"),
    },
    .{
        .path = "test/zig/standard-json/expected/solidity-abi.json",
        .contents = @embedFile("standard-json/expected/solidity-abi.json"),
    },
    .{
        .path = "test/zig/standard-json/expected/via-ir-smoke.json",
        .contents = @embedFile("standard-json/expected/via-ir-smoke.json"),
    },
    .{
        .path = "test/zig/standard-json/expected/parser-error.json",
        .contents = @embedFile("standard-json/expected/parser-error.json"),
    },
    .{
        .path = "test/zig/standard-json/expected/type-error.json",
        .contents = @embedFile("standard-json/expected/type-error.json"),
    },
};

const Corpus = struct {
    schema_version: u32,
    baseline: Baseline,
    reference: Reference,
    merkle: Merkle,
    cases: []const Case,

    const Baseline = struct {
        version: []const u8,
    };

    const Reference = struct {
        command: []const u8,
        required_version: []const u8,
    };

    const Merkle = struct {
        algorithm: []const u8,
        format: []const u8,
        odd_node: []const u8,
        root: []const u8,
    };

    const Case = struct {
        id: []const u8,
        input: []const u8,
        reference_output: []const u8,
        reference_sha256: []const u8,
        expected: enum { success, @"error" },
        pipeline: enum { legacy, via_ir, frontend },
    };
};

const StandardInputHeader = struct {
    language: []const u8,
};

test "reference corpus is valid JSON pinned to Solidity 0.8.36" {
    try std.testing.expect(try std.json.validate(std.testing.allocator, corpus_json));

    var corpus = try std.json.parseFromSlice(Corpus, std.testing.allocator, corpus_json, .{});
    defer corpus.deinit();

    try std.testing.expectEqual(@as(u32, 6), corpus.value.schema_version);
    try std.testing.expectEqualStrings(solidity.baseline.version, corpus.value.baseline.version);
    try std.testing.expectEqualStrings("solc --standard-json", corpus.value.reference.command);
    try std.testing.expectEqualStrings(
        solidity.baseline.version,
        corpus.value.reference.required_version,
    );
    try std.testing.expectEqualStrings("keccak256", corpus.value.merkle.algorithm);
    try std.testing.expectEqualStrings(
        "zsolc-reference-output-v1",
        corpus.value.merkle.format,
    );
    try std.testing.expectEqualStrings("duplicate_last", corpus.value.merkle.odd_node);
    try std.testing.expect(isLowerHex(corpus.value.merkle.root, @sizeOf(Digest) * 2));
    try std.testing.expectEqual(input_cases.len, corpus.value.cases.len);
    try std.testing.expectEqual(input_cases.len, reference_outputs.len);

    for (corpus.value.cases, input_cases, reference_outputs) |case, input, output| {
        try std.testing.expectEqualStrings(input.path, case.input);
        try std.testing.expectEqualStrings(output.path, case.reference_output);
        try std.testing.expect(isLowerHex(case.reference_sha256, 64));
        try std.testing.expect(try std.json.validate(std.testing.allocator, input.contents));
        try std.testing.expect(try std.json.validate(std.testing.allocator, output.contents));

        var digest: Digest = undefined;
        std.crypto.hash.sha2.Sha256.hash(output.contents, &digest, .{});
        const digest_hex = std.fmt.bytesToHex(digest, .lower);
        try std.testing.expectEqualStrings(case.reference_sha256, &digest_hex);

        var header = try std.json.parseFromSlice(
            StandardInputHeader,
            std.testing.allocator,
            input.contents,
            .{ .ignore_unknown_fields = true },
        );
        defer header.deinit();
        try std.testing.expectEqualStrings("Solidity", header.value.language);
    }

    const root = try referenceMerkleRoot(
        corpus.value.reference.required_version,
        corpus.value.cases,
    );
    const root_hex = std.fmt.bytesToHex(root, .lower);
    if (!std.mem.eql(u8, corpus.value.merkle.root, &root_hex))
        std.debug.print("computed frozen reference Merkle root: {s}\n", .{&root_hex});
    try std.testing.expectEqualStrings(corpus.value.merkle.root, &root_hex);

    const root_file = std.mem.trim(u8, frozen_merkle_root, " \t\r\n");
    try std.testing.expectEqual(@as(usize, 2 + @sizeOf(Digest) * 2), root_file.len);
    try std.testing.expectEqualStrings("0x", root_file[0..2]);
    try std.testing.expectEqualStrings(corpus.value.merkle.root, root_file[2..]);
}

test "clean compiler matches frozen solc 0.8.36 outputs byte-exact" {
    var all_match = true;
    for (input_cases, reference_outputs) |input, reference_output| {
        var dispatcher: solidity.StandardJsonDispatcher = .{};
        var actual = try dispatcher.compiler().compile(
            std.testing.allocator,
            .{ .input = input.contents },
        );
        defer actual.deinit();
        if (!std.mem.eql(u8, reference_output.contents, actual.bytes)) {
            std.debug.print("frozen compatibility mismatch: {s}\n", .{input.path});
            all_match = false;
        }
    }
    try std.testing.expect(all_match);
}

fn expectCorpusMatchesClean(session: *solidity.incremental.CompilerSession) !void {
    for (input_cases) |input| {
        var dispatcher: solidity.StandardJsonDispatcher = .{};
        var expected = try dispatcher.compiler().compile(
            std.testing.allocator,
            .{ .input = input.contents },
        );
        defer expected.deinit();
        var actual = try session.compiler().compile(
            std.testing.allocator,
            .{ .input = input.contents },
        );
        defer actual.deinit();
        try solidity.standard_json.compareExact(expected.bytes, actual.bytes);
    }
}

fn expectEachCorpusCaseMatchesCleanTwice(
    session: *solidity.incremental.CompilerSession,
) !void {
    for (input_cases) |input| {
        var dispatcher: solidity.StandardJsonDispatcher = .{};
        var expected = try dispatcher.compiler().compile(
            std.testing.allocator,
            .{ .input = input.contents },
        );
        defer expected.deinit();
        for (0..2) |_| {
            var actual = try session.compiler().compile(
                std.testing.allocator,
                .{ .input = input.contents },
            );
            defer actual.deinit();
            try solidity.standard_json.compareExact(expected.bytes, actual.bytes);
        }
    }
}

test "full frozen corpus is byte-exact through a memory compiler session" {
    var session = solidity.incremental.CompilerSession.init(std.testing.allocator);
    defer session.deinit();
    // Every compatibility case reaches either no frontend revision or a
    // graph-complete revision, so its immediate second compilation is safe to
    // reuse exactly.
    try expectEachCorpusCaseMatchesCleanTwice(&session);
    const statistics = session.statistics();
    try std.testing.expectEqual(
        @as(u64, input_cases.len),
        statistics.memory_response_hits,
    );
    try std.testing.expectEqual(
        @as(u64, input_cases.len),
        statistics.memory.hits,
    );
    try std.testing.expectEqual(@as(u64, 0), statistics.coherence_rejections);
}

test "full frozen corpus is byte-exact after a persistent session restart" {
    const authentication_key = [_]u8{0x72} ** 32;
    var temporary = std.testing.tmpDir(.{});
    defer temporary.cleanup();
    const path = try std.fmt.allocPrint(
        std.testing.allocator,
        ".zig-cache/tmp/{s}/reference-corpus.sqlite",
        .{&temporary.sub_path},
    );
    defer std.testing.allocator.free(path);
    const fingerprint = solidity.incremental.CompilerFingerprint.init(
        "reference-corpus-persistent-test",
    );

    {
        var first_store = try solidity.incremental.SqliteStore.init(
            std.testing.allocator,
            std.testing.io,
            path,
            authentication_key,
        );
        defer first_store.deinit();
        var first_session = try solidity.incremental.CompilerSession.initWithBackingStore(
            std.testing.allocator,
            fingerprint,
            first_store.artifactStore(),
        );
        defer first_session.deinit();
        try expectCorpusMatchesClean(&first_session);
    }

    var reopened_store = try solidity.incremental.SqliteStore.init(
        std.testing.allocator,
        std.testing.io,
        path,
        authentication_key,
    );
    defer reopened_store.deinit();
    var restarted_session = try solidity.incremental.CompilerSession.initWithBackingStore(
        std.testing.allocator,
        fingerprint,
        reopened_store.artifactStore(),
    );
    defer restarted_session.deinit();
    try expectCorpusMatchesClean(&restarted_session);
    const statistics = restarted_session.statistics();
    try std.testing.expectEqual(@as(u64, input_cases.len), statistics.persistent_hits);
    try std.testing.expectEqual(@as(u64, 0), statistics.persistent_misses);
}

fn isLowerHex(value: []const u8, expected_length: usize) bool {
    if (value.len != expected_length) return false;
    for (value) |character| switch (character) {
        '0'...'9', 'a'...'f' => {},
        else => return false,
    };
    return true;
}

fn referenceMerkleRoot(
    required_version: []const u8,
    cases: []const Corpus.Case,
) !Digest {
    if (cases.len == 0 or cases.len > reference_outputs.len)
        return error.InvalidMerkleTreeSize;

    var nodes: [reference_outputs.len]Digest = undefined;
    for (cases, reference_outputs[0..cases.len], 0..) |case, output, index|
        nodes[index] = try referenceMerkleLeaf(
            required_version,
            index,
            case.id,
            output.contents,
        );

    var node_count = cases.len;
    while (node_count > 1) {
        var parent_index: usize = 0;
        var child_index: usize = 0;
        while (child_index < node_count) : (child_index += 2) {
            const right_index = if (child_index + 1 < node_count)
                child_index + 1
            else
                child_index;
            nodes[parent_index] = referenceMerkleParent(
                nodes[child_index],
                nodes[right_index],
            );
            parent_index += 1;
        }
        node_count = parent_index;
    }
    return nodes[0];
}

fn referenceMerkleLeaf(
    required_version: []const u8,
    index: usize,
    id: []const u8,
    reference_output: []const u8,
) !Digest {
    var output_digest: Digest = undefined;
    std.crypto.hash.sha2.Sha256.hash(reference_output, &output_digest, .{});

    var hasher = std.crypto.hash.sha3.Keccak256.init(.{});
    hasher.update(&.{0});
    try updateMerkleLength(&hasher, required_version.len);
    hasher.update(required_version);
    try updateMerkleLength(&hasher, index);
    try updateMerkleLength(&hasher, id.len);
    hasher.update(id);
    hasher.update(&output_digest);

    var result: Digest = undefined;
    hasher.final(&result);
    return result;
}

fn referenceMerkleParent(left: Digest, right: Digest) Digest {
    var hasher = std.crypto.hash.sha3.Keccak256.init(.{});
    hasher.update(&.{1});
    hasher.update(&left);
    hasher.update(&right);
    var result: Digest = undefined;
    hasher.final(&result);
    return result;
}

fn updateMerkleLength(hasher: *std.crypto.hash.sha3.Keccak256, value: usize) !void {
    var encoded: [@sizeOf(u32)]u8 = undefined;
    std.mem.writeInt(
        u32,
        &encoded,
        std.math.cast(u32, value) orelse return error.MerkleValueTooLong,
        .big,
    );
    hasher.update(&encoded);
}
