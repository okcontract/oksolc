// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Bounded Solidity parser fuzz target kept separate from the C-backed
//! compiler module so Zig's native coverage instrumentation can link it.

const std = @import("std");
const Diagnostics = @import("liblangutil/diagnostics.zig");
const EVMVersion = @import("liblangutil/evm_version.zig").EVMVersion;
const Parser = @import("libsolidity/parsing/parser.zig");

const max_source_bytes = 2 * 1024;
const solidity_seed = smithSliceCorpus(
    "// SPDX-License-Identifier: UNLICENSED\n" ++
        "contract C { function f(uint x) external pure returns (uint) { return x + 1; } }",
);

test "fuzz bounded Solidity source parsing" {
    try std.testing.fuzz({}, fuzzSolidityParser, .{
        .corpus = &.{&solidity_seed},
    });
}

fn fuzzSolidityParser(_: void, smith: *std.testing.Smith) !void {
    @disableInstrumentation();
    var source_buffer: [max_source_bytes]u8 = undefined;
    const source_len = smith.sliceWeightedBytes(&source_buffer, &.{
        .rangeAtMost(u8, 0x00, 0xff, 1),
        .rangeAtMost(u8, 0x20, 0x7e, 5),
        .rangeAtMost(u8, 'a', 'z', 4),
        .value(u8, ' ', 8),
        .value(u8, '\n', 4),
        .value(u8, '{', 4),
        .value(u8, '}', 4),
        .value(u8, '(', 3),
        .value(u8, ')', 3),
        .value(u8, ';', 3),
    });
    const source = source_buffer[0..source_len];

    var reporter = Diagnostics.ErrorReporter.init(std.testing.allocator);
    defer reporter.deinit();
    var parsed = try Parser.parseSource(
        std.testing.allocator,
        source,
        "fuzz.sol",
        &reporter,
        EVMVersion.current(),
    );
    defer parsed.deinit();

    try std.testing.expectEqualSlices(u8, source, parsed.tree.source);
}

fn smithSliceCorpus(comptime value: []const u8) [4 + value.len]u8 {
    var result: [4 + value.len]u8 = undefined;
    std.mem.writeInt(u32, result[0..4], value.len, .little);
    @memcpy(result[4..], value);
    return result;
}
