// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Bounded fuzz target for the strict JSON parser used after Standard JSON
//! envelope inspection.

const std = @import("std");
const JSON = @import("libsolutil/json.zig");

const max_json_bytes = 4 * 1024;
const json_seed = smithSliceCorpus(
    \\{"language":"Solidity","sources":{"C.sol":{"content":"contract C {}"}}}
    ,
);

test "fuzz bounded strict JSON parsing" {
    try std.testing.fuzz({}, fuzzStrictJson, .{
        .corpus = &.{&json_seed},
    });
}

fn fuzzStrictJson(_: void, smith: *std.testing.Smith) !void {
    @disableInstrumentation();
    var input_buffer: [max_json_bytes]u8 = undefined;
    const input_len = smith.sliceWeightedBytes(&input_buffer, &.{
        .rangeAtMost(u8, 0x00, 0xff, 1),
        .rangeAtMost(u8, 0x20, 0x7e, 5),
        .value(u8, ' ', 4),
        .value(u8, '\n', 2),
        .value(u8, '{', 6),
        .value(u8, '}', 6),
        .value(u8, '[', 4),
        .value(u8, ']', 4),
        .value(u8, '"', 8),
        .value(u8, ':', 5),
        .value(u8, ',', 5),
    });

    var parsed = try JSON.jsonParseStrict(
        std.testing.allocator,
        input_buffer[0..input_len],
    );
    defer parsed.deinit();
}

fn smithSliceCorpus(comptime value: []const u8) [4 + value.len]u8 {
    var result: [4 + value.len]u8 = undefined;
    std.mem.writeInt(u32, result[0..4], value.len, .little);
    @memcpy(result[4..], value);
    return result;
}
