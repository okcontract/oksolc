// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Bounded fuzz target for the public libsolc-compatible Standard JSON ABI.
//!
//! Inputs traverse the exported `solidity_compile` entry point, the yyjson C
//! adapter, source canonicalization and callbacks, the strict Zig JSON parser,
//! and the Standard JSON dispatcher. Callback behavior is selected by URL so
//! it remains part of the coverage-guided input: `ok:` loads a small source,
//! `error:` returns an error, and every other URL is unsupported.

const std = @import("std");
const libsolc = @import("compiler").libsolc.libsolc;

const max_standard_json_bytes = 4 * 1024;
const source_contents = "contract Imported { function value() external pure returns (uint256) { return 1; } }";
const callback_error = "fuzzed source callback failure";

const content_seed = smithSliceCorpus(
    \\{"language":"Solidity","sources":{"C.sol":{"content":"contract C {}"}}}
    ,
);
const callback_success_seed = smithSliceCorpus(
    \\{"language":"Solidity","sources":{"Imported.sol":{"urls":["ok:Imported.sol"]}}}
    ,
);
const callback_error_seed = smithSliceCorpus(
    \\{"language":"Solidity","sources":{"Imported.sol":{"urls":["error:Imported.sol"]}}}
    ,
);
const duplicate_seed = smithSliceCorpus(
    \\{"language":"Solidity","sources":{"B.sol":{"content":"contract B {}"},"A.sol":{"urls":["missing:A.sol","ok:A.sol"]},"B.sol":{"content":"contract B2 {}"}},"settings":{}}
    ,
);

test "fuzz bounded public Standard JSON compilation" {
    try std.testing.fuzz({}, fuzzStandardJson, .{
        .corpus = &.{
            &content_seed,
            &callback_success_seed,
            &callback_error_seed,
            &duplicate_seed,
        },
    });
}

fn fuzzStandardJson(_: void, smith: *std.testing.Smith) !void {
    @disableInstrumentation();
    var input_buffer: [max_standard_json_bytes + 1]u8 = undefined;
    const input_len = smith.sliceWeightedBytes(input_buffer[0..max_standard_json_bytes], &.{
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
    input_buffer[input_len] = 0;
    const input: [:0]const u8 = input_buffer[0..input_len :0];

    const output = libsolc.solidity_compile(input.ptr, sourceCallback, null);
    if (output) |bytes| libsolc.solidity_free(bytes);
    libsolc.solidity_reset();
}

fn sourceCallback(
    _: ?*anyopaque,
    _: [*:0]const u8,
    data_pointer: [*:0]const u8,
    contents: *?[*:0]u8,
    error_message: *?[*:0]u8,
) callconv(.c) void {
    contents.* = null;
    error_message.* = null;
    const data = std.mem.span(data_pointer);
    if (std.mem.startsWith(u8, data, "ok:")) {
        contents.* = abiCopyZ(source_contents);
    } else if (std.mem.startsWith(u8, data, "error:")) {
        error_message.* = abiCopyZ(callback_error);
    }
}

fn abiCopyZ(bytes: []const u8) ?[*:0]u8 {
    const destination = libsolc.solidity_alloc(bytes.len + 1) orelse return null;
    @memcpy(destination[0..bytes.len], bytes);
    destination[bytes.len] = 0;
    return destination;
}

fn smithSliceCorpus(comptime value: []const u8) [4 + value.len]u8 {
    var result: [4 + value.len]u8 = undefined;
    std.mem.writeInt(u32, result[0..4], value.len, .little);
    @memcpy(result[4..], value);
    return result;
}
