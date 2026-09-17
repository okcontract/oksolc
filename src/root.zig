// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Public Zig API for the Solidity compiler.

const std = @import("std");

pub const standard_json = @import("common").standard_json;
pub const execution = @import("common").execution;
pub const cxx_compat = @import("cxx_compat");
pub const compiler = @import("compiler");

pub const libsolutil = compiler.libsolutil;
pub const liblangutil = compiler.liblangutil;
pub const libevmasm = compiler.libevmasm;
pub const libevm = compiler.libevm;
pub const libyul = compiler.libyul;
pub const libsolidity = compiler.libsolidity;
pub const libsolc = compiler.libsolc;
pub const incremental = compiler.incremental;
pub const StandardJsonDispatcher = libsolc.libsolc.Dispatcher;
/// Supported long-lived in-memory Standard JSON compiler session.
pub const CompilerSession = incremental.CompilerSession;
pub const CompilerSessionOptions = incremental.CompilerSessionOptions;
/// Supported long-lived Standard JSON session backed by a disposable SQLite cache.
pub const SqliteCompilerSession = incremental.SqliteCompilerSession;
pub const SqliteCompilerSessionOptions = incremental.SqliteCompilerSessionOptions;
pub const CompilerSessionStatistics = incremental.SessionStatistics;

pub const baseline = struct {
    pub const version = "0.8.36";
    pub const zig_version = "0.16.0";
};

test {
    _ = standard_json;
    _ = execution;
    _ = cxx_compat;
    _ = compiler;
}

test "public CompilerSession retains exact Standard JSON responses" {
    const input =
        \\{"language":"Yul","sources":{"A.yul":{"content":"object \"A\" { code { stop() } }"}},"settings":{"outputSelection":{"*":{"*":["evm.bytecode.object"]}}}}
    ;
    var session = CompilerSession.init(std.testing.allocator);
    defer session.deinit();

    var first = try session.compile(std.testing.allocator, .{ .input = input });
    defer first.deinit();
    var second = try session.compile(std.testing.allocator, .{ .input = input });
    defer second.deinit();

    try std.testing.expectEqualStrings(first.bytes, second.bytes);
    const statistics = session.statistics();
    try std.testing.expectEqual(@as(u64, 2), statistics.requests);
    try std.testing.expectEqual(@as(u64, 1), statistics.memory_response_hits);
}
