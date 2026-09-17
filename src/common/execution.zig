// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

/// Identifies the implementation that produced a Standard JSON response.
/// The compiler has a single in-process implementation; system `solc` is used
/// only by explicit reference checks and benchmarks.
pub const Backend = enum { zig };

pub const Execution = struct {
    backend: Backend = .zig,
};

test "the only compiler backend is Zig" {
    const execution: Execution = .{};
    try @import("std").testing.expectEqual(Backend.zig, execution.backend);
}
