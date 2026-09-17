// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Contracts shared by the compiler, C ABI, and CLI.

pub const execution = @import("execution.zig");
pub const standard_json = @import("standard_json.zig");

test {
    _ = execution;
    _ = standard_json;
}
