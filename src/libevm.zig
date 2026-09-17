// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Shared exact EVM semantics. This module currently provides deployment
//! address calculation and precompile dispatch metadata; bytecode execution,
//! precompile execution, and a state host remain separate staged deliverables.

pub const address = @import("libevm/address.zig");
pub const precompiles = @import("libevm/precompiles.zig");

test {
    _ = @import("libevm/address_tests.zig");
    _ = precompiles;
}
