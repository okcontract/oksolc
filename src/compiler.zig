// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Root module for the Solidity compiler implementation.

const cxx_compat = @import("cxx_compat");
const modules = @import("modules.zig");

pub const libsolutil = modules.libsolutil;
pub const liblangutil = modules.liblangutil;
pub const libevmasm = modules.libevmasm;
pub const libevm = modules.libevm;
pub const libyul = modules.libyul;
pub const libsolidity = modules.libsolidity;
pub const libsolc = modules.libsolc;
pub const incremental = modules.incremental;

comptime {
    _ = cxx_compat.Vector;
    // Keep the C ABI exports reachable when this file roots the shared library.
    _ = libsolc.libsolc.solidity_compile;
}

test "compiler module inventory" {
    _ = modules;
    _ = modules.libevm;
    // Keep every public incremental component in the normal compiler test
    // root, including components introduced before their pipeline wiring.
    _ = modules.incremental;
}
