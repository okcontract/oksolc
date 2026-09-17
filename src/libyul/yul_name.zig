// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! `YulName` is the semantic alias of the interned `YulString` handle.

const YulStringModule = @import("yul_string.zig");

pub const YulName = YulStringModule.YulString;
