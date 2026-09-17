// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Dialect interface and builtin metadata share the AST module to avoid a C++ forward-declaration cycle.

const AST = @import("ast.zig");

pub const BuiltinFunction = AST.BuiltinFunction;
pub const DialectVTable = AST.DialectVTable;
pub const Dialect = AST.Dialect;
