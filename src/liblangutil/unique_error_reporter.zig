// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! File-granular facade for `UniqueErrorReporter.h`.

const implementation = @import("diagnostics.zig");

pub const UniqueErrorReporter = implementation.UniqueErrorReporter;
pub const UniqueReportError = implementation.UniqueReportError;
