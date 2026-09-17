// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! File-granular facade for `ErrorReporter.h`.

const implementation = @import("diagnostics.zig");

pub const ErrorReporter = implementation.ErrorReporter;
pub const ErrorWatcher = implementation.ErrorWatcher;
pub const ReportError = implementation.ReportError;
