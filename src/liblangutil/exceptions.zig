// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Coherent facade for the exception and diagnostic types declared in
//! `liblangutil/Exceptions.h`.

const diagnostics = @import("diagnostics.zig");
const util_exceptions = @import("../libsolutil/exceptions.zig");

pub const ErrorId = diagnostics.ErrorId;
pub const ErrorType = diagnostics.ErrorType;
pub const Severity = diagnostics.Severity;
pub const TypeOrSeverity = diagnostics.TypeOrSeverity;
pub const Error = diagnostics.Diagnostic;
pub const ErrorList = []const diagnostics.Diagnostic;
pub const SecondarySourceLocation = diagnostics.SecondarySourceLocation;

pub const ExceptionKind = util_exceptions.Kind;
pub const Failure = util_exceptions.Failure;
pub const Exception = util_exceptions.Exception;

pub const errorSeverity = diagnostics.errorSeverity;
pub const errorSeverityOrType = diagnostics.errorSeverityOrType;
pub const isError = diagnostics.isErrorType;
pub const containsErrors = diagnostics.containsErrors;
pub const formatErrorSeverity = diagnostics.formatErrorSeverity;
pub const formatErrorSeverityLowercase = diagnostics.formatErrorSeverityLowercase;
pub const formatErrorType = diagnostics.formatErrorType;
pub const parseErrorType = diagnostics.parseErrorType;
pub const formatTypeOrSeverity = diagnostics.formatTypeOrSeverity;
