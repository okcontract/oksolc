// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Explicit Zig error-union equivalents of the assertion macros.

pub fn require(condition: bool, failure: anyerror) !void {
    if (!condition) return failure;
}

pub fn assertInternal(condition: bool) error{InternalCompilerError}!void {
    if (!condition) return error.InternalCompilerError;
}

pub fn assertUnimplemented(condition: bool) error{UnimplementedFeatureError}!void {
    if (!condition) return error.UnimplementedFeatureError;
}

pub fn assertValidAst(condition: bool) error{InvalidAstError}!void {
    if (!condition) return error.InvalidAstError;
}

pub fn unreachableCode() noreturn {
    unreachable;
}

test "assertions map failure categories without payload loss" {
    const std = @import("std");
    try require(true, error.BadHexCharacter);
    try std.testing.expectError(error.InternalCompilerError, assertInternal(false));
    try std.testing.expectError(error.UnimplementedFeatureError, assertUnimplemented(false));
    try std.testing.expectError(error.InvalidAstError, assertValidAst(false));
}
