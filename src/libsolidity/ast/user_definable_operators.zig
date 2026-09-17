// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! User-definable operator inventory from `UserDefinableOperators.h`.

const std = @import("std");
const Token = @import("../../liblangutil/token.zig").Token;

pub const user_definable_operators = [_]Token{
    .BitOr,
    .BitAnd,
    .BitXor,
    .BitNot,
    .Add,
    .Sub,
    .Mul,
    .Div,
    .Mod,
    .Equal,
    .NotEqual,
    .LessThan,
    .GreaterThan,
    .LessThanOrEqual,
    .GreaterThanOrEqual,
};

pub fn isUserDefinableOperator(token: Token) bool {
    for (user_definable_operators) |candidate|
        if (candidate == token) return true;
    return false;
}

test "operator inventory preserves upstream order and exclusions" {
    try std.testing.expectEqual(@as(usize, 15), user_definable_operators.len);
    try std.testing.expectEqual(Token.BitOr, user_definable_operators[0]);
    try std.testing.expectEqual(Token.GreaterThanOrEqual, user_definable_operators[14]);
    try std.testing.expect(isUserDefinableOperator(.Add));
    try std.testing.expect(!isUserDefinableOperator(.Exp));
}
