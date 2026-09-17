// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Solidity parser aliases for the shared `liblangutil` token API.

const std = @import("std");
const shared = @import("../../liblangutil/token.zig");

pub const Token = shared.Token;
pub const TokenTraits = shared;
pub const ElementaryTypeNameToken = shared.ElementaryTypeNameToken;

test "frontend parser token aliases preserve the shared enum ABI" {
    try std.testing.expect(Token == shared.Token);
    try std.testing.expectEqual(
        @intFromEnum(shared.Token.Function),
        @intFromEnum(Token.Function),
    );
    try std.testing.expectEqualStrings("function", TokenTraits.friendlyName(.Function));
}
