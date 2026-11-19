// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
//! Make the production helpers reachable without copying their implementations.
const numeric = @import("numeric");

export fn to_signed(value: u64) i64 {
    return @truncate(numeric.u2s(value));
}

export fn to_unsigned(value: i64) u64 {
    return @truncate(numeric.s2u(value));
}

fn at_constant_limit(value: u64) u512 {
    return @as(u512, value) +% (@as(u512, 1) << 511);
}

fn above_constant_limit(value: u64) u513 {
    return @as(u513, value) +% (@as(u513, 1) << 512);
}

export fn constant_boundaries(value: u64) u64 {
    return @truncate(at_constant_limit(value) +% @as(u512, @truncate(above_constant_limit(value))));
}
