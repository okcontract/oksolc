// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Transitional equivalents for recurring C++ constructs.
//!
//! This module exists to preserve source correspondence during translation.
//! Native replacements must not depend on it.

pub const Vector = @import("vector.zig").Vector;
pub const OwnedString = @import("owned_string.zig").OwnedString;
pub const OrderedMap = @import("ordered_map.zig").OrderedMap;
pub const OrderedSet = @import("ordered_map.zig").OrderedSet;
pub const BigInt = @import("big_int").BigInt;

test {
    _ = @import("vector.zig");
    _ = @import("owned_string.zig");
    _ = @import("ordered_map.zig");
    _ = BigInt;
}
