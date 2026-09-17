// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! Structural translation of `libsolutil/StackTooDeepString.h`.

const std = @import("std");

pub const stack_too_deep_string =
    "Stack too deep. " ++
    "Try compiling with `--via-ir` (cli) or the equivalent `viaIR: true` (standard JSON) " ++
    "while enabling the optimizer. Otherwise, try removing local variables.";

test "stack-too-deep guidance preserves exact bytes" {
    try std.testing.expectEqualStrings(
        "Stack too deep. Try compiling with `--via-ir` (cli) or the equivalent " ++
            "`viaIR: true` (standard JSON) while enabling the optimizer. " ++
            "Otherwise, try removing local variables.",
        stack_too_deep_string,
    );
}
