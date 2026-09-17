// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2014-2026 The Solidity Authors.
// Copyright (C) 2026 OKcontract Pte. Ltd.

//! First-match simplification facade for `SimplificationRules.cpp`.
//!
//! Pattern capture is represented by stable expression IDs in Zig. The full
//! ordered evaluator lives in `RuleList.zig` and is shared with
//! `ExpressionClasses.zig`.

const RuleList = @import("rule_list.zig");

pub const ExpressionId = RuleList.ExpressionId;
pub const binaryLogarithm = RuleList.binaryLogarithm;
pub const simplify = RuleList.simplify;

pub const Rules = struct {
    pub fn isInitialized(_: Rules) bool {
        return true;
    }
};
