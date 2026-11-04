/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from captured AIR instructions 4, 5, 6; do not edit.
This is a caller fragment, not a complete hash-function translation.
-/
import Compiler.ZigAir.AggregateCall
import Compiler.ZigAir.GeneratedWyhashInit

namespace Compiler.ZigAir.GeneratedExpressionHashInit

def fragment (next : AggregateCall.Code) : AggregateCall.Code :=
  AggregateCall.allocateCallStore 4 5 6 GeneratedWyhashInit.fn_init
    [(.constant (.value (.scalar (.int false 64 (0)))))] next

end Compiler.ZigAir.GeneratedExpressionHashInit
