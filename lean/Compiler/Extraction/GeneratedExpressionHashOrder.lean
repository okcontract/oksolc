/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
Generated from the complete captured caller call order.
Key-copy admission and update/finalization AIR refinement remain open.
-/
import Compiler.Extraction.ExpressionMapHashOrder

namespace Compiler.Extraction.ExpressionMap.GeneratedHashOrder
open Compiler.ZigAir.Memory

def inputs : List HashBytes.Ordered.Input := [some .kind, some .instruction, some .data, none, some .sequence]

/-- The captured initialization precedes every view/update pair; finalization follows them. -/
def run (state : State) (keyId : Nat) : Except Fault (BitVec 64) × State :=
  HashBytes.Ordered.run state keyId inputs

end Compiler.Extraction.ExpressionMap.GeneratedHashOrder
