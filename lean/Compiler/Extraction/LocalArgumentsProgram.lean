/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerLocalArguments

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments
open Compiler.Algebraic Compiler.ZigAir.Memory.WordArray

-- Generated initializer/overwrite segment of admitted RuleList.dropRepeatedNested.
-- The selected index is computed by the retained readonly prefix before this segment.
-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def zigLocal (source : View) (selected : Nat) (repeated : NodeId) (repeatedIsFirst : Bool) : GraphAction σ View :=
  fun before => match copy source before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok target, initialized) => if repeatedIsFirst then overwrite target selected repeated initialized
      else (.ok target, initialized)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments
