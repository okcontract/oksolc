/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityFunction

namespace Compiler.Validation.SolidityAddressLiteral
open Contract.Evm Contract.Interaction SolidityFunction

/-- A literal address is admitted only with its range checked by the kernel.
The existing word expression then carries its numeric value without truncation. -/
def literal (value : Nat) (_bounded : value < 2^160) : SolidityWord.Expr :=
  .literal value

/-- The complete return value is the 160-bit address zero-extended to one ABI
word, in both arithmetic modes. No narrower encoding or wraparound is assumed. -/
theorem result (source : Source) (value : Nat) (bounded : value < 2^160)
    (body : source.body = literal value bounded) (input : Input) :
    source.result input = .returned (wordBytes ((BitVec.ofNat 160 value).setWidth 256)) := by
  rw [BitVec.setWidth_ofNat_of_le_of_lt (by decide : 160 ≤ 256) bounded]
  simp [Source.result, Source.returnBytes, body, literal,
    SolidityWord.Expr.eval, SolidityWord.Expr.evalChecked]

end Compiler.Validation.SolidityAddressLiteral
