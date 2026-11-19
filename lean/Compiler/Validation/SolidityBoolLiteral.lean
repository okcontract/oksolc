/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityFunction

namespace Compiler.Validation.SolidityBoolLiteral
open Contract.Evm Contract.Interaction SolidityFunction

/-- Source boolean literals have exactly two values. No integer truthiness or
boolean parameter decoding is added to the admitted contract language. -/
def literal (value : Bool) : SolidityWord.Expr := .literal value.toNat

/-- The ABI result is one complete word containing exactly zero or one, in
either arithmetic mode. Other nonzero values are not boolean encodings. -/
theorem result (source : Source) (value : Bool)
    (body : source.body = literal value) (input : Input) :
    source.result input = .returned (wordBytes (if value then 1 else 0)) := by
  cases value <;> simp [Source.result, Source.returnBytes, body, literal,
    SolidityWord.Expr.eval, SolidityWord.Expr.evalChecked]

end Compiler.Validation.SolidityBoolLiteral
