/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityFunction

namespace Compiler.Validation.SolidityBytes32Literal
open Contract.Evm Contract.Interaction SolidityFunction

/-- A fixed-byte literal retains its original bytes. The untrusted generator
proposes a word; the kernel checks its complete right-padded ABI encoding.
The length check prevents truncation from becoming an admitted conversion. -/
def literal (bytes : List UInt8) (_fits : bytes.length ≤ 32) (value : Word)
    (_encoding : wordBytes value = bytes ++ List.replicate (32 - bytes.length) 0) :
    SolidityWord.Expr := .literal value.toNat

/-- No dynamic offset or length prefix: both arithmetic modes return exactly
the literal bytes followed by enough zero bytes to fill one ABI word. -/
theorem result (source : Source) (bytes : List UInt8) (fits : bytes.length ≤ 32)
    (value : Word)
    (encoding : wordBytes value = bytes ++ List.replicate (32 - bytes.length) 0)
    (body : source.body = literal bytes fits value encoding) (input : Input) :
    source.result input = .returned (bytes ++ List.replicate (32 - bytes.length) 0) := by
  simp [Source.result, Source.returnBytes, body, literal,
    SolidityWord.Expr.eval, SolidityWord.Expr.evalChecked, encoding]

end Compiler.Validation.SolidityBytes32Literal
