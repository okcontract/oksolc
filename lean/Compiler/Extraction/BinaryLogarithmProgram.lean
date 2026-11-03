/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.BinaryLogarithm

namespace Compiler.Extraction.BinaryLogarithm
open Contract.Yul

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d

def binaryLogarithm (usizeBits : Nat) (value : Word) : Except Folding.Fault (Option Nat) := do
  if value == 0 then return none
  let predecessor ← Folding.Zig.checkedSub value.toNat 1
  if value &&& BitVec.ofNat 256 predecessor != 0 then return none
  let count ← Folding.Zig.narrow usizeBits value.ctz.toNat
  return some count

end Compiler.Extraction.BinaryLogarithm
