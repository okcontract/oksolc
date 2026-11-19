/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.FoldingProofs
import Compiler.Extraction.CacheIR

namespace Compiler.Extraction.Folding
open Compiler.Extraction.Cache Contract.Yul

/-- Independent supported EVM vocabulary. Opcode values come from the word
specification; source-bound dispatch still has to agree with that specification. -/
def wordOperations : List Op := [
  .add, .mul, .sub, .div, .sdiv, .mod, .smod, .exp, .not, .lt, .gt, .slt, .sgt,
  .eq, .iszero, .and, .or, .xor, .byte, .addmod, .mulmod, .signextend, .shl, .shr]

def decodeWord (opcode : Opcode) : Option Op := wordOperations.find? (fun op => op.opcode == opcode)

theorem decode_word_opcode (op : Op) : decodeWord op.opcode = some op := by cases op <;> rfl

/-- Pure words ignore observation epochs. Other instructions retain their
original interpretation and sequence; unsupported arities remain undefined. -/
def wordMeaning (other : Meaning) : Meaning where
  operation := fun opcode sequence values =>
    match decodeWord opcode with
    | some op => op.eval values
    | none => other.operation opcode sequence values
  atom := other.atom

theorem word_meaning_operation (other : Meaning) (op : Op) (sequence : BitVec 32) (values : List Word) :
    (wordMeaning other).operation op.opcode sequence values = op.eval values := by
  simp [wordMeaning, decode_word_opcode]

theorem word_meaning_other (other : Meaning) (opcode : Opcode) (sequence : BitVec 32) (values : List Word)
    (unknown : decodeWord opcode = none) :
    (wordMeaning other).operation opcode sequence values = other.operation opcode sequence values := by
  simp [wordMeaning, unknown]

theorem folding_meaning (other : Meaning) (op : Op) (sequence : BitVec 32) (values : List Word) :
    run helpers clauses op.opcode values = .ok ((wordMeaning other).operation op.opcode sequence values) := by
  rw [word_meaning_operation, folding_correct]

end Compiler.Extraction.Folding
