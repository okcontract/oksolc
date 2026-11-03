/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedConstruction

namespace Compiler.Extraction.ArithmeticShift
open Compiler.Extraction.Cache Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul
set_option linter.unusedSimpArgs false

def opcode : Opcode := 0x1d

/-- EIP-145 SAR: unsigned amount, signed value and sign fill. The large-amount
guard also keeps concrete evaluation bounded for arbitrary 256-bit amounts.
https://eips.ethereum.org/EIPS/eip-145#0x1d-sar-arithmetic-shift-right -/
def value (amount word : Word) : Word :=
  if amount.toNat < 256 then word.sshiftRight amount.toNat
  else if word.msb then BitVec.allOnes 256 else 0

theorem value_nat (amount word : Word) : value amount word = word.sshiftRight amount.toNat := by
  by_cases small : amount.toNat < 256
  · simp [value, small]
  · have large : 256 ≤ amount.toNat := by omega
    cases sign : word.msb
    · simp [value, small, BitVec.sshiftRight_eq_of_msb_false sign, BitVec.ushiftRight_eq_zero large, sign]
    · simp [value, small, BitVec.sshiftRight_eq_of_msb_true sign, BitVec.ushiftRight_eq_zero large, sign]

theorem value_signed_floor (amount word : Word) :
    value amount word = BitVec.ofInt 256 (word.toInt / (2 ^ amount.toNat : Nat)) := by
  rw [value_nat, BitVec.sshiftRight_eq, Int.shiftRight_eq_div_pow]

theorem value_large (amount word : Word) (large : 256 ≤ amount.toNat) :
    value amount word = if word.msb then BitVec.allOnes 256 else 0 := by
  simp [value, show ¬amount.toNat < 256 by omega]

def eval : List Word → Option Word
  | [amount, word] => some (value amount word)
  | _ => none

/-- SAR is separate from the native constant folder's admitted opcode set.
Other operations retain their original interpretation and observation epoch. -/
def shiftMeaning (other : Meaning) : Meaning where
  operation := fun instruction sequence values =>
    if instruction == opcode then eval values else other.operation instruction sequence values
  atom := other.atom

def meaning (other : Meaning) : Meaning := Folding.wordMeaning (shiftMeaning other)

theorem operation (other : Meaning) (sequence : BitVec 32) (values : List Word) :
    (meaning other).operation opcode sequence values = eval values := rfl

theorem other_operation (other : Meaning) (instruction : Opcode) (sequence : BitVec 32) (values : List Word)
    (notWord : Folding.decodeWord instruction = none) (notShift : instruction ≠ opcode) :
    (meaning other).operation instruction sequence values = other.operation instruction sequence values := by
  simp [meaning, Folding.wordMeaning, notWord, shiftMeaning, notShift]

def Constructs (other : Meaning) (build : OperationBuilder Debug) : Prop :=
  ∀ left right amount word debug before, Invariant (meaning other) before →
    before.read left = some amount → before.read right = some word →
    Safe (meaning other) (build opcode [left, right] debug) before
      (fun id after => after.read id = some (value amount word))

theorem interner_constructs (other : Meaning) (p : Primitives) (contracts : Contracts (meaning other) p) :
    Constructs other (internerBuilder p : OperationBuilder Debug) := by
  intro left right amount word debug before valid lhs rhs
  apply find_safe (meaning other) p contracts _ before _ valid
  simpa [constructorCode, ConstructorCode.operationRequest, Scalar.run, Item.eval,
    readArguments, lhs, rhs, eval] using operation other 0 [amount, word]

end Compiler.Extraction.ArithmeticShift
