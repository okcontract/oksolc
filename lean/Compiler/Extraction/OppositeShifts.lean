/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssociativeProofs

namespace Compiler.Extraction.OppositeShifts
open Compiler.Extraction.Cache Contract.Yul
set_option linter.unusedSimpArgs false

inductive Direction where
  | left | right
  deriving DecidableEq, Repr

def Direction.op : Direction → Folding.Op | .left => .shl | .right => .shr
def Direction.opposite : Direction → Direction | .left => .right | .right => .left
def Direction.shift (direction : Direction) (value : Word) (amount : Nat) : Word :=
  match direction with | .left => value <<< amount | .right => value >>> amount

private theorem bit_in_range (value : Word) (index : Nat) :
    (value.getLsbD index && decide (index < 256)) = value.getLsbD index := by
  by_cases inside : index < 256
  · simp [inside]
  · rw [BitVec.getLsbD_of_ge value index (by omega)]; rfl

/-- The mask removes the bits that the intermediate left shift discards.
The identity is unbounded in the natural shift amounts. -/
theorem right_after_left (value : Word) (outer inner : Nat) :
    (value <<< inner) >>> outer =
      (if outer < inner then value <<< (inner - outer) else value >>> (outer - inner)) &&&
        ((BitVec.allOnes 256 <<< inner) >>> outer) := by
  by_cases order : outer < inner
  · simp only [order, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
    by_cases clipped : outer + index < 256
    · by_cases low : index < inner - outer
      · have low' : outer + index < inner := by omega
        simp [bound, clipped, low, low']
      · have low' : ¬outer + index < inner := by omega
        have same : outer + index - inner = index - (inner - outer) := by omega
        have inside : outer + index - inner < 256 := by omega
        simp [bound, clipped, low, low', inside, ← same]
    · simp [clipped]
  · simp only [order, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
    have low : ¬outer + index < inner := by omega
    have same : outer + index - inner = outer - inner + index := by omega
    by_cases clipped : outer + index < 256
    · have inside : outer + index - inner < 256 := by omega
      simp [bound, clipped, low, inside, ← same]
    · simp [clipped]

/-- The mask removes the bits that the intermediate right shift discards. -/
theorem left_after_right (value : Word) (outer inner : Nat) :
    (value >>> inner) <<< outer =
      (if outer < inner then value >>> (inner - outer) else value <<< (outer - inner)) &&&
        ((BitVec.allOnes 256 >>> inner) <<< outer) := by
  by_cases order : outer < inner
  · simp only [order, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
    by_cases low : index < outer
    · simp [bound, low]
    · have same : inner + (index - outer) = inner - outer + index := by omega
      simp [bound, low, same, bit_in_range]
  · simp only [order, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro index bound
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes]
    by_cases low : index < outer
    · simp [bound, low]
    · have low' : ¬index < outer - inner := by omega
      have same : inner + (index - outer) = index - (outer - inner) := by omega
      simp [bound, low, low', same, bit_in_range]

def netShift (direction : Direction) (outer inner : Nat) (value : Word) : Word :=
  if outer < inner then direction.opposite.shift value (inner - outer)
  else if inner < outer then direction.shift value (outer - inner)
  else value

theorem masked_net (direction : Direction) (outer inner : Nat) (value : Word) :
    direction.shift (direction.opposite.shift value inner) outer =
      netShift direction outer inner value &&&
        direction.shift (direction.opposite.shift (BitVec.allOnes 256) inner) outer := by
  have equal : ¬outer < inner → ¬inner < outer → outer = inner := by omega
  cases direction <;> simp only [Direction.opposite, Direction.shift, netShift]
  · rw [left_after_right]
    split
    · rfl
    · split
      · rfl
      · have same := equal (by assumption) (by assumption)
        subst outer; simp
  · rw [right_after_left]
    split
    · rfl
    · split
      · rfl
      · have same := equal (by assumption) (by assumption)
        subst outer; simp

end Compiler.Extraction.OppositeShifts
