/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Associative

namespace Compiler.Extraction.ShiftMasks
open Compiler.Extraction.Cache Contract.Yul

theorem power_shift_value (amount value : Word) :
    value * Folding.Op.shl.value amount 1 0 = Folding.Op.shl.value amount value 0 := by
  by_cases small : amount.toNat < 256
  · simp only [Folding.Op.value, Binary.eval, small, ↓reduceIte]
    rw [BitVec.shiftLeft_eq_mul_twoPow (1 : Word)]
    change value * (1#256 * BitVec.twoPow 256 amount.toNat) = value <<< amount.toNat
    rw [BitVec.one_mul, BitVec.mul_twoPow_eq_shiftLeft]
  · simp [Folding.Op.value, Binary.eval, small]

theorem divisor_shift_value (amount value : Word) :
    Folding.Op.div.value value (Folding.Op.shl.value amount 1 0) 0 = Folding.Op.shr.value amount value 0 := by
  by_cases small : amount.toNat < 256
  · simp only [Folding.Op.value, Binary.eval, small, ↓reduceIte]
    rw [BitVec.shiftLeft_eq_mul_twoPow (1 : Word)]
    change value / (1#256 * BitVec.twoPow 256 amount.toNat) = value >>> amount.toNat
    rw [BitVec.one_mul]
    exact BitVec.udiv_twoPow_eq_of_lt small
  · simp [Folding.Op.value, Binary.eval, small]

theorem coverage_contains (amount value : Word) :
    Folding.Op.shr.value amount (BitVec.allOnes 256) 0 &&& Folding.Op.shr.value amount value 0 =
      Folding.Op.shr.value amount value 0 := by
  by_cases small : amount.toNat < 256
  · simp only [Folding.Op.value, Binary.eval, small, ↓reduceIte]
    rw [← BitVec.ushiftRight_and_distrib, BitVec.allOnes_and]
  · simp [Folding.Op.value, Binary.eval, small]

theorem covered_mask_value (amount value mask : Word)
    (covered : mask &&& Folding.Op.shr.value amount (BitVec.allOnes 256) 0 =
      Folding.Op.shr.value amount (BitVec.allOnes 256) 0) :
    mask &&& Folding.Op.shr.value amount value 0 = Folding.Op.shr.value amount value 0 := by
  calc
    _ = mask &&& (Folding.Op.shr.value amount (BitVec.allOnes 256) 0 &&& Folding.Op.shr.value amount value 0) :=
      congrArg (mask &&& ·) (coverage_contains amount value).symm
    _ = _ := by rw [← BitVec.and_assoc, covered, coverage_contains]

end Compiler.Extraction.ShiftMasks
