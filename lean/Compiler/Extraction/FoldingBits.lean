/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Folding

namespace Compiler.Extraction.Folding
open Contract.Yul
set_option linter.unusedSimpArgs false

theorem highBit_toNat (bit : Nat) (bound : bit < 256) :
    ((1 : Word) <<< bit).toNat = 2 ^ bit := by
  change (1#256 <<< bit).toNat = 2 ^ bit
  rw [← BitVec.twoPow_eq]
  exact BitVec.toNat_twoPow_of_lt bound

theorem highBit_test (value : Word) (bit : Nat) (bound : bit < 256) :
    (value &&& ((1 : Word) <<< bit)) ≠ 0 ↔ value.getLsbD bit = true := by
  have nonzero : BitVec.twoPow 256 bit ≠ 0#256 := by
    intro zero
    have n := congrArg BitVec.toNat zero
    rw [BitVec.toNat_twoPow_of_lt bound] at n
    have positive := Nat.two_pow_pos bit
    simp at n
  change (value &&& (1#256 <<< bit)) ≠ 0#256 ↔ value.getLsbD bit = true
  rw [← BitVec.twoPow_eq, BitVec.and_twoPow]
  cases sign : value.getLsbD bit <;> simp [sign, nonzero]

/-- Bit-level equivalence of the native sign-bit mask algorithm and the
language model's truncation followed by signed extension. The sign bit itself
is handled separately from both the preserved low bits and the extended bits. -/
theorem signMask_correct (value : Word) (bit : Nat) (bound : bit < 256) :
    (if (value &&& ((1 : Word) <<< bit)) ≠ 0 then
      value ||| ~~~(BitVec.ofNat 256 (2 ^ bit - 1))
    else value &&& BitVec.ofNat 256 (2 ^ bit - 1)) =
      (value.setWidth (bit + 1)).signExtend 256 := by
  simp only [highBit_test value bit bound]
  apply BitVec.eq_of_getLsbD_eq
  intro index
  by_cases valid : index < 256
  · by_cases low : index < bit
    · have low' : index < bit + 1 := by omega
      cases sign : value.getLsbD bit <;>
        simp only [sign, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and,
          BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
          BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, valid, low, low',
          Nat.add_sub_cancel, sign, decide_true,
          decide_false, Bool.true_and, Bool.and_true, Bool.and_false,
          Bool.not_true, Bool.not_false, Bool.or_false, Bool.or_true] <;> simp
    · by_cases atBit : index = bit
      · subst index
        cases sign : value.getLsbD bit <;>
          simp only [sign, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and,
            BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
            BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
            BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, bound, Nat.add_sub_cancel, sign] <;> simp [sign, bound]
      · have above : ¬index < bit + 1 := by omega
        cases sign : value.getLsbD bit <;>
          simp only [sign, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and,
            BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
            BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last,
            BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, valid, low, above,
            Nat.add_sub_cancel, sign, bound, Nat.lt_add_one,
            decide_true, decide_false, Bool.true_and, Bool.and_true,
            Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.or_true] <;> simp
  · have outside : 256 ≤ index := by omega
    simp [outside]

end Compiler.Extraction.Folding
