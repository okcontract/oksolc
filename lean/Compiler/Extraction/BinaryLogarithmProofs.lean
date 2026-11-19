/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.BinaryLogarithmProgram

namespace Compiler.Extraction.BinaryLogarithm
open Contract.Yul
set_option linter.unusedSimpArgs false

private theorem pure_ok (value : α) : (pure value : Except Folding.Fault α) = .ok value := rfl
private theorem bind_ok (value : α) (next : α → Except Folding.Fault β) :
    ((.ok value : Except Folding.Fault α) >>= next) = next value := rfl
attribute [local simp] pure_ok bind_ok

theorem zero_rejected (usizeBits : Nat) : binaryLogarithm usizeBits 0 = .ok none := by
  simp [binaryLogarithm]

theorem native_correct (usizeBits : Nat) (platform : 8 ≤ usizeBits) (value : Word) :
    binaryLogarithm usizeBits value = .ok
      (if value = 0 ∨ value &&& (value - 1) ≠ 0 then none else some value.ctz.toNat) := by
  by_cases zero : value = 0
  · subst value
    simp [binaryLogarithm]
  · have positive : 1 ≤ value.toNat := by
      have nonzero : value.toNat ≠ 0 := by
        intro equality
        exact zero (BitVec.eq_of_toNat_eq equality)
      omega
    have subtraction : (value - 1).toNat = value.toNat - 1 := by
      apply BitVec.toNat_sub_of_not_usubOverflow
      simp [BitVec.usubOverflow]; omega
    have predecessor : BitVec.ofNat 256 (value.toNat - 1) = value - 1 := by
      simp only [← subtraction, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have cast : value.ctz.toNat < 2 ^ usizeBits :=
      Nat.lt_of_lt_of_le (ctz_bound value zero) (Nat.pow_le_pow_right (by decide : 0 < 2) platform)
    simp only [binaryLogarithm, beq_iff_eq, zero, ↓reduceIte, Folding.Zig.checkedSub,
      positive, bind_ok, predecessor, Folding.Zig.narrow, cast, pure_ok, false_or]
    simp only [bne_iff_ne, apply_ite]
    split <;> rename_i h <;> simp only [h, ↓reduceIte]

/-- A successful result is exact even on a hypothetical narrow usize target.
The width bound in `found_iff` is needed for total recognition, not soundness;
a failed checked narrowing is still an explicit native fault. -/
theorem found_sound (usizeBits : Nat) (value : Word) (power : Nat)
    (found : binaryLogarithm usizeBits value = .ok (some power)) : IsPower value power := by
  have nonzero : value ≠ 0 := by
    intro zero
    simp [zero, binaryLogarithm] at found
  have positive : 1 ≤ value.toNat := by
    have nonzeroNat : value.toNat ≠ 0 := fun equal => nonzero (BitVec.eq_of_toNat_eq equal)
    omega
  have subtraction : (value - 1).toNat = value.toNat - 1 := by
    apply BitVec.toNat_sub_of_not_usubOverflow
    simp [BitVec.usubOverflow]; omega
  have predecessor : BitVec.ofNat 256 (value.toNat - 1) = value - 1 := by
    simp only [← subtraction, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [binaryLogarithm, beq_iff_eq, nonzero, ↓reduceIte, Folding.Zig.checkedSub,
    positive, bind_ok, predecessor] at found
  by_cases cleared : value &&& (value - 1) = 0
  · simp only [cleared, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
      Folding.Zig.narrow] at found
    split at found
    next =>
      have count : value.ctz.toNat = power := Option.some.inj (Except.ok.inj found)
      obtain ⟨actual, exactPower⟩ := (word_clear value nonzero).mp cleared
      have same : actual = power := (ctz_power value actual exactPower).symm.trans count
      simpa only [same] using exactPower
    next =>
      change (Except.error Folding.Fault.invalidCast : Except Folding.Fault (Option Nat)) = .ok (some power) at found
      cases found
  · have different : (value &&& (value - 1) != 0) = true := by simpa only [bne_iff_ne] using cleared
    simp only [different, ↓reduceIte, pure_ok] at found
    cases Except.ok.inj found

theorem found_shift_value (usizeBits : Nat) (constant : Word) (power : Nat)
    (found : binaryLogarithm usizeBits constant = .ok (some power)) :
    Folding.Op.shl.value (BitVec.ofNat 256 power) 1 0 = constant := by
  obtain ⟨bound, exactPower⟩ := found_sound usizeBits constant power found
  have wordBound : power < 2 ^ 256 := by omega
  simp only [Folding.Op.value, Binary.eval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound, bound, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  rw [Folding.highBit_toNat power bound, exactPower]

/-- Exact recognition, in both directions, for every u256 input. The explicit
platform bound suffices for usize on all usual native compiler targets. -/
theorem found_iff (usizeBits : Nat) (platform : 8 ≤ usizeBits) (value : Word) (power : Nat) :
    binaryLogarithm usizeBits value = .ok (some power) ↔ IsPower value power := by
  constructor
  · exact found_sound usizeBits value power
  · intro exactPower
    rw [native_correct usizeBits platform value]
    have nonzero := power_nonzero value power exactPower
    have cleared := (word_clear value nonzero).mpr ⟨power, exactPower⟩
    simp only [nonzero, cleared, ne_eq, not_true_eq_false, false_or, ↓reduceIte,
      ctz_power value power exactPower]

theorem none_iff (usizeBits : Nat) (platform : 8 ≤ usizeBits) (value : Word) :
    binaryLogarithm usizeBits value = .ok none ↔ ¬ ∃ power, IsPower value power := by
  constructor
  · intro rejected ⟨power, exactPower⟩
    have accepted := (found_iff usizeBits platform value power).mpr exactPower
    rw [rejected] at accepted
    cases Except.ok.inj accepted
  · intro noPower
    rw [native_correct usizeBits platform value]
    split
    next => rfl
    next admitted =>
      have nonzero : value ≠ 0 := fun h => admitted (Or.inl h)
      have cleared : value &&& (value - 1) = 0 := by
        by_cases h : value &&& (value - 1) = 0
        · exact h
        · exact False.elim (admitted (Or.inr h))
      exact False.elim (noPower ((word_clear value nonzero).mp cleared))

theorem result_exact (usizeBits : Nat) (platform : 8 ≤ usizeBits) (value : Word) (power : Nat)
    (found : binaryLogarithm usizeBits value = .ok (some power)) :
    power < 256 ∧ value = (1 : Word) <<< power := by
  obtain ⟨bound, same⟩ := (found_iff usizeBits platform value power).mp found
  refine ⟨bound, BitVec.eq_of_toNat_eq ?_⟩
  rw [Folding.highBit_toNat power bound, same]

end Compiler.Extraction.BinaryLogarithm
