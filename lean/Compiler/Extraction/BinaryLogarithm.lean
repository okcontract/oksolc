/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.FoldingProofs

namespace Compiler.Extraction.BinaryLogarithm
open Contract.Yul

theorem clear_lowest_bit (value : Nat) (positive : 0 < value) :
    value &&& (value - 1) = 0 ↔ ∃ power, value = 2 ^ power := by
  constructor
  · intro cleared
    induction value using Nat.strongRecOn with
    | ind value ih =>
      have halves := congrArg (· / 2) cleared
      change (value &&& (value - 1)) / 2 = 0 at halves
      rw [Nat.and_div_two] at halves
      rcases Nat.mod_two_eq_zero_or_one value with even | odd
      · have pred : (value - 1) / 2 = value / 2 - 1 := by omega
        have smaller : value / 2 < value := by omega
        have nonzero : 0 < value / 2 := by omega
        rw [pred] at halves
        obtain ⟨power, same⟩ := ih (value / 2) smaller nonzero halves
        refine ⟨power + 1, ?_⟩
        rw [Nat.pow_succ, ← same]
        omega
      · have pred : (value - 1) / 2 = value / 2 := by omega
        rw [pred, Nat.and_self] at halves
        exact ⟨0, by simp; omega⟩
  · rintro ⟨power, rfl⟩
    simp

def IsPower (value : Word) (power : Nat) : Prop :=
  power < 256 ∧ value.toNat = 2 ^ power

theorem power_nonzero (value : Word) (power : Nat) (exactPower : IsPower value power) : value ≠ 0 := by
  intro zero
  have same := exactPower.2
  rw [zero] at same
  have positive := Nat.two_pow_pos power
  change 0 = 2 ^ power at same
  omega

theorem word_clear (value : Word) (nonzero : value ≠ 0) :
    value &&& (value - 1) = 0 ↔ ∃ power, IsPower value power := by
  have positive : 0 < value.toNat := by
    have : value.toNat ≠ 0 := by
      intro zero
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      exact zero
    omega
  have subtraction : (value - 1).toNat = value.toNat - 1 := by
    apply BitVec.toNat_sub_of_not_usubOverflow
    simp [BitVec.usubOverflow]; omega
  rw [← BitVec.toNat_inj, BitVec.toNat_and, subtraction]
  change value.toNat &&& (value.toNat - 1) = 0 ↔ _
  rw [clear_lowest_bit value.toNat positive]
  constructor
  · rintro ⟨power, same⟩
    refine ⟨power, ?_, same⟩
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (same ▸ value.isLt)
  · rintro ⟨power, _, same⟩
    exact ⟨power, same⟩

theorem ctz_bound (value : Word) (nonzero : value ≠ 0) : value.ctz.toNat < 256 := by
  have bound := BitVec.ctz_lt_iff_ne_zero.mpr nonzero
  simpa [BitVec.lt_def] using bound

theorem ctz_power (value : Word) (power : Nat) (exactPower : IsPower value power) :
    value.ctz.toNat = power := by
  have bit := BitVec.getLsbD_true_ctz_of_ne_zero (power_nonzero value power exactPower)
  change value.toNat.testBit value.ctz.toNat = true at bit
  rw [exactPower.2, Nat.testBit_two_pow] at bit
  exact (of_decide_eq_true bit).symm

end Compiler.Extraction.BinaryLogarithm
