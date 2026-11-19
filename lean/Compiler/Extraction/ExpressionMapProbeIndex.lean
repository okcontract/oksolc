/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCandidate

namespace Compiler.Extraction.ExpressionMap.Probe

/-- Native capacity geometry, independently of table contents or search success. -/
def Power (capacity : BitVec 32) : Prop := ∃ shift, capacity.toNat = 2 ^ shift
def mask (capacity : BitVec 32) : BitVec 64 := (capacity - 1).setWidth 64
def fingerprint (hash : BitVec 64) : BitVec 7 := (hash >>> 57).setWidth 7
def start (capacity : BitVec 32) (hash : BitVec 64) : Nat := (hash &&& mask capacity).toNat
def advance (capacity : BitVec 32) (index : Nat) : Nat :=
  ((BitVec.ofNat 64 index + 1) &&& mask capacity).toNat

/-- A proof coordinate for the source's masked walk, not another runtime scan. -/
def slot (capacity : BitVec 32) (hash : BitVec 64) (distance : Nat) : Nat :=
  (start capacity hash + distance) % capacity.toNat

theorem Power.positive (power : Power capacity) : 0 < capacity.toNat := by
  obtain ⟨shift, exact⟩ := power
  rw [exact]; exact Nat.two_pow_pos shift

theorem mask_exact (capacity : BitVec 32) (positive : 0 < capacity.toNat) :
    (mask capacity).toNat = capacity.toNat - 1 := by
  rw [mask, BitVec.toNat_setWidth_of_le (by decide), BitVec.toNat_sub]
  have bound := capacity.isLt
  have one : (1 : BitVec 32).toNat = 1 := by decide
  rw [one]
  omega

theorem start_exact (capacity : BitVec 32) (hash : BitVec 64) (power : Power capacity) :
    start capacity hash = hash.toNat % capacity.toNat := by
  rw [start, BitVec.toNat_and, mask_exact capacity power.positive]
  obtain ⟨shift, exact⟩ := power
  rw [exact, Nat.and_two_pow_sub_one_eq_mod]

theorem advance_exact (capacity : BitVec 32) (index : Nat) (power : Power capacity)
    (inside : index < capacity.toNat) : advance capacity index = (index + 1) % capacity.toNat := by
  have bound := capacity.isLt
  have fits : index < 2 ^ 64 := by omega
  have step : index + 1 < 2 ^ 64 := by omega
  rw [advance, BitVec.toNat_and, mask_exact capacity power.positive, BitVec.toNat_add]
  have one : (1 : BitVec 64).toNat = 1 := by decide
  rw [one]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, Nat.mod_eq_of_lt step]
  obtain ⟨shift, exact⟩ := power
  rw [exact, Nat.and_two_pow_sub_one_eq_mod]

variable {capacity : BitVec 32} {hash : BitVec 64}

theorem start_bound (power : Power capacity) : start capacity hash < capacity.toNat := by
  rw [start_exact capacity hash power]; exact Nat.mod_lt _ power.positive

theorem slot_bound (power : Power capacity) : slot capacity hash distance < capacity.toNat :=
  Nat.mod_lt _ power.positive

theorem slot_zero (power : Power capacity) : slot capacity hash 0 = start capacity hash := by
  simp only [slot, Nat.add_zero, Nat.mod_eq_of_lt (start_bound power)]

theorem slot_next (power : Power capacity) : advance capacity (slot capacity hash distance) = slot capacity hash (distance + 1) := by
  rw [advance_exact capacity _ power (slot_bound power)]
  simp only [slot]
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem slot_split (power : Power capacity) (inside : distance < capacity.toNat) :
    slot capacity hash distance = if start capacity hash + distance < capacity.toNat then
      start capacity hash + distance else start capacity hash + distance - capacity.toNat := by
  have base := start_bound (hash := hash) power
  unfold slot
  split
  · rename_i small; exact Nat.mod_eq_of_lt small
  · rename_i large
    rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)

theorem slot_covers (power : Power capacity) (inside : index < capacity.toNat) :
    ∃ distance, distance < capacity.toNat ∧ slot capacity hash distance = index := by
  have base := start_bound (hash := hash) power
  by_cases before : start capacity hash ≤ index
  · refine ⟨index - start capacity hash, by omega, ?_⟩
    rw [slot_split power (by omega), if_pos (by omega)]
    omega
  · refine ⟨capacity.toNat + index - start capacity hash, by omega, ?_⟩
    rw [slot_split power (by omega), if_neg (by omega)]
    omega

end Compiler.Extraction.ExpressionMap.Probe
