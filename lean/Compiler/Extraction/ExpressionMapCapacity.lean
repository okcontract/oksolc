/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapReady

namespace Compiler.Extraction.ExpressionMap.Capacity
open Compiler.ZigAir.Memory

/-- Failed native casts/assertions are not allocator OOM. -/
def rejected (safety : Bool) : Fault := .scalar (if safety then .safetyPanic else .illegalBehavior)

def expanded (size : BitVec 32) : BitVec 64 := (size.setWidth 64 * 100) / 80 + 1
def exponent (value : BitVec 32) : Nat := 32 - (value - 1).clz.toNat
def promoted (value : BitVec 32) : BitVec 33 := BitVec.twoPow 33 (exponent value)
def rounded (value : BitVec 32) : BitVec 32 := (promoted value).setWidth 32
def forSizeWord (size : BitVec 32) : BitVec 32 := rounded ((expanded size).setWidth 32)

/-- The pinned ceilPowerOfTwo algorithm promotes before testing its overflow
bit. capacityForSize catches that overflow with unreachable. -/
def ceil (safety : Bool) (value : BitVec 32) : Except Fault (BitVec 32) :=
  if value = 0 then .error (rejected safety) else
  let rounded := promoted value
  if BitVec.twoPow 33 32 &&& rounded ≠ 0 then .error (rejected safety)
  else .ok (rounded.setWidth 32)

def forSize (safety : Bool) (size : BitVec 32) : Except Fault (BitVec 32) :=
  let value := expanded size
  if value.toNat ≥ 2 ^ 32 then .error (rejected safety)
  else ceil safety (value.setWidth 32)

theorem expanded_exact (size : BitVec 32) :
    (expanded size).toNat = size.toNat * 100 / 80 + 1 := by
  have bounded := size.isLt
  have widened : (size.setWidth 64).toNat = size.toNat := BitVec.toNat_setWidth_of_le (by decide)
  have product : (size.setWidth 64 * 100).toNat = size.toNat * 100 := by
    simp only [BitVec.toNat_mul, widened, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
    omega
  have quotient : ((size.setWidth 64 * 100) / 80).toNat = size.toNat * 100 / 80 := by
    rw [BitVec.toNat_udiv, product]
    rfl
  change ((((size.setWidth 64 * 100) / 80).toNat + 1) % 2 ^ 64) = _
  rw [quotient]
  omega

theorem promoted_exact (value : BitVec 32) :
    (promoted value).toNat = 2 ^ exponent value := by
  have bound : exponent value ≤ 32 := Nat.sub_le _ _
  have power := Nat.pow_lt_pow_right (a := 2) (by decide) (show exponent value < 33 by omega)
  simp only [promoted, BitVec.toNat_twoPow]
  exact Nat.mod_eq_of_lt power

theorem exponent_bound (value : BitVec 32) (positive : 0 < value.toNat)
    (bounded : value.toNat ≤ 2 ^ 31) : exponent value < 32 ∧ value.toNat ≤ 2 ^ exponent value := by
  have subtract : (value - 1).toNat = value.toNat - 1 :=
    BitVec.toNat_sub_of_le (by change (1 : BitVec 32).toNat ≤ value.toNat; simpa using positive)
  have leading := BitVec.clz_le (x := value - 1)
  change (value - 1).clz.toNat ≤ 32 at leading
  have nonzero : (value - 1).clz.toNat ≠ 0 := by
    intro zero
    have lower := (BitVec.clz_eq_zero_iff (x := value - 1) (by decide)).mp zero
    rw [subtract] at lower
    omega
  have upper := BitVec.toNat_lt_two_pow_sub_clz (x := value - 1)
  rw [subtract] at upper
  change value.toNat - 1 < 2 ^ exponent value at upper
  exact ⟨by change 32 - (value - 1).clz.toNat < 32; omega, by omega⟩

theorem ceil_verified (safety : Bool) (value : BitVec 32) (positive : 0 < value.toNat)
    (bounded : value.toNat ≤ 2 ^ 31) :
    ceil safety value = .ok (rounded value) ∧ (rounded value).toNat = 2 ^ exponent value ∧
      value.toNat ≤ (rounded value).toNat ∧ 0 < (rounded value).toNat ∧ (rounded value).toNat ≤ 2 ^ 31 := by
  obtain ⟨shift, covers⟩ := exponent_bound value positive bounded
  have power := Nat.pow_le_pow_right (n := 2) (by decide) (show exponent value ≤ 31 by omega)
  have noOverflow : BitVec.twoPow 33 32 &&& promoted value = 0 := by
    rw [BitVec.twoPow_and]
    simp [promoted, show 32 ≠ exponent value by omega]
  have exactCast : ((promoted value).setWidth 32).toNat = 2 ^ exponent value := by
    rw [BitVec.toNat_setWidth, promoted_exact]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, exactCast, ?_, ?_, ?_⟩
  · simp only [ceil, rounded, show value ≠ 0 from by intro zero; subst value; contradiction,
      ↓reduceIte, noOverflow, ne_self_iff_false]
  all_goals unfold rounded; rw [exactCast]; omega

/-- This bound is the complete ordinary input range of the pinned u32
capacityForSize: the next power of two must still fit in 32 bits. -/
def maximumSize : Nat := 1717986918

theorem for_size_verified (safety : Bool) (size : BitVec 32) (bounded : size.toNat ≤ maximumSize) :
    forSize safety size = .ok (forSizeWord size) ∧
      size.toNat * 100 / 80 + 1 ≤ (forSizeWord size).toNat ∧ 0 < (forSizeWord size).toNat ∧
      (forSizeWord size).toNat ≤ 2 ^ 31 ∧ ∃ shift < 32, (forSizeWord size).toNat = 2 ^ shift := by
  have expandedEq := expanded_exact size
  have range : 0 < (expanded size).toNat ∧ (expanded size).toNat ≤ 2 ^ 31 := by
    dsimp [maximumSize] at bounded
    omega
  have cast : ((expanded size).setWidth 32).toNat = (expanded size).toNat := by
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨ran, power, covers, positive, bound⟩ := ceil_verified safety ((expanded size).setWidth 32)
    (by omega) (by omega)
  refine ⟨?_, by change _ ≤ (rounded _).toNat; omega, positive, bound,
    exponent ((expanded size).setWidth 32), (exponent_bound _ (by omega) (by omega)).1, power⟩
  simp only [forSize, forSizeWord, show ¬(expanded size).toNat ≥ 2 ^ 32 from by omega, ↓reduceIte, ran]

theorem ceil_rejected (safety : Bool) (value : BitVec 32) (large : 2 ^ 31 < value.toNat) :
    ceil safety value = .error (rejected safety) := by
  have subtract : (value - 1).toNat = value.toNat - 1 := BitVec.toNat_sub_of_le (by change 1 ≤ value.toNat; omega)
  have leading : (value - 1).clz.toNat = 0 := (BitVec.clz_eq_zero_iff (by decide)).mpr (by rw [subtract]; omega)
  have selected : promoted value = BitVec.twoPow 33 32 := by simp only [promoted, exponent, leading, Nat.sub_zero]
  simp only [ceil, show value ≠ 0 from by intro zero; subst value; contradiction,
    ↓reduceIte, selected]
  rfl

theorem for_size_rejected (safety : Bool) (size : BitVec 32) (large : maximumSize < size.toNat) :
    forSize safety size = .error (rejected safety) := by
  have exactWord := expanded_exact size
  simp only [forSize]
  split
  · rfl
  · rename_i fits
    have cast : ((expanded size).setWidth 32).toNat = (expanded size).toNat := by
      rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
    apply ceil_rejected
    dsimp [maximumSize] at large
    omega

def growWord (capacity : BitVec 32) : BitVec 32 := if capacity.toNat < 8 then 8 else capacity
def powerGuard (capacity : BitVec 32) : Bool := capacity &&& (capacity - 1) == 0

theorem power_guard (capacity : BitVec 32) (power : ∃ shift < 32, capacity.toNat = 2 ^ shift) :
    powerGuard capacity = true := by
  obtain ⟨shift, bound, exactWord⟩ := power
  have same : capacity = BitVec.twoPow 32 shift := BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) bound)]; exact exactWord)
  rw [same]
  have checked : ∀ shift : Fin 32, powerGuard (BitVec.twoPow 32 shift.val) = true := by decide +kernel
  exact checked ⟨shift, bound⟩

theorem grow_word (capacity : BitVec 32) :
    8 ≤ (growWord capacity).toNat ∧ capacity.toNat ≤ (growWord capacity).toNat ∧
      (powerGuard capacity = true → powerGuard (growWord capacity) = true) := by
  unfold growWord
  split
  · constructor
    · decide
    constructor
    · change capacity.toNat ≤ 8; omega
    · intro _; decide
  · exact ⟨by omega, Nat.le_refl _, id⟩

def loadWord (capacity available : BitVec 32) : BitVec 32 := Local.Availability.word capacity - available
def target (capacity available additional : BitVec 32) : BitVec 32 :=
  growWord (forSizeWord (loadWord capacity available + additional))

/-- growIfNeeded's words and grow's entry guards. The memory caller below
supplies these words by actual checked reads, not a chosen allocation size. -/
def select (safety : Bool) (capacity available additional : BitVec 32) : Except Fault (Option (BitVec 32)) := do
  if additional.toNat ≤ available.toNat then return none
  let maximum := Local.Availability.word capacity
  if maximum.toNat < available.toNat then .error (rejected safety) else do
  let count := maximum - available
  if count.toNat + additional.toNat ≥ 2 ^ 32 then .error (rejected safety) else do
  let selected ← forSize safety (count + additional)
  let selected := growWord selected
  if selected.toNat ≤ capacity.toNat then .error (rejected safety) else
  if !powerGuard selected then .error (rejected safety) else .ok (some selected)

theorem select_room (safety : Bool) (capacity available additional : BitVec 32)
    (room : additional.toNat ≤ available.toNat) : select safety capacity available additional = .ok none := by
  simp only [select, room, ↓reduceIte, pure, Except.pure]

theorem select_growth (safety : Bool) (capacity available additional : BitVec 32)
    (countdown : available.toNat ≤ (Local.Availability.word capacity).toNat)
    (needed : available.toNat < additional.toNat)
    (bounded : (Local.Availability.word capacity).toNat - available.toNat + additional.toNat ≤ maximumSize) :
    select safety capacity available additional = .ok (some (target capacity available additional)) ∧
      8 ≤ (target capacity available additional).toNat ∧
      capacity.toNat < (target capacity available additional).toNat ∧
      powerGuard (target capacity available additional) = true := by
  have loadExact : (loadWord capacity available).toNat = (Local.Availability.word capacity).toNat - available.toNat :=
    BitVec.toNat_sub_of_le (by exact countdown)
  have totalExact : (loadWord capacity available + additional).toNat =
      (Local.Availability.word capacity).toNat - available.toNat + additional.toNat := by
    rw [BitVec.toNat_add, loadExact]
    exact Nat.mod_eq_of_lt (by dsimp [maximumSize] at bounded; omega)
  obtain ⟨ran, covers, positive, _, power⟩ := for_size_verified safety (loadWord capacity available + additional) (by omega)
  obtain ⟨minimum, widened, guard⟩ := grow_word (forSizeWord (loadWord capacity available + additional))
  have availableExact := (Local.Availability.word_exact capacity).2.1
  have grows : capacity.toNat < (target capacity available additional).toNat := by
    change capacity.toNat < (growWord _).toNat
    omega
  have guarded := guard (power_guard _ power)
  refine ⟨?_, minimum, grows, guarded⟩
  have noOverflow : ¬(loadWord capacity available).toNat + additional.toNat ≥ 2 ^ 32 := by
    dsimp [maximumSize] at bounded; omega
  simp only [loadWord] at ran guarded
  simp only [select, show ¬additional.toNat ≤ available.toNat from by omega, ↓reduceIte,
    show ¬(Local.Availability.word capacity).toNat < available.toNat from by omega]
  change (if (loadWord capacity available).toNat + additional.toNat ≥ 2 ^ 32 then _ else _) = _
  simp only [noOverflow, ↓reduceIte, ran, bind, Except.bind]
  change (if (target capacity available additional).toNat ≤ capacity.toNat then _ else _) = _
  rw [if_neg (show ¬(target capacity available additional).toNat ≤ capacity.toNat from by omega)]
  rw [guarded]
  rfl

end Compiler.Extraction.ExpressionMap.Capacity
