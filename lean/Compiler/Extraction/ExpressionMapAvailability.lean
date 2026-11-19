/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapMetadataInitialization

namespace Compiler.Extraction.ExpressionMap.Local.Availability
open Compiler.ZigAir.Memory Initialization

/-- max_load_percentage is a u64 comptime parameter in the pinned map. The
native multiplication/division therefore precede the explicit u32 truncation. -/
def word (capacity : BitVec 32) : BitVec 32 :=
  ((capacity.setWidth 64 * (80 : BitVec 64)) / 100).setWidth 32

def value (capacity : BitVec 32) : Value := .scalar (.int false 32 (word capacity).toNat)

/-- Every u32 capacity has exact widened arithmetic and a lossless truncation.
This does not establish grow's positive/power-of-two capacity guards. -/
theorem word_exact (capacity : BitVec 32) :
    capacity.toNat * 80 < 2 ^ 64 ∧ (word capacity).toNat = capacity.toNat * 80 / 100 ∧
      (word capacity).toNat ≤ capacity.toNat := by
  have bounded := capacity.isLt
  have widened : (capacity.setWidth 64).toNat = capacity.toNat := BitVec.toNat_setWidth_of_le (by decide)
  have product : (capacity.setWidth 64 * (80 : BitVec 64)).toNat = capacity.toNat * 80 := by
    simp only [BitVec.toNat_mul, widened, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
    omega
  have quotient : ((capacity.setWidth 64 * (80 : BitVec 64)) / 100).toNat = capacity.toNat * 80 / 100 := by
    rw [BitVec.toNat_udiv, product]
    rfl
  have result : (word capacity).toNat = capacity.toNat * 80 / 100 := by
    simp only [word, BitVec.toNat_setWidth, quotient]
    omega
  refine ⟨by omega, result, ?_⟩
  rw [result]
  omega

theorem positive (capacity : BitVec 32) (minimum : 8 ≤ capacity.toNat) :
    0 < (word capacity).toNat ∧ (word capacity).toNat < capacity.toNat := by
  rw [(word_exact capacity).2.1]
  omega

def slot : Slot := .available

/-- The actual local field selector is checked before storing the evaluated
source value; it is not supplied by a caller or replaced by an assumed write. -/
def assign (safety : Bool) (receiver : Nat) (capacity : BitVec 32) (before : State) : Except Fault State := do
  let selected ← fieldPointer before (.pointer (.pointer true false (allocationType safety)) ⟨receiver, 0⟩)
    (slot.offset safety)
  store before selected (value capacity)

theorem initialize_verified (safety : Bool) (receiver : Nat) (capacity : BitVec 32)
    (before : State) (cell : Allocation) (valid : before.valid = true)
    (found : before.heap.lookup receiver = some cell) (typed : cell.type = allocationType safety)
    (writable : cell.writable = true) :
    ∃ after, assign safety receiver capacity before = .ok after ∧
      Stored safety receiver before after .available (value capacity) := by
  have selectedField : slot = .available := rfl
  have selected := root_fieldPointer before receiver cell (allocationType safety) (.scalar (.int false 32))
    (Placement.localMap.layout safety) (availableOffset safety) true false valid found typed
    (Placement.localMap.layout_checked safety) (by cases safety <;> decide) (by cases safety <;> rfl)
  obtain ⟨after, stored, post⟩ := store_value_verified safety before receiver cell .available (value capacity)
    rfl (Compiler.ZigAir.Memory.WordArray.number_valid (word capacity)) (by simp [Slot.Active]) valid found typed writable
  refine ⟨after, ?_, post⟩
  simpa only [assign, selectedField, Slot.offset, selected, bind, Except.bind, field] using stored

end Compiler.Extraction.ExpressionMap.Local.Availability
