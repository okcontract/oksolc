/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRecordFields

namespace Compiler.ZigAir.Memory

/-- A positive aligned field region inside an already checked descriptor uses
the same allocation and permission. Native representative writes need this
derivation in addition to successful selection of the descriptor's fields. -/
theorem access_subregion (state : State) (address : Address) (parent child : Layout)
    (offset : Nat) (write : Bool) (cell : Allocation)
    (accessed : access state address parent write = .ok cell)
    (positive : 0 < child.bytes) (inside : offset + child.bytes ≤ parent.bytes)
    (aligned : offset % child.alignment = 0) (divided : parent.alignment % child.alignment = 0) :
    access state ⟨address.allocation, address.offset + offset⟩ child write = .ok cell := by
  obtain ⟨found, region, shaped, basePositive, bounded, _, parentBound, parentAligned, permitted⟩ :=
    access_success_region state address parent write cell accessed
  have childAligned : (cell.base + (address.offset + offset)) % child.alignment = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    rw [← Nat.add_assoc]
    exact Nat.dvd_add (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero divided) (Nat.dvd_of_mod_eq_zero parentAligned))
      (Nat.dvd_of_mod_eq_zero aligned)
  have checks : ¬(cell.base = 0 ∨ cell.base + region.bytes > addressLimit ∨
      cell.base + (address.offset + offset) ≥ addressLimit ∨
      address.offset + offset + child.bytes > region.bytes ∨
      (cell.base + (address.offset + offset)) % child.alignment ≠ 0) := by omega
  cases write <;>
    simp only [access, found, shaped, Bool.false_and, Bool.false_eq_true, ↓reduceIte, if_neg checks]
  simp only [permitted rfl, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

theorem Value.leaves_shift (value : Value) (offset : Nat) :
    value.leaves offset = (value.leaves 0).map (fun entry => (offset + entry.1, entry.2)) := by
  cases value with
  | scalar value | optionalScalar _ value | optionalObject _ _ value => simp [Value.leaves]
  | pointer type address => simp [Value.leaves]
  | slice type address length => cases type <;> simp [Value.leaves]

theorem Value.leaves_atomic (value : Value) (valid : value.valid = true)
    (atomic : leafType value.type 0 = some value.type) : value.leaves 0 = [(0, value)] := by
  cases value with
  | scalar | optionalScalar | optionalObject | pointer => rfl
  | slice type address length =>
    cases type <;> simp_all [Value.valid, Value.type, leafType, sliceFieldType]

/-- Typed subobject initialization uses the existing leaf writer. Contents and
leaf validity follow from the actual valid value and declared field geometry;
there is no successful-store or initialized-destination premise. -/
theorem Cells.write_subobject_total (cells : Cells) (owner : Ty) (offset : Nat) (value : Value)
    (valid : value.valid = true) (view : acceptsView owner offset value.type = true)
    (declared : ∀ entry ∈ value.leaves 0, leafType owner (offset + entry.1) = some entry.2.type) :
    ∃ contents, cells.write owner offset value = .ok contents := by
  obtain ⟨root, initialized⟩ := Cells.write_root [] value valid
  have fits := (Cells.write_success [] value.type 0 value root initialized).2.2.1
  have shifted : (value.leaves offset).all (leafFits owner) = true := by
    rw [value.leaves_shift, List.all_map]
    apply List.all_eq_true.mpr
    intro entry present
    have rootFit := List.all_eq_true.mp fits entry present
    simp only [leafFits, Bool.and_eq_true] at rootFit
    change leafFits owner (offset + entry.1, entry.2) = true
    simp only [leafFits, declared entry present, decide_true, Bool.true_and]
    exact rootFit.2
  simp only [Cells.write, valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, view, shifted]
  exact ⟨_, rfl⟩

/-- A valid evaluated value initializes its checked declared region in the same
heap. Bounds, permission and leaf typing remain separate obligations; neither
initialized contents nor a successful write is assumed. -/
theorem store_subobject_total (state : State) (address : Address) (layout : Layout) (cell : Allocation) (value : Value)
    (valid : value.valid = true) (shaped : value.type.layout = some layout)
    (accessed : access state address layout true = .ok cell)
    (view : acceptsView cell.type address.offset value.type = true)
    (declared : ∀ entry ∈ value.leaves 0, leafType cell.type (address.offset + entry.1) = some entry.2.type) :
    ∃ after, store state (.pointer (.pointer true false value.type) address) value = .ok after := by
  obtain ⟨contents, written⟩ := Cells.write_subobject_total cell.cells cell.type address.offset value valid view declared
  exact ⟨_, store_of_access state value.type address layout cell contents value
    (by simpa only [Value.hasType, decide_true, Bool.true_and] using valid) shaped accessed written⟩

end Compiler.ZigAir.Memory
