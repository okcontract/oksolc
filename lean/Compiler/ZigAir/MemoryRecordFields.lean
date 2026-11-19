/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryPointers
import Compiler.ZigAir.MemorySlots

namespace Compiler.ZigAir.Memory

/-- Every admitted field has a positive extent inside the parent and an
alignment dividing its parent's alignment. These facts come from admission,
not an assumed successful field load. Nested fields retain their complete type. -/
theorem Ty.aggregate_member_geometry (layout : Layout) (fields : List (Nat × Field))
    (base : Nat) (field : Field) (accepted : Ty.aggregateValid layout fields = true)
    (member : (base, field) ∈ fields) :
    ∃ region, field.type.layout = some region ∧ 0 < region.bytes ∧
      base + region.bytes ≤ layout.bytes ∧ base % region.alignment = 0 ∧
      layout.alignment % region.alignment = 0 := by
  simp only [Ty.aggregateValid, checkFields, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have resolved : (base, field.layout) ∈ Field.layouts fields := by
    rw [Field.layouts_eq_map]
    exact List.mem_map_of_mem member
  have checked := List.all_eq_true.mp accepted.1.2 (base, field.layout) resolved
  dsimp only at checked
  cases shaped : field.layout with
  | none => simp only [shaped, Bool.false_eq_true] at checked
  | some region =>
    simp only [shaped, decide_eq_true_eq] at checked
    exact ⟨region, field.layout_eq_type.symm.trans shaped, checked⟩

theorem Ty.aggregate_disjoint (layout : Layout) (fields : List (Nat × Field))
    (accepted : Ty.aggregateValid layout fields = true) :
    fields.Pairwise fun a b => ∀ region, a.2.type.layout = some region → a.1 + region.bytes ≤ b.1 := by
  simp only [Ty.aggregateValid, checkFields, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have ordered := accepted.2
  rw [Field.layouts_eq_map, List.pairwise_map] at ordered
  apply ordered.imp
  intro a b apart region shaped
  have resolved := a.2.layout_eq_type.trans shaped
  simpa only [resolved, Option.getD_some] using apart

/-- Selection retains the captured field identity, checked byte interval and
parent geometry. An invalid/overlapping field table cannot select a field. -/
theorem Ty.fieldAt_geometry (layout : Layout) (fields : List (Nat × Field))
    (offset base : Nat) (field : Ty) (selected : Ty.fieldAt layout fields offset = some (base, field)) :
    Ty.aggregateValid layout fields = true ∧ ∃ native region,
      (base, native) ∈ fields ∧ native.type = field ∧ field.layout = some region ∧
      0 < region.bytes ∧ base ≤ offset ∧ offset < base + region.bytes ∧
      base + region.bytes ≤ layout.bytes ∧ base % region.alignment = 0 ∧
      layout.alignment % region.alignment = 0 := by
  unfold Ty.fieldAt at selected
  split at selected
  · contradiction
  · rename_i valid
    have accepted : Ty.aggregateValid layout fields = true := by simpa using valid
    obtain ⟨⟨foundBase, native⟩, found, same⟩ := Option.map_eq_some_iff.mp selected
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    have member := List.mem_of_find?_eq_some found
    obtain ⟨region, shaped, positive, bounded, aligned, divided⟩ :=
      Ty.aggregate_member_geometry layout fields foundBase native accepted member
    have contains := List.find?_some found
    dsimp only at contains
    unfold Field.contains at contains
    rw [native.layout_eq_type, shaped] at contains
    simp only [decide_eq_true_eq] at contains
    exact ⟨accepted, native, region, member, rfl, shaped, positive,
      contains.1, contains.2, bounded, aligned, divided⟩

/-- A field pointer preserves its parent's lifetime and constness. Validate the
complete parent subobject before consulting the captured field offsets. This
does not authorize a record view over unrelated storage of the same size. -/
def fieldPointer (state : State) (source : Value) (offset : Nat) : Except Fault Value := do
  let .pointer (.pointer writable _ owner) address := source | .error .malformed
  let some layout := owner.layout | .error .unsupported
  let allocation ← access state address layout false
  if !acceptsView allocation.type address.offset owner then .error .unsupported else
  let some field := fieldType owner offset | .error .unsupported
  .ok (.pointer (.pointer writable false field) ⟨address.allocation, address.offset + offset⟩)

theorem fieldPointer_eq_of_lookup (before after : State) (writable many : Bool) (owner : Ty)
    (address : Address) (offset : Nat)
    (same : after.heap.lookup address.allocation = before.heap.lookup address.allocation) :
    fieldPointer after (.pointer (.pointer writable many owner) address) offset =
      fieldPointer before (.pointer (.pointer writable many owner) address) offset := by
  simp only [fieldPointer, access, same]

theorem fieldPointer_address (state : State) (writable many : Bool) (owner : Ty) (address : Address)
    (offset : Nat) (result : Value)
    (selected : fieldPointer state (.pointer (.pointer writable many owner) address) offset = .ok result) :
    ∃ field, fieldType owner offset = some field ∧
      result = .pointer (.pointer writable false field) ⟨address.allocation, address.offset + offset⟩ := by
  unfold fieldPointer at selected
  cases shaped : owner.layout with
  | none => simp [shaped] at selected
  | some layout =>
    simp only [shaped] at selected
    cases accessed : access state address layout false with
    | error fault => simp [accessed, bind, Except.bind] at selected
    | ok allocation =>
      simp only [accessed, bind, Except.bind] at selected
      split at selected
      · contradiction
      · cases found : fieldType owner offset with
        | none => simp [found] at selected
        | some field => exact ⟨field, rfl, (Except.ok.inj (by simpa only [found] using selected)).symm⟩

theorem fieldPointer_parent (state : State) (writable many : Bool) (owner : Ty) (address : Address)
    (offset : Nat) (result : Value)
    (selected : fieldPointer state (.pointer (.pointer writable many owner) address) offset = .ok result) :
    ∃ layout allocation, owner.layout = some layout ∧ access state address layout false = .ok allocation ∧
      acceptsView allocation.type address.offset owner = true := by
  unfold fieldPointer at selected
  cases shaped : owner.layout with
  | none => simp [shaped] at selected
  | some layout =>
    simp only [shaped] at selected
    cases accessed : access state address layout false with
    | error fault => simp [accessed, bind, Except.bind] at selected
    | ok allocation =>
      simp only [accessed, bind, Except.bind] at selected
      split at selected
      · contradiction
      · rename_i admitted
        exact ⟨layout, allocation, rfl, accessed, by simpa using admitted⟩

/-- A field of any checked declared subobject retains its address and permission.
Payload initialization is independent of this metadata selection. -/
theorem fieldPointer_of_access (state : State) (address : Address) (cell : Allocation) (owner field : Ty)
    (layout : Layout) (offset : Nat) (writable many : Bool)
    (shaped : owner.layout = some layout) (accessed : access state address layout false = .ok cell)
    (admitted : acceptsView cell.type address.offset owner = true)
    (selected : fieldType owner offset = some field) :
    fieldPointer state (.pointer (.pointer writable many owner) address) offset =
      .ok (.pointer (.pointer writable false field) ⟨address.allocation, address.offset + offset⟩) := by
  simp only [fieldPointer, shaped, accessed, bind, Except.bind, admitted,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, selected]

/-- A declared field of a valid live root is selectable before initialization.
Payload initialization is independently checked by loads and stores. -/
theorem root_fieldPointer (state : State) (id : Nat) (cell : Allocation) (owner field : Ty)
    (layout : Layout) (offset : Nat) (writable many : Bool)
    (initial : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = owner) (shaped : owner.layout = some layout) (positive : 0 < layout.bytes)
    (selected : fieldType owner offset = some field) :
    fieldPointer state (.pointer (.pointer writable many owner) ⟨id, 0⟩) offset =
      .ok (.pointer (.pointer writable false field) ⟨id, offset⟩) := by
  have accessed : access state ⟨id, 0⟩ layout false = .ok cell := by
    exact root_access state id cell layout false initial found (typed ▸ shaped) positive (by simp)
  have admitted : acceptsView cell.type 0 owner = true := by
    rw [typed]
    exact acceptsView_self owner
  simpa only [Nat.zero_add] using
    fieldPointer_of_access state ⟨id, 0⟩ cell owner field layout offset writable many shaped accessed admitted selected

/-- Writing cells never changes the declared parent subobject, address,
constness or captured offsets. The field selector does not inspect payloads. -/
theorem fieldPointer_replace_cells (state : State) (id : Nat) (cell : Allocation) (contents : Cells)
    (writable many : Bool) (owner : Ty) (address : Address) (offset : Nat)
    (found : state.heap.lookup id = some cell) :
    fieldPointer { state with heap := state.heap.replace id { cell with cells := contents } }
      (.pointer (.pointer writable many owner) address) offset =
    fieldPointer state (.pointer (.pointer writable many owner) address) offset := by
  by_cases alias : address.allocation = id
  · cases shaped : owner.layout with
    | none => simp [fieldPointer, shaped]
    | some layout =>
      have atParent : state.heap.lookup address.allocation = some cell := alias ▸ found
      have updated := access_replace_cells state address layout false cell contents atParent
      rw [alias] at updated
      simp only [fieldPointer, shaped, updated, bind, Except.bind]
      cases access state address layout false <;> rfl
  · simp only [fieldPointer, access, replace_other state.heap id address.allocation _ alias]

theorem fieldPointer_after_store (state after : State) (pointer value : Value)
    (writable many : Bool) (owner : Ty) (address : Address) (offset : Nat)
    (stored : store state pointer value = .ok after) :
    fieldPointer after (.pointer (.pointer writable many owner) address) offset =
      fieldPointer state (.pointer (.pointer writable many owner) address) offset := by
  obtain ⟨_, _, target, layout, cell, contents, _, _, _, accessed, _, rfl⟩ :=
    store_success state pointer value after stored
  exact fieldPointer_replace_cells state target.allocation cell contents writable many owner address offset
    (access_success_region state target layout true cell accessed).1

/-- Derive the readback from an actual checked store, keeping the same live
field selector. No initialized-record or successful final load is assumed. -/
theorem field_load_after_store (state after : State) (writable many : Bool) (owner : Ty)
    (address : Address) (offset : Nat) (pointer value : Value)
    (selected : fieldPointer state (.pointer (.pointer writable many owner) address) offset = .ok pointer)
    (stored : store state pointer value = .ok after) :
    (do let field ← fieldPointer after (.pointer (.pointer writable many owner) address) offset
        load after field) = .ok value := by
  rw [fieldPointer_after_store state after pointer value writable many owner address offset stored, selected]
  exact load_after_store state pointer value after stored

end Compiler.ZigAir.Memory
