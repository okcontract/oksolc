/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativePublicationProofs

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory

/-- `allocatedSlice` observes the pointer and full capacity, never the items
length or uninitialized spare descriptors. Empty views need no live sentinel
allocation; nonempty views must fit the actual containing backing region. -/
def allocatedSlice (state : State) (header : Address) : Except Fault Value := do
  let pointer ← readItemsData state header
  let .pointer type data := pointer | .error .malformed
  if type ≠ Publication.pointerType then .error .malformed else
  let .scalar (.int false 64 capacity) ← readField state header capacityOffset | .error .malformed
  if capacity = 0 then .ok (.slice itemsType data 0)
  else makeSlice state itemsType pointer capacity.toNat

theorem allocatedSlice_empty (state : State) (header data : Address)
    (pointer : readItemsData state header = .ok (.pointer Publication.pointerType data))
    (capacity : readField state header capacityOffset = .ok (.scalar (.int false 64 0))) :
    allocatedSlice state header = .ok (.slice itemsType data 0) := by
  simp only [allocatedSlice, pointer, capacity, bind, Except.bind, ne_self_iff_false, ↓reduceIte]

/-- The saved nonempty view covers the declared capacity, including unwritten
spare descriptors. Its construction uses actual header reads and live backing
geometry, without reading any descriptor or assuming a successful slice. -/
theorem allocatedSlice_nonempty (state : State) (header : Address) (id capacity : Nat) (cell : Allocation)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (nonempty : capacity ≠ 0)
    (pointer : readItemsData state header = .ok (.pointer Publication.pointerType ⟨id, 0⟩))
    (count : readField state header capacityOffset = .ok (.scalar (.int false 64 capacity))) :
    allocatedSlice state header = .ok (.slice itemsType ⟨id, 0⟩ capacity) := by
  have shaped : cell.type.layout = some ⟨capacity * 32, 8⟩ := by
    rw [typed]; rfl
  obtain ⟨_, positive, layout, shape, _, bounded, limit⟩ := valid_lookup state id cell valid found
  cases Option.some.inj (shape.symm.trans shaped)
  have width : capacity < addressLimit := by dsimp only at bounded; omega
  have access := root_access state id cell ⟨capacity * 32, 8⟩ false valid found shaped (by dsimp only; omega) (by simp)
  have slice : makeSlice state itemsType (.pointer Publication.pointerType ⟨id, 0⟩) capacity =
      .ok (.slice itemsType ⟨id, 0⟩ capacity) := by
    simp [makeSlice, itemsType, Publication.pointerType, elementType, Ty.layout,
      Nat.not_le.mpr width, access, bind, Except.bind]
  simpa [allocatedSlice, pointer, count, nonempty, bind, Except.bind] using slice

/-- Recover the pointer from the already checked slice read. The executable
pointer reader itself does not read the length or dereference the backing. -/
theorem readItemsData_from_loaded (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (data : Address) (length : Nat) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (loaded : readItems state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType data length)) :
    readItemsData state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.pointer Publication.pointerType data) := by
  have header : Owner.headerAddress ⟨lifetime, 0⟩ = ⟨lifetime, Owner.representativesOffset⟩ := rfl
  rw [header] at loaded ⊢
  have fields := Owner.root_header_fields runtimeSafety state lifetime cell false initial found typed
  rw [header] at fields
  have selector := Publication.owner_pointer_selector runtimeSafety state lifetime cell false initial found typed
  have raw : load state (.pointer (.pointer false false itemsType) ⟨lifetime, Owner.representativesOffset + itemsOffset⟩) =
      .ok (.slice itemsType data length) := by
    simpa only [readItems, readField, fields.1, bind, Except.bind] using loaded
  cases accessed : access state ⟨lifetime, Owner.representativesOffset + itemsOffset⟩ ⟨16, 8⟩ false with
  | error fault => simp [load, itemsType, Ty.layout, accessed, bind, Except.bind] at raw
  | ok owner =>
    have same := Option.some.inj (((access_success_region state _ _ false owner accessed).1).symm.trans found)
    subst owner
    have read : cell.cells.read cell.type (Owner.representativesOffset + itemsOffset) itemsType =
        .ok (.slice itemsType data length) := by
      simpa only [load, itemsType, Ty.layout, Ty.leafLayout, accessed, bind, Except.bind, readCell] using raw
    have parts := cell.cells.read_slice_parts cell.type (Owner.representativesOffset + itemsOffset) true elementType data length read
    have pointerAccess := access_subregion state ⟨lifetime, Owner.representativesOffset + itemsOffset⟩ ⟨16, 8⟩ ⟨8, 8⟩ 0 false cell
      accessed (by decide) (by decide) (by decide) (by decide)
    simp only [Nat.add_zero] at pointerAccess
    have view : acceptsView cell.type (Owner.representativesOffset + itemsOffset) (.pointer true true elementType) = true := by
      rw [typed]
      cases runtimeSafety <;> decide
    have pointerRead : load state (.pointer (.pointer false false Publication.pointerType) ⟨lifetime, Owner.representativesOffset + itemsOffset⟩) =
        .ok (.pointer Publication.pointerType data) := by
      simp only [load, Publication.pointerType, Ty.layout, Ty.leafLayout, pointerAccess, bind, Except.bind, readCell,
        Cells.read, view, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      exact parts.2.1
    simp only [readItemsData, itemsDataPointer, fields.1, selector, bind, Except.bind, pointerRead]

end Compiler.Extraction.RepresentativeArray
