/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativePublicationProgram
import Compiler.Extraction.RepresentativeOwnerFields
import Compiler.ZigAir.MemorySliceUpdates
import Compiler.ZigAir.MemoryAllocationShape

namespace Compiler.Extraction.RepresentativeArray.Publication
open Compiler.ZigAir.Memory

def pointerType : Ty := .pointer true true elementType

theorem pointer_field_checked : fieldType itemsType 0 = some pointerType := by decide

/-- Execute one admitted assignment. Selecting a slice's pointer field supplies
no length value and does not rewrite that leaf. Inputs are already evaluated. -/
def write (update : Update) (state : State) (header data : Address) (capacity : Int) : Except Fault State := do
  match update with
  | .itemsPointer =>
    let pointer ← itemsDataPointer state header true
    store state pointer (.pointer pointerType data)
  | .capacity =>
    let pointer ← fieldPointer state (.pointer (.pointer true false allocationType) header) capacityOffset
    store state pointer (.scalar (.int false 64 capacity))

/-- A rejected later assignment retains the pointer update already reached.
This suffix neither reserves backing nor frees/transfers its prior owner. -/
def steps (updates : List Update) (state : State) (header data : Address) (capacity : Int) : Except Fault Unit × State :=
  match updates with
  | [] => (.ok (), state)
  | update :: rest =>
    match write update state header data capacity with
    | .error fault => (.error fault, state)
    | .ok after => steps rest after header data capacity

def run (state : State) (header data : Address) (capacity : Int) : Except Fault Unit × State :=
  steps program state header data capacity

theorem write_is_store (update : Update) (state after : State) (header data : Address) (capacity : Int)
    (executed : write update state header data capacity = .ok after) :
    ∃ offset type value, store state (.pointer (.pointer true false type) ⟨header.allocation, offset⟩) value = .ok after := by
  cases update with
  | itemsPointer =>
    cases selected : fieldPointer state (.pointer (.pointer true false allocationType) header) itemsOffset with
    | error fault => simp [write, itemsDataPointer, selected, bind, Except.bind] at executed
    | ok items =>
      obtain ⟨field, _, rfl⟩ := fieldPointer_address state true false allocationType header itemsOffset items selected
      cases pointerSelected : fieldPointer state
          (.pointer (.pointer true false field) ⟨header.allocation, header.offset + itemsOffset⟩) 0 with
      | error fault => simp [write, itemsDataPointer, selected, pointerSelected, bind, Except.bind] at executed
      | ok pointer =>
        obtain ⟨type, _, rfl⟩ := fieldPointer_address state true false field
          ⟨header.allocation, header.offset + itemsOffset⟩ 0 pointer pointerSelected
        exact ⟨_, type, .pointer pointerType data, by simpa only [write, itemsDataPointer, selected, pointerSelected, bind, Except.bind] using executed⟩
  | capacity =>
    cases selected : fieldPointer state (.pointer (.pointer true false allocationType) header) capacityOffset with
    | error fault => simp [write, selected, bind, Except.bind] at executed
    | ok pointer =>
      obtain ⟨type, _, rfl⟩ := fieldPointer_address state true false allocationType header capacityOffset pointer selected
      exact ⟨_, type, .scalar (.int false 64 capacity), by simpa only [write, selected, bind, Except.bind] using executed⟩

/-- Every publication prefix preserves valid storage and all other lifetimes.
An error never rolls back an earlier assignment or changes allocation history. -/
theorem steps_storage (updates : List Update) (state : State) (header data : Address) (capacity : Int)
    (initial : state.valid = true) :
    (steps updates state header data capacity).2.valid = true ∧
      state.heap.RetainsShape (steps updates state header data capacity).2.heap ∧
      (steps updates state header data capacity).2.nextId = state.nextId ∧
      (steps updates state header data capacity).2.nextAddress = state.nextAddress ∧
      (∀ id, id ≠ header.allocation → (steps updates state header data capacity).2.heap.lookup id = state.heap.lookup id) := by
  induction updates generalizing state with
  | nil => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
  | cons update rest ih =>
    simp only [steps]
    cases executed : write update state header data capacity with
    | error fault => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
    | ok after =>
      obtain ⟨offset, type, value, stored⟩ := write_is_store update state after header data capacity executed
      have tail := ih after (store_preserves_valid _ _ _ _ initial stored)
      have counters := store_keeps_counters _ _ _ _ stored
      exact ⟨tail.1, (store_retains_shape _ _ _ _ stored).trans tail.2.1,
        tail.2.2.1.trans counters.1, tail.2.2.2.1.trans counters.2,
        fun id apart => (tail.2.2.2.2 id apart).trans (heap_after_store_other _ _ _ _ _ _ _ stored id apart)⟩

theorem run_storage (state : State) (header data : Address) (capacity : Int) (initial : state.valid = true) :
    (run state header data capacity).2.valid = true ∧ state.heap.RetainsShape (run state header data capacity).2.heap ∧
      (run state header data capacity).2.nextId = state.nextId ∧ (run state header data capacity).2.nextAddress = state.nextAddress ∧
      (∀ id, id ≠ header.allocation → (run state header data capacity).2.heap.lookup id = state.heap.lookup id) :=
  steps_storage program state header data capacity initial

end Compiler.Extraction.RepresentativeArray.Publication
