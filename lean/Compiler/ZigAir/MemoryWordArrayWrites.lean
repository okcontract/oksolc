/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordArray

namespace Compiler.ZigAir.Memory.WordArray

theorem array_view (extent index : Nat) (inside : index < extent) :
    acceptsView (.array extent word) (index * 4) word = true := by
  simp [acceptsView, word, Ty.layout, inside]

theorem array_leaf (extent index : Nat) (inside : index < extent) :
    leafType (.array extent word) (index * 4) = some word := by
  simp [leafType, word, Ty.layout, inside]

theorem writable_store (state after : State) (view : View) (pointer value : Value)
    (stored : store state pointer value = .ok after) (cap : Writable state view) :
    Writable after view := by
  obtain ⟨extent, cell, found, typed, writable, bound⟩ := cap
  obtain ⟨_, _, address, layout, target, contents, _, _, _, accessed, _, rfl⟩ :=
    store_success state pointer value after stored
  have targetFound := (access_success_region state address layout true target accessed).1
  by_cases alias : view.allocation = address.allocation
  · have same : cell = target := Option.some.inj (found.symm.trans (alias ▸ targetFound))
    subst target
    refine ⟨extent, { cell with cells := contents }, ?_, typed, writable, bound⟩
    simpa only [alias] using Heap.lookup_replace state.heap address.allocation cell { cell with cells := contents } targetFound
  · exact ⟨extent, cell, (replace_other state.heap address.allocation view.allocation _ alias).trans found,
      typed, writable, bound⟩

theorem write_total (state : State) (view : View) (index : Nat) (value : BitVec 32)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    ∃ after, store state (view.pointer index) (number value) = .ok after := by
  obtain ⟨extent, cell, found, typed, _, bound, accessed⟩ :=
    element_access state view index 4 initial cap inside (by omega) true
  have inArray : view.first + index < extent := by omega
  have contents : cell.cells.write cell.type (view.address index).offset (number value) =
      .ok (cell.cells.set (view.address index).offset (number value)) := by
    rw [typed]
    apply Cells.write_single
    · exact number_valid value
    · exact array_view extent (view.first + index) inArray
    · simp only [leafFits, number, Value.type, Scalar.Value.type, View.address, array_leaf extent _ inArray,
        decide_true, Bool.true_and]
      exact number_valid value
    · rfl
  exact ⟨_, store_of_access state word (view.address index) ⟨4, 4⟩ cell _ (number value)
    (number_typed value) rfl accessed contents⟩

theorem write_offset_frame (state after : State) (view : View) (index offset : Nat) (value : BitVec 32)
    (stored : store state (view.pointer index) (number value) = .ok after)
    (apart : offset ≠ (view.address index).offset) :
    load after (.pointer (.pointer true false word) ⟨view.allocation, offset⟩) =
      load state (.pointer (.pointer true false word) ⟨view.allocation, offset⟩) := by
  apply load_disjoint_after_store state true false word (view.address index) (number value) after
    true false word offset stored
  simpa [Ty.readOffsets, Value.leaves, number] using apart

theorem write_frame (state after : State) (view : View) (index other : Nat) (value : BitVec 32)
    (stored : store state (view.pointer index) (number value) = .ok after) (apart : other ≠ index) :
    load after (view.pointer other) = load state (view.pointer other) :=
  write_offset_frame state after view index (view.address other).offset value stored (by
    simp only [View.address]; omega)

/-- Complete initialized view, related to the existing list used by the
optimizer. Memory outside the view remains unconstrained and is framed. -/
def Represents (state : State) (view : View) (items : List (BitVec 32)) : Prop :=
  items.length = view.length ∧ ∀ index (inside : index < items.length),
    load state (view.pointer index) = .ok (number items[index])

theorem write_represents (state after : State) (view : View) (items : List (BitVec 32))
    (index : Nat) (value : BitVec 32) (represented : Represents state view items)
    (stored : store state (view.pointer index) (number value) = .ok after) :
    Represents after view (items.set index value) := by
  refine ⟨by simpa using represented.1, ?_⟩
  intro other inside
  have inItems : other < items.length := by simpa using inside
  by_cases same : other = index
  · subst other
    simpa using load_after_store state (view.pointer index) (number value) after stored
  · rw [write_frame state after view index other value stored same]
    simpa [List.getElem_set, Ne.symm same] using represented.2 other inItems

/-- Successful writes also retain allocation counters and every unrelated
allocation exactly, not merely its initialized word observations. -/
theorem write_allocation_frame (state after : State) (view : View) (index : Nat) (value : BitVec 32)
    (stored : store state (view.pointer index) (number value) = .ok after) :
    after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      ∀ id, id ≠ view.allocation → after.heap.lookup id = state.heap.lookup id := by
  have counters := store_keeps_counters state _ _ after stored
  refine ⟨counters.1, counters.2, ?_⟩
  exact heap_after_store_other state true false word (view.address index) (number value) after stored

end Compiler.ZigAir.Memory.WordArray
