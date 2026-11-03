/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpPrologue
import Compiler.ZigAir.MemoryHeapFrame

/-! Writable whole-word scratch views. Combined with the executable heap
invariant, this small capability discharges each checked store; it is proved
for fresh allocations and preserved by writes and unrelated allocations. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir

def Writable (state : State) (address : Address) : Prop :=
  address.offset = 0 ∧ ∃ cell, state.heap.lookup address.allocation = some cell ∧
    cell.type = wordType ∧ cell.writable = true

theorem writable_fresh (state after : State) (pointer : Value)
    (allocated : allocate state wordType = .ok (pointer, after)) : Writable after ⟨state.nextId, 0⟩ := by
  obtain ⟨_, base, _, _, rfl⟩ := allocate_shape state wordType pointer after allocated
  exact ⟨rfl, ⟨base, wordType, [], true, true⟩, by simp [Heap.lookup_cons], rfl, rfl⟩

theorem writable_allocate (state after : State) (pointer : Value) (address : Address)
    (allocated : allocate state wordType = .ok (pointer, after)) (cap : Writable state address)
    (apart : address.allocation ≠ state.nextId) : Writable after address := by
  obtain ⟨offset, cell, found, typed, writable⟩ := cap
  obtain ⟨_, _, _, _, rfl⟩ := allocate_shape state wordType pointer after allocated
  exact ⟨offset, cell, by simpa only [Heap.lookup_cons, if_neg apart.symm] using found, typed, writable⟩

theorem writable_store (state after : State) (written address : Address) (value : Word)
    (stored : store state (slot written) (number value) = .ok after) (cap : Writable state address) :
    Writable after address := by
  obtain ⟨offset, cell, found, typed, writable⟩ := cap
  obtain ⟨_, _, _, _, target, contents, same, _, _, accessed, _, rfl⟩ := store_success state _ _ after stored
  cases same
  have targetFound := (access_success_region state written _ true target accessed).1
  by_cases alias : address.allocation = written.allocation
  · have sameCell : cell = target := Option.some.inj (found.symm.trans (alias ▸ targetFound))
    subst target
    refine ⟨offset, { cell with cells := contents }, ?_, typed, writable⟩
    simpa only [alias] using Heap.lookup_replace state.heap written.allocation cell { cell with cells := contents } targetFound
  · exact ⟨offset, cell, (replace_other state.heap written.allocation address.allocation _ alias).trans found, typed, writable⟩

theorem write_total (state : State) (address : Address) (value : Word)
    (initial : state.valid = true) (cap : Writable state address) :
    ∃ after, store state (slot address) (number value) = .ok after := by
  obtain ⟨offset, cell, found, typed, writable⟩ := cap
  obtain ⟨_, positive, layout, shaped, aligned, extent, bounded⟩ := valid_lookup state address.allocation cell initial found
  rw [typed] at shaped
  have shape : layout = ⟨32, 16⟩ := Option.some.inj shaped.symm
  subst layout
  dsimp only at aligned extent
  have checks : ¬(cell.base = 0 ∨ cell.base + 32 > addressLimit ∨ cell.base + address.offset ≥ addressLimit ∨
      address.offset + 32 > 32 ∨ (cell.base + address.offset) % 16 ≠ 0) := by simp only [offset, Nat.add_zero]; omega
  have accessed : access state address ⟨32, 16⟩ true = .ok cell := by
    simp only [access, found, typed, Ty.layout, Ty.leafLayout, wordType, writable, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, if_neg checks]
  have contents : cell.cells.write cell.type address.offset (number value) =
      .ok (cell.cells.set 0 (number value)) := by
    rw [typed, offset]
    apply Cells.write_single cell.cells wordType 0 (number value)
    · exact number_valid value
    · rfl
    · change (decide (some wordType = some wordType) && (number value).valid) = true
      rw [number_valid]; rfl
    · rfl
  refine ⟨{ state with heap := state.heap.replace address.allocation { cell with cells := cell.cells.set 0 (number value) } }, ?_⟩
  exact store_of_access state wordType address ⟨32, 16⟩ cell _ (number value)
    (number_typed value) rfl accessed contents

theorem allocate_fault (state : State) (reason : Fault) (initial : state.valid = true)
    (failed : allocate state wordType = .error reason) : reason = .outOfMemory := by
  simp only [allocate, initial, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Ty.layout, Ty.leafLayout, wordType] at failed
  split at failed
  · exact (Except.error.inj failed).symm
  · contradiction

end Compiler.ZigAir.MemoryExp
