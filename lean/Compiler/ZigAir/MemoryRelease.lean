/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationLaws

namespace Compiler.ZigAir.Memory

/-- Remove one lifetime without rewinding allocation history. This operation
alone grants no permission to free: clients must check ownership and extent. -/
def erase (state : State) (id : Nat) : State :=
  { state with heap := state.heap.filter (fun entry => entry.1 != id) }

theorem erase_lookup (state : State) (id query : Nat) :
    (erase state id).heap.lookup query = if query = id then none else state.heap.lookup query := by
  rcases state with ⟨heap, nextId, nextAddress⟩
  induction heap with
  | nil => simp [erase, Heap.lookup]
  | cons entry tail ih =>
    rcases entry with ⟨key, cell⟩
    by_cases selected : key = id
    · subst key
      by_cases same : query = id
      · subst query
        simpa [erase, Heap.lookup_cons] using ih
      · simpa [erase, Heap.lookup_cons, same, Ne.symm same] using ih
    · by_cases same : key = query
      · subst query
        simp [erase, Heap.lookup_cons, selected]
      · simpa [erase, Heap.lookup_cons, selected, same] using ih

theorem erase_preserves_valid (state : State) (id : Nat) (valid : state.valid = true) :
    (erase state id).valid = true := by
  simp only [State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid ⊢
  exact ⟨⟨valid.1.1, fun entry present => valid.1.2 entry (List.mem_filter.mp present).1⟩,
    valid.2.filter _⟩

theorem erase_keeps_counters (state : State) (id : Nat) :
    (erase state id).nextId = state.nextId ∧ (erase state id).nextAddress = state.nextAddress := ⟨rfl, rfl⟩

theorem erase_load_other (state : State) (id : Nat) (writable many : Bool) (child : Ty)
    (address : Address) (apart : address.allocation ≠ id) :
    load (erase state id) (.pointer (.pointer writable many child) address) =
      load state (.pointer (.pointer writable many child) address) := by
  apply load_eq_of_lookup
  simp only [erase_lookup, if_neg apart]

theorem erase_load_dead (state : State) (id offset : Nat) (writable many : Bool) (child : Ty)
    (layout : Layout) (shaped : child.layout = some layout) :
    load (erase state id) (.pointer (.pointer writable many child) ⟨id, offset⟩) = .error .unallocated := by
  simp [load, shaped, access, erase_lookup, bind, Except.bind]

/-- Release one complete persistent mutable allocation. The owner/allocator
registry is checked by the compiler client before this typed lifetime check. -/
def releaseOwned (state : State) (id : Nat) (type : Ty) : Except Fault State := do
  if !state.valid then .error .malformed else
  let some cell := state.heap.lookup id | .error .unallocated
  if cell.type = type ∧ cell.writable = true ∧ cell.stack = false then
    .ok (erase state id)
  else .error .memoryValidity

/-- Successful release checks the complete declared persistent allocation;
contents need not be initialized. The lifetime is erased without reuse. -/
theorem releaseOwned_shape (state after : State) (id : Nat) (type : Ty)
    (released : releaseOwned state id type = .ok after) :
    state.valid = true ∧ ∃ cell, state.heap.lookup id = some cell ∧ cell.type = type ∧
      cell.writable = true ∧ cell.stack = false ∧ after = erase state id := by
  unfold releaseOwned at released
  split at released
  · contradiction
  · rename_i valid
    cases found : state.heap.lookup id with
    | none => simp only [found] at released; contradiction
    | some cell =>
      simp only [found] at released
      split at released
      · rename_i owned
        cases released
        exact ⟨by simpa using valid, cell, rfl, owned.1, owned.2.1, owned.2.2, rfl⟩
      · contradiction

end Compiler.ZigAir.Memory
