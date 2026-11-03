/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationLaws

/-! Persistence of allocation metadata while contents change. These are facts
about the typed heap; no native address/provenance correspondence is assumed. -/
namespace Compiler.ZigAir.Memory

def Allocation.SameShape (before after : Allocation) : Prop :=
  after.base = before.base ∧ after.type = before.type ∧
    after.writable = before.writable ∧ after.stack = before.stack

def Heap.RetainsShape (before after : Heap) : Prop :=
  ∀ id cell, before.lookup id = some cell →
    ∃ updated, after.lookup id = some updated ∧ cell.SameShape updated

theorem Allocation.SameShape.refl (cell : Allocation) : cell.SameShape cell := ⟨rfl, rfl, rfl, rfl⟩

theorem Allocation.SameShape.trans {a b c : Allocation}
    (first : a.SameShape b) (second : b.SameShape c) : a.SameShape c :=
  ⟨second.1.trans first.1, second.2.1.trans first.2.1,
    second.2.2.1.trans first.2.2.1, second.2.2.2.trans first.2.2.2⟩

theorem Heap.RetainsShape.refl (heap : Heap) : heap.RetainsShape heap :=
  fun _ cell found => ⟨cell, found, Allocation.SameShape.refl cell⟩

theorem Heap.RetainsShape.trans {a b c : Heap}
    (first : a.RetainsShape b) (second : b.RetainsShape c) : a.RetainsShape c := by
  intro id cell found
  obtain ⟨middle, lookup, shape⟩ := first id cell found
  obtain ⟨after, lookup, next⟩ := second id middle lookup
  exact ⟨after, lookup, shape.trans next⟩

theorem store_retains_shape (state : State) (pointer value : Value) (after : State)
    (success : store state pointer value = .ok after) : state.heap.RetainsShape after.heap := by
  obtain ⟨_, _, address, _, cell, contents, _, _, _, accessed, _, rfl⟩ :=
    store_success state pointer value after success
  have found := (access_success_region state address _ true cell accessed).1
  intro id old lookup
  by_cases selected : id = address.allocation
  · subst id
    have same : old = cell := Option.some.inj (lookup.symm.trans found)
    subst old
    exact ⟨{ cell with cells := contents }, Heap.lookup_replace _ _ _ _ found, rfl, rfl, rfl, rfl⟩
  · exact ⟨old, (replace_other _ _ _ _ selected).trans lookup, Allocation.SameShape.refl old⟩

/-- A store updates an existing allocation and cannot revive a dead lifetime. -/
theorem store_keeps_missing (state : State) (pointer value : Value) (after : State) (id : Nat)
    (success : store state pointer value = .ok after) (missing : state.heap.lookup id = none) :
    after.heap.lookup id = none := by
  obtain ⟨_, _, address, _, cell, contents, _, _, _, accessed, _, rfl⟩ :=
    store_success state pointer value after success
  have found := (access_success_region state address _ true cell accessed).1
  have apart : id ≠ address.allocation := by intro same; rw [← same, missing] at found; contradiction
  exact (replace_other _ _ _ _ apart).trans missing

theorem allocate_retains_shape (state : State) (child : Ty) (value : Value) (after : State)
    (initial : state.valid = true) (success : allocate state child = .ok (value, after)) :
    state.heap.RetainsShape after.heap := by
  obtain ⟨_, _, _, _, rfl⟩ := allocate_shape state child value after success
  intro id cell found
  have older := (valid_lookup state id cell initial found).1
  exact ⟨cell, by simpa only [Heap.lookup_cons, if_neg (by omega : state.nextId ≠ id)] using found,
    Allocation.SameShape.refl cell⟩

theorem cleanup_lookup_older (state : State) (mark id : Nat) (older : id < mark) :
    (cleanup mark state).heap.lookup id = state.heap.lookup id := by
  rcases state with ⟨heap, nextId, nextAddress⟩
  change Heap.lookup (heap.filter (fun entry => !entry.2.stack || entry.1 < mark)) id = heap.lookup id
  induction heap with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key, cell⟩
    by_cases selected : key = id
    · subst key
      simp [older, Heap.lookup_cons]
    · simp only [List.filter_cons]
      split <;> simp only [Heap.lookup_cons, if_neg selected, ih]

/-- A live stack local at or after the return mark is retired. Native validity
rules out a duplicate lifetime reappearing underneath the removed entry. -/
theorem cleanup_lookup_stack (state : State) (mark id : Nat) (cell : Allocation)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell)
    (stack : cell.stack = true) (recent : mark ≤ id) :
    (cleanup mark state).heap.lookup id = none := by
  cases observed : (cleanup mark state).heap.lookup id with
  | none => rfl
  | some other =>
    have member := List.mem_filter.mp (Heap.lookup_mem (cleanup mark state).heap id other observed)
    have same := Option.some.inj ((lookup_of_mem_valid state id other valid member.1).symm.trans found)
    have retained := member.2
    simp only [same, stack, Bool.not_true, Bool.false_or, decide_eq_true_eq] at retained
    omega

/-- Caller stack allocations survive cleanup at the invocation's original
mark. This deliberately makes no persistence claim for fresh stack cells. -/
theorem cleanup_retains_shape (caller after : State) (initial : caller.valid = true)
    (retained : caller.heap.RetainsShape after.heap) :
    caller.heap.RetainsShape (cleanup caller.nextId after).heap := by
  intro id cell found
  obtain ⟨updated, lookup, shape⟩ := retained id cell found
  exact ⟨updated, (cleanup_lookup_older after caller.nextId id
    (valid_lookup caller id cell initial found).1).trans lookup, shape⟩

end Compiler.ZigAir.Memory
