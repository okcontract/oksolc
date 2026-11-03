/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationLaws

/-! Heap framing across invocation-local allocations and writes. The older
heap retains exact list order and complete allocations, not only load values. -/
namespace Compiler.ZigAir.Memory

def Heap.older (mark : Nat) (heap : Heap) : Heap := heap.filter (fun entry => entry.1 < mark)
def Heap.StackSince (mark : Nat) (heap : Heap) : Prop :=
  ∀ entry ∈ heap, mark ≤ entry.1 → entry.2.stack = true

theorem Heap.older_replace (heap : Heap) (mark id : Nat) (cell : Allocation) (fresh : mark ≤ id) :
    (heap.replace id cell).older mark = heap.older mark := by
  induction heap with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨key, old⟩
    by_cases selected : key = id
    · subst key
      simpa [Heap.replace_cons, Heap.older, Nat.not_lt.mpr fresh] using ih
    · simp only [Heap.replace_cons, if_neg selected, Heap.older, List.filter_cons]
      split <;> simp_all [Heap.older]

theorem Heap.StackSince.replace (heap : Heap) (mark id : Nat) (cell : Allocation)
    (initial : heap.StackSince mark) (stack : cell.stack = true) : (heap.replace id cell).StackSince mark := by
  intro entry present newer
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
  by_cases selected : old.1 = id
  · simpa [selected] using stack
  · simp only [if_neg selected] at newer ⊢
    exact initial old member newer

theorem cleanup_eq_older (state : State) (mark : Nat) (stack : state.heap.StackSince mark) :
    (cleanup mark state).heap = state.heap.older mark := by
  apply List.filter_congr
  intro entry present
  by_cases old : entry.1 < mark
  · simp [old]
  · simp [old, stack entry present (by omega)]

theorem valid_initial_frame (state : State) (initial : state.valid = true) :
    state.heap.StackSince state.nextId ∧ state.heap.older state.nextId = state.heap := by
  have older : ∀ entry ∈ state.heap, entry.1 < state.nextId := by
    simp only [State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at initial
    intro entry present
    have h := initial.1.2 entry present
    exact h.1.1
  refine ⟨fun entry present newer => False.elim (by have := older entry present; omega), ?_⟩
  exact List.filter_eq_self.mpr (fun entry present => by simpa using older entry present)

theorem allocate_frame (state after : State) (child : Ty) (pointer : Value) (mark : Nat)
    (allocated : allocate state child = .ok (pointer, after))
    (fresh : mark ≤ state.nextId) (stack : state.heap.StackSince mark) :
    after.heap.StackSince mark ∧ after.heap.older mark = state.heap.older mark := by
  obtain ⟨layout, base, _, _, rfl⟩ := allocate_shape state child pointer after allocated
  constructor
  · intro entry present newer
    rcases List.mem_cons.mp present with same | old
    · cases same; rfl
    · exact stack entry old newer
  · simp [Heap.older, Nat.not_lt.mpr fresh]

theorem store_frame (state after : State) (writable many : Bool) (child : Ty) (address : Address)
    (value : Value) (mark : Nat)
    (stored : store state (.pointer (.pointer writable many child) address) value = .ok after)
    (fresh : mark ≤ address.allocation) (stack : state.heap.StackSince mark) :
    after.heap.StackSince mark ∧ after.heap.older mark = state.heap.older mark := by
  obtain ⟨_, _, _, _, cell, contents, same, _, _, accessed, _, rfl⟩ := store_success state _ value after stored
  cases same
  have found := (access_success_region state address _ true cell accessed).1
  have localStack := stack (address.allocation, cell) (Heap.lookup_mem state.heap _ cell found) fresh
  exact ⟨Heap.StackSince.replace state.heap mark address.allocation _ stack localStack,
    Heap.older_replace state.heap mark address.allocation _ fresh⟩

end Compiler.ZigAir.Memory
