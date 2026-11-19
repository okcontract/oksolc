/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeGrowthProofs

namespace Compiler.Extraction.RepresentativeArray.Growth
open Compiler.ZigAir.Memory

/-- Allocation rejection, OOM and later copy/publication rejection all preserve
valid storage and every allocation except the header owner and fresh backing. -/
theorem first_storage (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (initial : state.valid = true) :
    (firstAllocation state header capacity allocate effects).1.2.valid = true ∧
      (∀ id, id ≠ header.allocation → id ≠ state.nextId →
        (firstAllocation state header capacity allocate effects).1.2.heap.lookup id = state.heap.lookup id) := by
  have validReady := Backing.reserve_preserves_valid state capacity allocate effects initial
  have frame : ∀ id, id ≠ header.allocation → id ≠ state.nextId →
      (Backing.reserve state capacity allocate effects).1.2.heap.lookup id = state.heap.lookup id := by
    intro id _ apart
    unfold Backing.reserve
    split
    · rfl
    · exact RegionAllocation.reserve_heap_other state (Backing.type capacity) allocate effects id apart
  unfold firstAllocation
  generalize reserved : Backing.reserve state capacity allocate effects = outcome at *
  rcases outcome with ⟨⟨result, ready⟩, reached⟩
  cases result with
  | error fault => exact ⟨validReady, frame⟩
  | ok value =>
    cases value with
    | none => exact ⟨validReady, frame⟩
    | some data =>
      simp only []
      cases loaded : readItems ready header with
      | error fault => exact ⟨validReady, frame⟩
      | ok value =>
        cases value <;> try exact ⟨validReady, frame⟩
        rename_i type source length
        by_cases empty : length = 0
        · subst length
          simp only [ne_self_iff_false, ↓reduceIte, Copy.run]
          have publication := Publication.run_storage ready header data capacity validReady
          generalize published : Publication.run ready header data capacity = outcome at *
          rcases outcome with ⟨result, after⟩
          cases result <;> exact ⟨publication.1, fun id ownerApart freshApart =>
            (publication.2.2.2.2 id ownerApart).trans (frame id ownerApart freshApart)⟩
        · simp only [if_pos empty]
          exact ⟨validReady, frame⟩

theorem run_storage (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (initial : state.valid = true) :
    (run state header capacity allocate effects).1.2.valid = true ∧
      (∀ id, id ≠ header.allocation → id ≠ state.nextId →
        (run state header capacity allocate effects).1.2.heap.lookup id = state.heap.lookup id) := by
  unfold run
  cases prepare state header capacity with
  | error fault => exact ⟨initial, fun _ _ _ => rfl⟩
  | ok value => cases value with
    | none => exact ⟨initial, fun _ _ _ => rfl⟩
    | some pair =>
      rcases pair with ⟨data, oldCapacity⟩
      dsimp only
      split
      · exact first_storage state header capacity allocate effects initial
      · exact ⟨initial, fun _ _ _ => rfl⟩

/-- A live independently allocated parent view survives every first-growth
outcome, including a successful reservation followed by a checked rejection. -/
theorem run_parent_borrow (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (parent : WordArray.View)
    (items : List (BitVec 32)) (initial : state.valid = true)
    (separate : parent.allocation ≠ header.allocation)
    (represented : WordArray.Represents state parent items) :
    WordArray.Represents (run state header capacity allocate effects).1.2 parent items := by
  refine ⟨represented.1, ?_⟩
  intro index inside
  have nonempty : items ≠ [] := by intro empty; simp [empty] at inside
  have older := WordAllocation.source_older state parent items initial represented nonempty
  have frame := (run_storage state header capacity allocate effects initial).2 parent.allocation separate (by omega)
  exact (load_eq_of_lookup state _ true false WordArray.word (parent.address index) frame).trans (represented.2 index inside)

end Compiler.Extraction.RepresentativeArray.Growth
