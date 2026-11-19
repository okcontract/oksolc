/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ObservedStorage

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache

/-- An ordinary failure of the existing transaction retains the complete
reached graph, including the cursor. The candidate is never installed on this
path, so no candidate binding or denotation premise is needed. -/
theorem observed_insert_failure (candidate : Storage.Cell) (key : Key) (deterministic : Bool)
    (succeeds : Storage.Allocation → Bool) (before : Heap) (rows : List Storage.Cell)
    (present : before.representatives = some rows) (reads : before.read = Storage.readValue rows)
    (outcome : Storage.Outcome) (failure : outcome ≠ .success)
    (failed : (Storage.insertProgram.run ⟨deterministic, decide (rows.length < 2 ^ 32 - 1), succeeds⟩ {}).1 = some outcome) :
    observedInsert candidate key deterministic succeeds before = (insertionOutcome rows (some outcome), before) := by
  have safe := Storage.insert_safe_any (⟨deterministic, decide (rows.length < 2 ^ 32 - 1), succeeds⟩ : Storage.Input)
  cases ran : Storage.insertProgram.run ⟨deterministic, decide (rows.length < 2 ^ 32 - 1), succeeds⟩ {} with
  | mk result closed =>
    simp only [ran] at failed safe
    subst result
    have released : Storage.Released closed := by
      cases outcome with
      | success => exact False.elim (failure rfl)
      | allocationFailure | capacityFailure => exact safe
    have restored := Storage.failure_restores rows candidate closed released
    have returned : insertionCells rows candidate (insertionOutcome rows (some outcome)) = rows := by
      cases outcome with
      | success => exact False.elim (failure rfl)
      | allocationFailure | capacityFailure => rfl
    simp only [observedInsert, present, observedInsertTransaction, insertTransaction, ran,
      insertedHeap, storageHeap, restored, released.2.2.1, Bool.false_eq_true, ↓reduceIte, returned]
    cases before
    simp only at present reads
    cases reads
    cases present
    rfl

theorem observed_insert_capacity (candidate : Storage.Cell) (key : Key) (deterministic : Bool)
    (succeeds : Storage.Allocation → Bool) (before : Heap) (rows : List Storage.Cell)
    (present : before.representatives = some rows) (reads : before.read = Storage.readValue rows)
    (saturated : 2 ^ 32 - 1 ≤ rows.length) :
    observedInsert candidate key deterministic succeeds before = (.error .capacity, before) := by
  apply observed_insert_failure candidate key deterministic succeeds before rows present reads .capacityFailure (by decide)
  rw [Storage.insert_outcome_any]
  simp only [Storage.expectedOutcome, show decide (rows.length < 2 ^ 32 - 1) = false from
    decide_eq_false (Nat.not_lt_of_ge saturated), Bool.not_false, ↓reduceIte]

theorem observed_insert_preparation_oom (candidate : Storage.Cell) (key : Key)
    (succeeds : Storage.Allocation → Bool) (before : Heap) (rows : List Storage.Cell)
    (present : before.representatives = some rows) (reads : before.read = Storage.readValue rows)
    (room : rows.length < 2 ^ 32 - 1)
    (failed : succeeds .arguments = false ∨ succeeds .item = false ∨ succeeds .clone = false) :
    observedInsert candidate key true succeeds before = (.error .outOfMemory, before) := by
  apply observed_insert_failure candidate key true succeeds before rows present reads .allocationFailure (by decide)
  rw [Storage.insert_outcome_any]
  rcases failed with arguments | item | clone
  all_goals simp [Storage.expectedOutcome, *]

end Compiler.Extraction.Interner
