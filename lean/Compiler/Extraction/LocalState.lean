/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.RepresentativeFrame

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache

/-- Earlier state-independent primitive clients embed without changing their
outcomes, graph or cursor. This equality includes failures. -/
theorem lift_local_from_except (result : Except Error α) :
    liftLocal (Local.fromExcept result) = lift result := rfl

theorem local_result (action : Local α) (before : Heap) :
    (liftLocal action before).1 = (action before.allocationCursor).1 := rfl

theorem local_cursor (action : Local α) (before : Heap) :
    (liftLocal action before).2.allocationCursor = (action before.allocationCursor).2 := rfl

theorem local_observations (action : Local α) (before : Heap) :
    (liftLocal action before).2.read = before.read ∧
    (liftLocal action before).2.table = before.table ∧
    (liftLocal action before).2.representatives = before.representatives := ⟨rfl, rfl, rfl⟩

theorem local_safe (meaning : Meaning) (action : Local α) (before : Heap) (valid : Invariant meaning before) :
    Safe meaning (liftLocal action) before (fun value after =>
      action before.allocationCursor = (.ok value, after.allocationCursor)) := by
  intro outcome after ran
  cases step : action before.allocationCursor with
  | mk result cursor =>
    simp only [liftLocal, step] at ran
    cases ran
    refine ⟨valid.with_cursor cursor, fun _ _ found => found, ?_⟩
    cases outcome with
    | error error => trivial
    | ok value => rfl

/-- Stateful local composition threads the same cursor as graph actions. In
particular, an error does not reset earlier allocation observations. -/
theorem lift_local_bind (first : Local α) (next : α → Local β) :
    liftLocal (first >>= next) = (liftLocal first >>= fun value => liftLocal (next value)) := by
  funext before
  cases step : first before.allocationCursor with
  | mk result middle =>
    cases result with
    | error error => simp only [bind, Effect.bind, liftLocal, step]
    | ok value => simp only [bind, Effect.bind, liftLocal, step]

theorem local_sequential_failure (first : Local α) (next : α → Local β) (before : Heap)
    (value : α) (middle after : Nat) (error : Error)
    (initial : first before.allocationCursor = (.ok value, middle))
    (failed : next value middle = (.error error, after)) :
    (liftLocal first >>= fun value => liftLocal (next value)) before =
      (.error error, { before with allocationCursor := after }) := by
  rw [← lift_local_bind]
  simp only [liftLocal, Effect.bind, initial, failed]

/-- This transaction adapter has separately supplied allocation decisions; it
must retain the surrounding cursor rather than resetting it to the value-only
transaction projection's zero. Consuming insertion events is a further adapter. -/
theorem observed_insert_cursor (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (succeeds : Storage.Allocation → Bool) (before : Heap) :
    (observedInsert cell key deterministic succeeds before).2.allocationCursor = before.allocationCursor := by
  cases present : before.representatives <;> simp only [observedInsert, present]

theorem publish_cursor (succeeds : Bool) (key : Key) (id : NodeId) (before : Heap) :
    (publish succeeds key id before).2.allocationCursor = before.allocationCursor := by
  cases succeeds <;> rfl

end Compiler.Extraction.Interner
