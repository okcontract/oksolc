/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortCaptured

namespace Compiler.Extraction.InsertionSort.Captured
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

theorem insert_head (budget : Nat) (view : View) (state : State) (items : List NodeId) (j : Nat)
    (related : Heap.Related view state items) (inside : j + 1 < items.length) :
    insertUsing (operations budget view) (j + 1) state =
      if less items[j + 1] items[j] then
        match exchange budget view state (j + 1) j with
        | (.error reason, after) => (.error reason, after)
        | (.ok (), after) => insertUsing (operations budget view) j after
      else (.ok (), state) := by
  simp only [insertUsing, operations,
    Heap.read_represents state view items (j + 1) related.valid related.writable related.values inside,
    Heap.read_represents state view items j related.valid related.writable related.values (by omega)]
  split
  · cases exchange budget view state (j + 1) j with
    | mk result after => cases result with
      | error reason => rfl
      | ok value => cases value; rfl
  · rfl

/-- There is one finite call budget adequate for the entire extracted inner
loop. Exhaustion stops at the exact prefix state and keeps a permutation of the
input. Success agrees with the original value-level insertion. -/
theorem insert_refines (view : View) (j : Nat) (state : State) (items : List NodeId)
    (related : Heap.Related view state items) (inside : j < items.length ∨ j = 0) :
    ∃ result after values, Settles (fun budget => insertUsing (operations budget view) j state) (result, after) ∧
      Heap.Related view after values ∧ values.Perm items ∧ HeapFrame view state after ∧
      ((result = .ok () ∧ insert j items = .ok values) ∨ result = .error (.memory .outOfMemory)) := by
  induction j generalizing state items with
  | zero => exact ⟨.ok (), state, items, ⟨0, fun _ _ => rfl⟩, related, .refl _, .refl _ _, Or.inl ⟨rfl, rfl⟩⟩
  | succ j ih =>
    have current : j + 1 < items.length := by omega
    have previous : j < items.length := by omega
    by_cases compared : less items[j + 1] items[j] = true
    · obtain ⟨result, middle, ⟨budget, settled⟩, frame, effect⟩ := exchange_refines view state items j related current
      dsimp only at settled
      rcases effect with ⟨failed, same⟩ | ⟨success, connected, _⟩
      · subst middle
        subst result
        refine ⟨_, state, items, ⟨budget, ?_⟩, related, .refl _, frame, Or.inr rfl⟩
        intro fuel enough
        change insertUsing (operations fuel view) (j + 1) state = _
        rw [insert_head fuel view state items j related current, if_pos compared, settled fuel enough]
      · subst result
        obtain ⟨result, after, values, ⟨restBudget, rest⟩, relatedAfter, permutation, framed, effect⟩ :=
          ih middle ((items.set (j + 1) items[j]).set j items[j + 1]) connected (Or.inl (by simpa using previous))
        dsimp only at rest
        refine ⟨result, after, values, ⟨budget + restBudget, ?_⟩, relatedAfter,
          permutation.trans (adjacent_exchange items j current), frame.trans framed, ?_⟩
        · intro fuel enough
          change insertUsing (operations fuel view) (j + 1) state = _
          rw [insert_head fuel view state items j related current, if_pos compared, settled fuel (by omega)]
          exact rest fuel (by omega)
        · rcases effect with ⟨success, evaluated⟩ | failed
          · refine Or.inl ⟨success, ?_⟩
            simpa only [insert_succ, List.getElem?_eq_getElem current, List.getElem?_eq_getElem previous,
              if_pos compared] using evaluated
          · exact Or.inr failed
    · refine ⟨.ok (), state, items, ⟨0, ?_⟩, related, .refl _, .refl _ _, Or.inl ⟨rfl, ?_⟩⟩
      · intro fuel _
        change insertUsing (operations fuel view) (j + 1) state = _
        rw [insert_head fuel view state items j related current, if_neg compared]
      · simp only [insert_succ, List.getElem?_eq_getElem current, List.getElem?_eq_getElem previous, if_neg compared]

theorem passes_refines (view : View) (fuel stop i : Nat) (state : State) (items : List NodeId)
    (related : Heap.Related view state items) (length : items.length = stop) (enough : stop - i < fuel) :
    ∃ result after values, Settles (fun budget => passesUsing (operations budget view) fuel stop i state) (result, after) ∧
      Heap.Related view after values ∧ values.Perm items ∧ HeapFrame view state after ∧
      ((result = .ok () ∧ passes fuel stop i items = .ok values) ∨ result = .error (.memory .outOfMemory)) := by
  induction fuel generalizing i state items with
  | zero => omega
  | succ fuel ih =>
    by_cases guard : i < stop
    · obtain ⟨result, middle, values, ⟨budget, settled⟩, connected, permutation, frame, effect⟩ :=
        insert_refines view i state items related (Or.inl (by omega))
      dsimp only at settled
      rcases effect with ⟨success, evaluated⟩ | failed
      · subst result
        obtain ⟨result, after, final, ⟨restBudget, rest⟩, relatedAfter, permuted, framed, effect⟩ :=
          ih (i + 1) middle values connected (permutation.length_eq.trans length) (by omega)
        dsimp only at rest
        refine ⟨result, after, final, ⟨budget + restBudget, ?_⟩, relatedAfter,
          permuted.trans permutation, frame.trans framed, ?_⟩
        · intro limit sufficient
          change passesUsing (operations limit view) (fuel + 1) stop i state = _
          rw [passesUsing, if_pos guard, settled limit (by omega)]
          exact rest limit (by omega)
        · rcases effect with ⟨success, finished⟩ | failed
          · refine Or.inl ⟨success, ?_⟩
            rw [passes_succ, if_pos guard, evaluated]
            exact finished
          · exact Or.inr failed
      · subst result
        refine ⟨_, middle, values, ⟨budget, ?_⟩, connected, permutation, frame, Or.inr rfl⟩
        intro limit sufficient
        change passesUsing (operations limit view) (fuel + 1) stop i state = _
        rw [passesUsing, if_pos guard, settled limit sufficient]
    · refine ⟨.ok (), state, items, ⟨0, ?_⟩, related, .refl _, .refl _ _, Or.inl ⟨rfl, ?_⟩⟩
      · intro limit _
        change passesUsing (operations limit view) (fuel + 1) stop i state = _
        rw [passesUsing, if_neg guard]
      · rw [passes_succ, if_neg guard]

/-- Full source-bound sort control using the captured AIR call. Every admitted
input has a finite uniform call budget; every larger budget yields this same
terminal result. Success produces sortIds. OOM preserves the exact partially
sorted permutation and unrelated heap observations. OOM is never success. -/
theorem run_refines (view : View) (state : State) (items : List NodeId) (related : Heap.Related view state items) :
    ∃ result after values, Settles (fun budget => run budget state view) (result, after) ∧
      Heap.Related view after values ∧ values.Perm items ∧ HeapFrame view state after ∧
      ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) := by
  obtain ⟨result, after, values, ⟨budget, settled⟩, connected, permutation, frame, effect⟩ :=
    passes_refines view (view.length + 1) view.length 1 state items related related.values.1 (by omega)
  refine ⟨result, after, values, ⟨budget, ?_⟩, connected, permutation, frame, ?_⟩
  · intro fuel enough
    simpa only [run, if_pos (view_width state view related.valid related.writable), runUsing] using settled fuel enough
  · rcases effect with ⟨success, evaluated⟩ | failed
    · have projected : InsertionSort.run items = .ok values := by
        simpa only [run_passes, related.values.1] using evaluated
      exact Or.inl ⟨success, Result.ok.inj (projected.symm.trans (run_sortIds items))⟩
    · exact Or.inr failed

end Compiler.Extraction.InsertionSort.Captured
