/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortHeap

namespace Compiler.Extraction.InsertionSort.Heap
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

structure Related (view : View) (state : State) (items : List NodeId) : Prop where
  valid : state.valid = true
  writable : Writable state view
  values : Represents state view items

private theorem insert_head (view : View) (state : State) (items : List NodeId) (j : Nat)
    (related : Related view state items) (inside : j + 1 < items.length) :
    insertUsing (operations view) (j + 1) state =
      if less items[j + 1] items[j] then
        match exchange view state (j + 1) j with
        | (.error reason, after) => (.error reason, after)
        | (.ok (), after) => insertUsing (operations view) j after
      else (.ok (), state) := by
  simp only [insertUsing, operations,
    read_represents state view items (j + 1) related.valid related.writable related.values inside,
    read_represents state view items j related.valid related.writable related.values (by omega)]
  split
  · cases exchange view state (j + 1) j with
    | mk result after => cases result with
      | error reason => rfl
      | ok value => cases value; rfl
  · rfl

theorem insert_refines (view : View) (j : Nat) (state : State) (items : List NodeId)
    (related : Related view state items) (inside : j < items.length ∨ j = 0) :
    ∃ sorted after, insertUsing (operations view) j state = (.ok (), after) ∧
      insert j items = .ok sorted ∧ Related view after sorted ∧ sorted.Perm items ∧ Frame view state after := by
  induction j generalizing state items with
  | zero => exact ⟨items, state, rfl, rfl, related, .refl _, .refl _ _⟩
  | succ j ih =>
    have current : j + 1 < items.length := by omega
    have previous : j < items.length := by omega
    rw [insert_head view state items j related current, insert_succ,
      List.getElem?_eq_getElem current, List.getElem?_eq_getElem previous]
    by_cases compared : less items[j + 1] items[j] = true
    · simp only [if_pos compared]
      obtain ⟨middle, exchanged, valid, writable, values, frame⟩ :=
        exchange_refines state view items j related.valid related.writable related.values current
      rw [exchanged]
      obtain ⟨sorted, after, executed, evaluated, connected, permutation, framed⟩ :=
        ih middle ((items.set (j + 1) items[j]).set j items[j + 1])
          ⟨valid, writable, values⟩ (Or.inl (by simpa using previous))
      exact ⟨sorted, after, executed, evaluated, connected,
        permutation.trans (adjacent_exchange items j current), frame.trans framed⟩
    · simp only [if_neg compared]
      exact ⟨items, state, rfl, rfl, related, .refl _, .refl _ _⟩

theorem passes_refines (view : View) (fuel stop i : Nat) (state : State) (items : List NodeId)
    (related : Related view state items) (length : items.length = stop) (enough : stop - i < fuel) :
    ∃ sorted after, passesUsing (operations view) fuel stop i state = (.ok (), after) ∧
      passes fuel stop i items = .ok sorted ∧ Related view after sorted ∧
      sorted.Perm items ∧ Frame view state after := by
  induction fuel generalizing i state items with
  | zero => omega
  | succ fuel ih =>
    rw [passesUsing, passes_succ]
    by_cases guard : i < stop
    · rw [if_pos guard, if_pos guard]
      obtain ⟨middleItems, middle, executed, evaluated, connected, permutation, frame⟩ :=
        insert_refines view i state items related (Or.inl (by omega))
      rw [executed, evaluated]
      obtain ⟨sorted, after, executed, evaluated, connected, permuted, framed⟩ :=
        ih (i + 1) middle middleItems connected (permutation.length_eq.trans length) (by omega)
      exact ⟨sorted, after, executed, evaluated, connected, permuted.trans permutation, frame.trans framed⟩
    · rw [if_neg guard, if_neg guard]
      exact ⟨items, state, rfl, rfl, related, .refl _, .refl _ _⟩

/-- Complete terminating heap execution agrees with the source-bound value
sort. No successful read/write, exchange, run or sufficient-fuel premise. -/
theorem run_refines (view : View) (state : State) (items : List NodeId) (related : Related view state items) :
    ∃ after, run state view = (.ok (), after) ∧ Related view after (sortIds items) ∧ Frame view state after := by
  obtain ⟨sorted, after, executed, evaluated, connected, framed⟩ :=
    passes_refines view (view.length + 1) view.length 1 state items related related.values.1 (by omega)
  have projected : InsertionSort.run items = .ok sorted := by
    simpa only [run_passes, related.values.1] using evaluated
  have same : sorted = sortIds items := Result.ok.inj (projected.symm.trans (run_sortIds items))
  subst sorted
  exact ⟨after, by simpa only [run, if_pos (view_width state view related.valid related.writable), runUsing] using executed,
    connected, framed.2⟩

/-- Determinism turns the existential construction into a guarantee for every
observed invocation result, including exclusion of modeled memory faults. -/
theorem run_result (view : View) (state after : State) (items : List NodeId) (result : Except Fault Unit)
    (related : Related view state items) (executed : run state view = (result, after)) :
    result = .ok () ∧ Related view after (sortIds items) ∧ Frame view state after := by
  obtain ⟨final, ran, connected, frame⟩ := run_refines view state items related
  have same := Prod.mk.inj (executed.symm.trans ran)
  cases same.1
  cases same.2
  exact ⟨rfl, connected, frame⟩

end Compiler.Extraction.InsertionSort.Heap
