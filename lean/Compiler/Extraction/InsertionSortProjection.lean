/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortProgram

namespace Compiler.Extraction.InsertionSort
open Compiler.Algebraic

theorem insert_zero (items : List NodeId) : insert 0 items = .ok items := rfl

/-- Recover the original value-level equation from shared executable control.
The memory instance therefore does not require a second copy of the loops. -/
theorem insert_succ (j : Nat) (items : List NodeId) :
    insert (j + 1) items =
      match items[j + 1]?, items[j]? with
      | some current, some previous =>
        if less current previous then insert j ((items.set (j + 1) previous).set j current)
        else .ok items
      | _, _ => .fault .bounds items := by
  cases current : items[j + 1]? with
  | none => simp [insert, insertUsing, listOperations, current, Result.fromOutcome]
  | some a =>
    cases previous : items[j]? with
    | none => simp [insert, insertUsing, listOperations, current, previous, Result.fromOutcome]
    | some b =>
      by_cases compared : less a b = true <;>
        simp [insert, insertUsing, listOperations, current, previous, compared, Result.fromOutcome]

theorem passes_zero (stop i : Nat) (items : List NodeId) :
    passes 0 stop i items = .fault .incomplete items := rfl

theorem passes_succ (fuel stop i : Nat) (items : List NodeId) :
    passes (fuel + 1) stop i items =
      if i < stop then
        match insert i items with
        | .fault reason after => .fault reason after
        | .ok after => passes fuel stop (i + 1) after
      else .ok items := by
  by_cases guard : i < stop
  · cases ran : insertUsing listOperations i items with
    | mk result after =>
      cases result with
      | error fault => simp [passes, passesUsing, insert, ran, guard, Result.fromOutcome]
      | ok value => cases value; simp [passes, passesUsing, insert, ran, guard, Result.fromOutcome]
  · simp [passes, passesUsing, guard, Result.fromOutcome]

theorem run_passes (items : List NodeId) : run items = passes (items.length + 1) items.length 1 items := rfl

end Compiler.Extraction.InsertionSort
