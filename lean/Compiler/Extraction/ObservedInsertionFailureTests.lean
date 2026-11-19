/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ObservedInsertionFailure
import Compiler.Extraction.InsertionEffects

namespace Compiler.Extraction.Interner.InsertionFailureTests
open Compiler.Algebraic Compiler.Extraction.Cache

def empty (cursor : Nat) : Heap := { observedHeap [] (fun _ => none) with allocationCursor := cursor }

/-- Failure installs no candidate fields and preserves the incoming cursor,
including nonzero cursors. Candidate correctness is a success obligation. -/
theorem preparation_retains_cursor (candidate : Storage.Cell) (key : Key) (cursor : Nat) :
    observedInsert candidate key true (Storage.allocationPolicy false true true true true) (empty cursor) =
      (.error .outOfMemory, empty cursor) :=
  observed_insert_preparation_oom candidate key _ (empty cursor) [] rfl rfl (by decide) (Or.inl rfl)

/-- An advancing allocation stream is a different contract. This equality
prevents a cursor-preserving connection from certifying that adapter by accident. -/
theorem stream_advances_cursor (candidate : Storage.Cell) (key : Key) (cursor : Nat) :
    observedInsertWith candidate key true (fun _ current => (false, current + 1)) (empty cursor) =
      (.error .outOfMemory, empty (cursor + 1)) := by rfl

theorem missing_rows_reject (candidate : Storage.Cell) (key : Key) (deterministic : Bool)
    (policy : Storage.Allocation → Bool) (cursor : Nat) :
    let before : Heap := ⟨fun _ => none, fun _ => none, none, cursor⟩
    observedInsert candidate key deterministic policy before = (.error .safetyFault, before) := by rfl

end Compiler.Extraction.Interner.InsertionFailureTests
