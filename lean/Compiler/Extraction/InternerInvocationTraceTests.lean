/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInvocationTrace
import Compiler.Extraction.InsertionExecutionActionTests

namespace Compiler.Extraction.Interner.InvocationTrace.Tests
open Compiler.Extraction.Cache

/-- None of normalization's three callbacks can consume an insertion event
merely because it occupies the next index. -/
theorem normalization_foreign (leading trailing : List (Event Unit Unit)) (lookup : NormalizationOwnership.State) :
    let events := leading ++ [.insertion (.attempt .arguments {} (.ok true))] ++ trailing
    let calls := NormalizationOwnership.Trace.replay (normalizations events) ()
    calls.allocate .temporary leading.length = (false, events.length + 1) ∧
      calls.prepare lookup leading.length = (.error (), events.length + 1) ∧
      calls.release lookup leading.length = events.length + 1 := by
  simp [normalizations, normalization, NormalizationOwnership.Trace.replay, NormalizationOwnership.Trace.allocate,
    NormalizationOwnership.Trace.prepare, NormalizationOwnership.Trace.release, NormalizationOwnership.Trace.rejected]

theorem insertion_foreign (leading trailing : List (Event Unit Unit)) (owner : Storage.State) :
    let events := leading ++ [.normalization (.allocate .temporary true)] ++ trailing
    let calls := operations events ()
    calls.attempt .arguments owner leading.length = (.error (), events.length + 1) ∧
      calls.release .arguments owner leading.length = (.error (), events.length + 1) := by
  simp [operations, insertions, insertion, Storage.Trace.replay]

/-- Do not scan forward over another protocol's call to find a matching one. -/
theorem no_skipping :
    (operations ([.normalization (.allocate .temporary true), .insertion (.attempt .arguments {} (.ok true))] :
      List (Event Unit Unit)) ()).attempt .arguments {} 0 = (.error (), 3) := rfl

/-- The total allocation projection returns false on a foreign slot, but its
poisoned cursor prevents checked admission from treating that as ordinary OOM. -/
theorem foreign_admission :
    let events : List (Event Unit Unit) := [.insertion (.attempt .arguments {} (.ok true))]
    let projected := normalizations events
    let selected := (NormalizationOwnership.Trace.replay projected ()).allocate .temporary 0
    NormalizationOwnership.Trace.Scope.admit projected
      ((.ok () : Except (Unit × NormalizationOwnership.State) Unit), selected.2) () = .error (.mismatch 2) := rfl

theorem publication_views (key : Key) (accepted : Bool) :
    normalizations ([.publicationProbe key accepted] : List (Event Unit Unit)) = [.foreign] ∧
      insertions ([.publicationProbe key accepted] : List (Event Unit Unit)) = [.foreign] := ⟨rfl, rfl⟩

theorem publication_foreign (leading trailing : List (Event Unit Unit)) (key : Key)
    (id : Compiler.Algebraic.NodeId) (before : Heap) :
    let events := leading ++ [.normalization (.allocate .temporary true)] ++ trailing
    publish events key id { before with allocationCursor := leading.length } =
      (.error .safetyFault, { before with allocationCursor := events.length + 1 }) := by
  simp [publish]

theorem publication_wrong_key (leading trailing : List (Event Unit Unit)) (key other : Key)
    (id : Compiler.Algebraic.NodeId) (accepted : Bool) (before : Heap) (different : other ≠ key) :
    let events := leading ++ [.publicationProbe other accepted] ++ trailing
    publish events key id { before with allocationCursor := leading.length } =
      (.error .safetyFault, { before with allocationCursor := events.length + 1 }) := by
  simp [publish, different]

theorem publication_no_skipping (key : Key) (id : Compiler.Algebraic.NodeId) (before : Heap) :
    publish ([.insertion (.attempt .arguments {} (.ok true)), .publicationProbe key true] : List (Event Unit Unit))
      key id { before with allocationCursor := 0 } = (.error .safetyFault, { before with allocationCursor := 3 }) := rfl

theorem publication_exhausted (key : Key) (id : Compiler.Algebraic.NodeId) (before : Heap) :
    publish ([] : List (Event Unit Unit)) key id { before with allocationCursor := 0 } =
      (.error .safetyFault, { before with allocationCursor := 1 }) := rfl

theorem insertion_slot (leading trailing : List (Event Unit Unit)) (owner : Storage.State) (result : Except Unit Bool) :
    (operations (leading ++ [.insertion (.attempt .arguments owner result)] ++ trailing) ()).attempt .arguments owner leading.length =
      (result, leading.length + 1) := by
  simp [operations, insertions, insertion, Storage.Trace.replay]

theorem normalization_slot (leading trailing : List (Event Unit Unit)) (result : Bool) :
    (resources (leading ++ [.normalization (.allocate .temporary result)] ++ trailing) ()).allocate .temporary [] leading.length =
      (result, leading.length + 1) := by
  simp [resources, normalizations, normalization, NormalizationOwnership.Trace.Scope.resources, NormalizationOwnership.Trace.allocate]

/-- Reuse the effectful publication-OOM fixture. Both foreign neighbors remain
in place; insertion consumes all eight calls, including its three releases. -/
theorem cleanup_cursor :
    let captured := InsertionExecution.ActionTests.captured (some .publish)
    let events : List (Event Unit Storage.ExecutionTests.Fault) :=
      [.normalization (.allocate .temporary true)] ++ captured.2.events.map Event.insertion ++ [.normalization (.release {})]
    let before := { ObservedTests.callerHeap with allocationCursor := 1 }
    let result := InsertionExecution.action ObservedStorageTests.cell ObservedStorageTests.key true
      (operations events .cleanup) before
    result = (.error .outOfMemory, { ObservedTests.callerHeap with allocationCursor := 9 }) := by rfl'

end Compiler.Extraction.Interner.InvocationTrace.Tests
