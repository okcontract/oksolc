/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionExecutionAction
import Compiler.Extraction.StorageExecutionTraceTests

namespace Compiler.Extraction.Interner.InsertionExecution.ActionTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (cell key binding denotation)

def captured (failure : Option Allocation := none) (releaseFault : Option Release := none) :=
  insertProgram.execute ⟨true, true, fun _ => false⟩
    (Trace.record (ExecutionTests.operations failure false releaseFault)) {} ⟨[], []⟩

def run (failure : Option Allocation := none) (releaseFault : Option Release := none) :=
  action cell key true (Trace.replay (captured failure releaseFault).2.events ExecutionTests.Fault.cleanup) callerHeap

theorem success : run.1 = .ok 1 ∧ run.2.allocationCursor = 5 ∧ run.2.representatives = some [caller, cell] :=
  ⟨by rfl', by rfl', by rfl'⟩

/-- Publication refusal runs all three cleanup callbacks. The cursor records
eight protocol calls, rather than only the five allocation attempts. -/
theorem publication_oom : (run (some .publish)).1 = .error .outOfMemory ∧
    (run (some .publish)).2 = { callerHeap with allocationCursor := 8 } := ⟨by rfl', by rfl'⟩

/-- A fault in pop retains the already executed last-value cleanup, stops
before normalized cleanup and does not manufacture an ordinary OOM rollback. -/
theorem stopped_cleanup_fault : (run (some .publish) (some .pop)).1 = .error .safetyFault ∧
    (run (some .publish) (some .pop)).2.allocationCursor = 7 ∧
    (run (some .publish) (some .pop)).2.representatives = some [caller, cell] := ⟨by rfl', by rfl', by rfl'⟩

theorem exhausted_trace :
    action cell key true (Trace.replay [] ExecutionTests.Fault.cleanup) callerHeap =
      (.error .safetyFault, { callerHeap with allocationCursor := 1 }) := by rfl'

theorem missing_representatives (cursor : Nat) :
    action cell key true (Trace.replay [] ExecutionTests.Fault.cleanup) { callerHeap with representatives := none, allocationCursor := cursor } =
      (.error .safetyFault, { callerHeap with representatives := none, allocationCursor := cursor }) := rfl

/-- The existing source-controlled family supplies semantic preservation with
the same replayed decisions; no fixture-specific successful policy is chosen. -/
theorem ordinary_words (failure : Option Allocation) (outcome : Option Outcome)
    (completed : (ExecutionTests.run true true failure).1.1 = .ok outcome) :
    Invariant model (run failure).2 ∧ Stable callerHeap (run failure).2 ∧
      match (run failure).1 with | .error _ => True | .ok id => (run failure).2.read id = some cell.value := by
  have replayed := (Trace.Tests.existing_family true true failure false none [] []).2
  have returned := congrArg (fun ran => ran.1.1) replayed
  simp only [List.nil_append, List.append_nil] at returned
  have ordinary := returned.trans completed
  exact (action_verified model cell key true _ callerHeap [caller] outcome rfl caller_valid binding denotation ordinary).2

end Compiler.Extraction.Interner.InsertionExecution.ActionTests
