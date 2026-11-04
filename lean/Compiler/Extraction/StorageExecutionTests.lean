/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionExecution
import Compiler.Extraction.ObservedStorageTests

namespace Compiler.Extraction.Storage.ExecutionTests

inductive Event where
  | attempt (site : Allocation) (appended : Bool)
  | release (action : Release) (appended : Bool)
  deriving DecidableEq, Repr

inductive Fault where
  | allocation | cleanup
  deriving DecidableEq, Repr

def operations (failure : Option Allocation := none) (attemptFault : Bool := false)
    (releaseFault : Option Release := none) : Operations (List Event) Fault where
  attempt site state trace :=
    (if attemptFault then .error .allocation else .ok (failure != some site),
      trace ++ [.attempt site state.appended])
  release action state trace :=
    (if releaseFault = some action then .error .cleanup else .ok (),
      trace ++ [.release action state.appended])

def run (deterministic := true) (room := true) (failure : Option Allocation := none)
    (attemptFault := false) (releaseFault : Option Release := none) :=
  insertProgram.execute ⟨deterministic, room, fun _ => false⟩
    (operations failure attemptFault releaseFault) {} []

theorem deterministic_success : (run).1.1 = .ok (some .success) ∧
    (run).2 = [.attempt .arguments false, .attempt .item false, .attempt .clone false,
      .attempt .append false, .attempt .publish true] := ⟨by rfl', by rfl'⟩

theorem nondeterministic_success : (run false).1.1 = .ok (some .success) ∧
    (run false).2 = [.attempt .item false, .attempt .clone false, .attempt .append false] ∧
    (run false).1.2.owner .normalized = .graph := ⟨by rfl', by rfl', by rfl'⟩

theorem capacity_cleanup (deterministic : Bool) :
    (run deterministic false).1.1 = .ok (some .capacityFailure) ∧
    (run deterministic false).2 = [.release .normalized false] ∧
    (run deterministic false).1.2.owner .normalized = .freed := ⟨by rfl', by rfl', by rfl'⟩

theorem duplicate_failure : (run true true (some .arguments)).1.1 = .ok (some .allocationFailure) ∧
    (run true true (some .arguments)).2 = [.attempt .arguments false, .release .normalized false] := ⟨by rfl', by rfl'⟩

theorem item_failure : (run true true (some .item)).2 =
    [.attempt .arguments false, .attempt .item false, .release .arguments false, .release .normalized false] := by rfl'

theorem clone_failure : (run true true (some .clone)).2 =
    [.attempt .arguments false, .attempt .item false, .attempt .clone false,
      .release .allocation false, .release .arguments false, .release .normalized false] := by rfl'

theorem append_failure : (run true true (some .append)).2 =
    [.attempt .arguments false, .attempt .item false, .attempt .clone false, .attempt .append false,
      .release .value false, .release .allocation false, .release .arguments false, .release .normalized false] := by rfl'

theorem publication_failure : (run true true (some .publish)).1.1 = .ok (some .allocationFailure) ∧
    (run true true (some .publish)).2 =
      [.attempt .arguments false, .attempt .item false, .attempt .clone false, .attempt .append false,
        .attempt .publish true, .release .lastValue true, .release .pop true, .release .normalized false] ∧
    (run true true (some .publish)).1.2.appended = false := ⟨by rfl', by rfl', by rfl'⟩

theorem aliased_failure : (run false true (some .clone)).2 =
    [.attempt .item false, .attempt .clone false, .release .allocation false, .release .arguments false] ∧
    (run false true (some .clone)).1.2.owner .normalized = .freed := ⟨by rfl', by rfl'⟩

theorem allocation_fault : (run true true none true).1.1 = .error .allocation ∧
    (run true true none true).2 = [.attempt .arguments false] ∧
    (run true true none true).1.2.owner .normalized = .local := ⟨by rfl', by rfl', by rfl'⟩

theorem cleanup_fault : (run true true (some .publish) false (some .pop)).1.1 = .error .cleanup ∧
    (run true true (some .publish) false (some .pop)).2 =
      [.attempt .arguments false, .attempt .item false, .attempt .clone false, .attempt .append false,
        .attempt .publish true, .release .lastValue true, .release .pop true] ∧
    (run true true (some .publish) false (some .pop)).1.2.appended = true ∧
    (run true true (some .publish) false (some .pop)).1.2.owner .value = .freed ∧
    (run true true (some .publish) false (some .pop)).1.2.owner .normalized = .local :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

/-- A nested scope can clean up and then fall through. The next allocation must
observe that cleanup, so an allocation-only policy cannot drive this execution. -/
def continuationProgram : Program := .branch .deterministic
  (.scope false (.sequence [.normalized]) .done) .done
  (.command .createItem .ret)

def dependentOperations : Operations Nat Fault where
  attempt _ _ effects := (.ok (effects == 0), effects + 10)
  release _ _ effects := (.ok (), effects + 1)

theorem cleanup_changes_later_allocation :
    (continuationProgram.execute ⟨true, true, fun _ => true⟩ dependentOperations {} 0).1.1 = .ok (some .allocationFailure) ∧
    (continuationProgram.execute ⟨true, true, fun _ => true⟩ dependentOperations {} 0).2 = 11 := ⟨rfl, rfl⟩

/-- An ordinary error is not a semantic fault. Even failed capacity cleanup
retains the deallocator's effects and rejects the whole observation. -/
theorem capacity_cleanup_fault :
    (run true false none false (some .normalized)).1.1 = .error .cleanup ∧
    (run true false none false (some .normalized)).2 = [.release .normalized false] := ⟨by rfl', by rfl'⟩

open Compiler.Extraction.Interner
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (cell key binding denotation)

def projected (failure : Option Allocation := none) :=
  InsertionExecution.project [caller] (fun _ => none) cell key (run true true failure).1.2

/-- The same execution is used by the composed ownership/word theorem, including
late publication OOM. The cell/key witnesses come from the existing interner fixture. -/
theorem semantic_execution (failure : Option Allocation) (outcome : Option Outcome)
    (completed : (run true true failure).1.1 = .ok outcome) :
    SafeResult true (outcome, (run true true failure).1.2) ∧
      Invariant model (projected failure) ∧ Stable callerHeap (projected failure) ∧
      match insertionOutcome [caller] outcome with
      | .error _ => True
      | .ok id => (projected failure).read id = some cell.value :=
  InsertionExecution.verified model [caller] (fun _ => none) cell key true (operations failure) [] outcome
    caller_valid binding denotation completed

theorem success_words : Invariant model projected ∧ Stable callerHeap projected ∧
    projected.read 1 = some cell.value := (semantic_execution none _ deterministic_success.1).2

theorem failures_restore (site : Allocation) : projected (some site) = callerHeap := by
  cases site <;> rfl'

end Compiler.Extraction.Storage.ExecutionTests
