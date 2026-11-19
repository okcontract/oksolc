/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionTests
import Compiler.Extraction.InsertionExecutionPolicy

namespace Compiler.Extraction.Storage.ExecutionPolicyTests
open ExecutionTests Compiler.Algebraic Compiler.Extraction.Cache

/-- Existing success and all five allocation-failure cases specialize the same
general policy theorem, in both ownership modes. -/
theorem fixture_outcomes (deterministic : Bool) (failure : Option Allocation) :
    ∃ outcome, (run deterministic true failure).1.1 = .ok outcome ∧
      (insertProgram.run ⟨deterministic, true, executionPolicy (operations failure) deterministic []⟩ {}).1 = outcome := by
  have ordinary : ∃ outcome, (run deterministic true failure).1.1 = .ok outcome := by
    cases deterministic <;> cases failure with
    | none => exact ⟨some .success, by rfl'⟩
    | some site =>
      cases site
      all_goals first
        | exact ⟨some .allocationFailure, by rfl'⟩
        | exact ⟨some .success, by rfl'⟩
  obtain ⟨outcome, completed⟩ := ordinary
  exact ⟨outcome, completed, insert_execution_policy ⟨deterministic, true, fun _ => false⟩
    (operations failure) [] outcome completed⟩

theorem fixture_graph (cells : List Cell) (table : Table) (candidate : Cell) (key : Key)
    (deterministic : Bool) (failure : Option Allocation)
    (room : decide (cells.length < 2 ^ 32 - 1) = true) :
    ∃ outcome, (run deterministic true failure).1.1 = .ok outcome ∧
      Interner.observedInsertTransaction cells table candidate key deterministic
        (executionPolicy (operations failure) deterministic []) =
      (Interner.insertionOutcome cells outcome, Interner.InsertionExecution.project cells table candidate key
        (run deterministic true failure).1.2) := by
  obtain ⟨outcome, completed, _⟩ := fixture_outcomes deterministic failure
  refine ⟨outcome, completed, ?_⟩
  have checked := Interner.InsertionExecution.observed cells table candidate key deterministic (operations failure) [] outcome
    (by simpa only [room] using completed)
  simpa only [room] using checked

/-- Creation observes the duplicate's changed private state. Final cleanup
changes it again, without changing the allocation policy's earlier decisions. -/
theorem stateful_policy :
    executionPolicy dependentOperations true 0 .arguments = true ∧
    executionPolicy dependentOperations true 0 .item = false ∧
    (insertProgram.execute ⟨true, true, fun _ => true⟩ dependentOperations {} 0).1.1 = .ok (some .allocationFailure) ∧
    (insertProgram.execute ⟨true, true, fun _ => true⟩ dependentOperations {} 0).2 = 22 :=
  ⟨rfl, rfl, by rfl', by rfl'⟩

theorem attempt_rejection :
    executionPolicy (operations none true) true [] .arguments = false ∧
    (run true true none true).1.1 = .error .allocation :=
  ⟨rfl, allocation_fault.1⟩

theorem cleanup_rejection :
    executionPolicy (operations (some .publish) false (some .pop)) true [] .publish = false ∧
    (run true true (some .publish) false (some .pop)).1.1 = .error .cleanup :=
  ⟨rfl, cleanup_fault.1⟩

/-- This callback depends on the reached owner. The default empty owner is
rejected, so the old ownership-blind callback premises cannot justify it. Cleanup
rejects if invoked; actual success must transfer all owners without calling it. -/
def ownerSensitive : Operations Nat Fault where
  attempt site owner effects :=
    (.ok (match site with
      | .arguments => owner.flag .normalized
      | .item => owner.flag .arguments
      | .clone => owner.flag .allocation
      | .append => owner.flag .value
      | .publish => owner.appended && !owner.flag .value), effects + 1)
  release _ _ effects := (.error .cleanup, effects + 100)

theorem ownership_sensitive_success (deterministic : Bool) (effects : Nat) :
    (insertProgram.execute ⟨deterministic, true, fun _ => false⟩ ownerSensitive {} effects).1.1 = .ok (some .success) ∧
    (insertProgram.execute ⟨deterministic, true, fun _ => false⟩ ownerSensitive {} effects).2 =
      effects + if deterministic then 5 else 3 := by
  cases deterministic <;> exact ⟨by rfl', by rfl'⟩

theorem ownership_sensitive_preparation (deterministic : Bool) (effects : Nat) :
    executionPreparation ownerSensitive deterministic effects = effects + if deterministic then 3 else 2 := by
  cases deterministic <;> rfl

theorem ownership_sensitive_observations (deterministic : Bool) (effects : Nat) :
    let prepared := executionPreparation ownerSensitive deterministic effects
    let appended := ownerSensitive.attempt .append (executionOwner deterministic .append) prepared
    appended.1 = .ok true ∧ (deterministic = true →
      (ownerSensitive.attempt .publish publicationOwnership appended.2).1 = .ok true) :=
  ⟨(insert_execution_success ownerSensitive deterministic true effects (ownership_sensitive_success deterministic effects).1).1,
    (insert_execution_success ownerSensitive deterministic true effects (ownership_sensitive_success deterministic effects).1).2.1⟩

theorem wrong_owner_rejected (effects : Nat) :
    ownerSensitive.attempt .item {} effects = (.ok false, effects + 1) := rfl

end Compiler.Extraction.Storage.ExecutionPolicyTests
