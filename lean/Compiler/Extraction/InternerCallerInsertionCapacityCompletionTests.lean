/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionCapacityCompletion
import Compiler.Extraction.InternerCallerInsertionCapacityTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CompletionTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- The new caller adapter uses precisely the existing native executor and
reached projection on the initialized chain, for arbitrary operation responses
and either determinism setting. -/
theorem initialized_body (safety empty deterministic : Bool) (actions : Operations Nat)
    (reserve : Backing.Registry.Allocate Nat) :
    Native.insert actions reserve safety 7 6 (parent empty) source Insertion.Tests.model input (key empty)
      (normalized safety empty 4) deterministic (some growth) (taken safety empty 4).2.world =
    insertWith actions safety empty (normalized safety empty 4) reserve deterministic (taken safety empty 4).2.world := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have rows : (taken safety empty 4).2.world.graph.representatives = some (cells safety empty 4) := by
    rw [entry.origin.graph]; exact prior.facts.projected
  have checked := CapacityTests.initialized_entry safety empty deterministic actions reserve (some growth)
  simp only [Native.insert, rows, body, checked, insertWith, Option.getD_some, selectedGrowth, prior.count, ↓reduceIte]
  generalize execution actions reserve safety 7 6 (parent empty) source Insertion.Tests.model input (key empty)
    (normalized safety empty 4) deterministic (cells safety empty 4) (taken safety empty 4).2.world (some growth) = ran
  obtain ⟨⟨result, owner⟩, after⟩ := ran
  rfl

def completed (safety empty clone : Bool) := finishInsertion (TransferredPreparationFailureTests.actions clone) allocate safety 7 6
  (parent empty) source Insertion.Tests.model input (key empty) false (taken safety empty 4).2 (some growth)

/-- Existing caller-derived preparation OOM proofs now run through the concrete
native adapter and actual outer cleanup. The final graph/native facts are not
established by reducing the fixture's final state. -/
theorem preparation_oom (safety empty clone : Bool) :
    completed safety empty clone = (.error (.language .outOfMemory),
      ⟨TransferredPreparationFailureTests.world safety empty clone, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    GraphFacts safety (lifetime empty) 5 (completed safety empty clone).2.world (cells safety empty 4) ∧
    Good (parent empty) (request empty).arguments (completed safety empty clone).2.world ∧
    Consumed (normalized safety empty 4) (completed safety empty clone).2.world.memory := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  obtain ⟨after, ran, _, _⟩ := TransferredPreparationFailureTests.native_contract safety empty clone
  have old := TransferredPreparationFailureTests.completed safety empty clone after ran
  have same : TransferredPreparationFailureTests.world safety empty clone = TransferredPreparationFailureTests.reached safety empty clone :=
    congrArg (fun result => result.2.world) old.1
  have rows : (taken safety empty 4).2.world.graph.representatives.getD [] = cells safety empty 4 := by
    rw [entry.origin.graph, prior.facts.projected]; rfl
  have selected : selectedGrowth (cells safety empty 4) = some growth := by simp only [selectedGrowth, prior.count, ↓reduceIte]
  have result : (insertWith (TransferredPreparationFailureTests.actions clone) safety empty (normalized safety empty 4)
      allocate false (taken safety empty 4).2.world).1 = .error (.language .outOfMemory) := by
    simp only [insertWith, rows, selected]
    change (match (TransferredPreparationFailureTests.executed safety empty clone).1.1 with
      | .error _ => (Except.error (OwnedCall.Fault.language .safetyFault) : Except OwnedCall.Fault NodeId)
      | .ok outcome => (Interner.insertionOutcome (cells safety empty 4) outcome).mapError OwnedCall.Fault.language) = _
    rw [ran]; rfl
  have inserted : insertWith (TransferredPreparationFailureTests.actions clone) safety empty (normalized safety empty 4)
      allocate false (taken safety empty 4).2.world =
      (.error (.language .outOfMemory), TransferredPreparationFailureTests.world safety empty clone) :=
    Prod.ext result same.symm
  have finished := entry.finish_native (TransferredPreparationFailureTests.actions clone) allocate safety 7 6 (parent empty) source
    Insertion.Tests.model (request empty) (values empty) input (key empty) (normalized safety empty 4) (lookup empty)
    (before safety empty 4) (taken safety empty 4).2 false (some growth)
  rw [initialized_body, inserted] at finished
  simp only [ordinary, OwnedCall.Fault.recoverable, ↓reduceIte] at finished
  change completed safety empty clone = _ at finished
  refine ⟨finished, ?_, ?_, ?_⟩
  all_goals rw [finished]
  · exact (TransferredPreparationFailureTests.derived_contract safety empty clone).2.1
  · exact (TransferredPreparationFailureTests.parent_borrow_after_oom safety empty clone).2
  · exact (TransferredPreparationFailureTests.derived_contract safety empty clone).2.2.1

def missingContainer (safety empty : Bool) := (taken safety empty 4).2.world.memory.memory.nextId

theorem missing_owner (safety empty : Bool) :
    checkedCount (taken safety empty 4).2.world.memory.memory (missingContainer safety empty) (cells safety empty 4) = .error (.memory .unallocated) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

def rejected (safety empty deterministic : Bool) := finishInsertion ops allocate safety 7 (missingContainer safety empty) (parent empty) source
  Insertion.Tests.model input (key empty) deterministic (taken safety empty 4).2 (some growth)

theorem rejection_retains_owner (safety empty deterministic : Bool) :
    rejected safety empty deterministic = (.error (.language .safetyFault),
      ⟨(taken safety empty 4).2.world, ⟨some (lookup empty), some (normalized safety empty 4), true⟩⟩) ∧
    Memory.SliceValid 7 (rejected safety empty deterministic).2.world.memory.heap (normalized safety empty 4) ∧
    ordinary (rejected safety empty deterministic).1 = false := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have finished := entry.rejected_completed ops allocate safety 7 (missingContainer safety empty) (parent empty) source Insertion.Tests.model
    (request empty) (values empty) input (key empty) (normalized safety empty 4) (lookup empty) (before safety empty 4)
    (taken safety empty 4).2 deterministic (cells safety empty 4) (some growth) prior.facts.projected (.memory .unallocated)
    (missing_owner safety empty)
  change rejected safety empty deterministic = _ at finished
  refine ⟨finished, ?_, ?_⟩
  · rw [finished]; exact entry.origin.held.2.1
  · rw [finished]; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.CompletionTests
