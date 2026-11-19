/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionTransferredGrowthSetupTests
import Compiler.Extraction.InternerCallerTransferredPreparationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredPreparationFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

abbrev object := TransferredGrowthTests.object

/-- Both ordinary preparation failures occur after the actual sixth caller has
normalized and transferred its arguments. The preceding five rows were created
and published by the initialized source execution. -/
def actions (clone : Bool) : Operations Nat := { ops with
  create := fun wanted before => if clone then ops.create wanted before else (none, before.effects * 10 + 5)
  copy := fun _ before => (none, before.effects * 10 + 6) }
def made (safety empty clone : Bool) := AssemblyItem.Creation.create (observe (actions clone).create) 7 input.item (taken safety empty 4).2.world.memory
def cloned (safety empty : Bool) := AssemblyClone.Physical.run (observe (actions true).copy) 7 input (made safety empty true).2
def failed (safety empty clone : Bool) := if clone then (cloned safety empty).2 else (made safety empty false).2
def outcome (safety empty clone : Bool) := invokeWith (actions clone) safety empty (before safety empty 4) allocate false
def world (safety empty clone : Bool) := (outcome safety empty clone).2.world
def executed (safety empty clone : Bool) := execution (actions clone) allocate safety 7 6 (parent empty) source Insertion.Tests.model
  input (key empty) (normalized safety empty 4) false (cells safety empty 4) (taken safety empty 4).2.world (some growth)
def reached (safety empty clone : Bool) :=
  (insertWith (actions clone) safety empty (normalized safety empty 4) allocate false (taken safety empty 4).2.world).2
def closed (clone : Bool) := if clone then (Storage.Cleanup.sequence [.allocation, .arguments]).run transferredCreated
  else (Storage.Cleanup.sequence [.arguments]).run transferredArguments

theorem create_failure_result (safety empty : Bool) : (made safety empty false).1 = .error .outOfMemory := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem create_success_result (safety empty : Bool) : (made safety empty true).1 = .ok (object empty) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem clone_failure_result (safety empty : Bool) : (cloned safety empty).1 = .error .outOfMemory := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem failure_results (safety empty : Bool) :
    (made safety empty false).1 = .error .outOfMemory ∧
    (made safety empty true).1 = .ok (object empty) ∧
    (cloned safety empty).1 = .error .outOfMemory :=
  ⟨create_failure_result safety empty, create_success_result safety empty, clone_failure_result safety empty⟩

theorem completed (safety empty clone : Bool) (after : Frame Nat)
    (ran : executed safety empty clone = ((.ok (some .allocationFailure), closed clone), after)) :
    outcome safety empty clone = (.error (.language .outOfMemory),
      ⟨reached safety empty clone, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    (reached safety empty clone).memory = memory after ∧
    (reached safety empty clone).graph.representatives = some (cells safety empty 4) ∧
    (reached safety empty clone).graph.table = (before safety empty 4).graph.table := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have rows : (taken safety empty 4).2.world.graph.representatives.getD [] = cells safety empty 4 := by
    rw [entry.origin.graph]; rfl
  have selected : selectedGrowth (cells safety empty 4) = some growth := by simp only [selectedGrowth, prior.count, ↓reduceIte]
  have inserted : insertWith (actions clone) safety empty (normalized safety empty 4) allocate false (taken safety empty 4).2.world =
      (.error (.language .outOfMemory), reached safety empty clone) := by
    apply Prod.ext
    · simp only [insertWith, rows, selected]
      change (match (executed safety empty clone).1.1 with
        | .error _ => (Except.error (OwnedCall.Fault.language .safetyFault) : Except OwnedCall.Fault NodeId)
        | .ok result => (Interner.insertionOutcome (cells safety empty 4) result).mapError OwnedCall.Fault.language) = _
      rw [ran]
      rfl
    · rfl
  have finished := entry.handoff_insert (actions clone).arguments (fun slice => insertWith (actions clone) safety empty slice allocate false)
  simp only [inserted, ordinary, (prefix_results safety empty 4 (by decide)).2.2.2] at finished
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold outcome invokeWith
    rw [(prefix_results safety empty 4 (by decide)).1]
    have initialized : prepared safety empty 4 = (.ok (values empty), (prepared safety empty 4).2) :=
      Prod.ext (prefix_results safety empty 4 (by decide)).2.1 rfl
    have transferred : taken safety empty 4 = (.ok (), (taken safety empty 4).2) :=
      Prod.ext (prefix_results safety empty 4 (by decide)).2.2.1 rfl
    unfold prepared at initialized
    unfold taken at transferred
    simp only [Caller.invoke, Effect.bind]
    change finish (Publication.external (actions clone).arguments) 7 _ _ = _
    simp only [show (actions clone).arguments = ops.arguments from rfl]
    rw [initialized]
    change finish (Publication.external (actions clone).arguments) 7
      (Effect.bind (take (Publication.external (actions clone).arguments) 7)
        (fun _ => (do handoff; graph (fun slice => insertWith (actions clone) safety empty slice allocate false) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).1
      (Effect.bind (take (Publication.external (actions clone).arguments) 7)
        (fun _ => (do handoff; graph (fun slice => insertWith (actions clone) safety empty slice allocate false) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).2 = _
    simp only [Effect.bind]
    simp only [show (actions clone).arguments = ops.arguments from rfl]
    rw [transferred]
    exact finished
  · unfold reached insertWith
    simp only [rows, selected]
    change memory (executed safety empty clone).2 = _
    rw [ran]
  · unfold reached insertWith
    simp only [rows, selected]
    change (Insertion.projected _ _ _ (cell _ _ _ _ (executed safety empty clone).1.2 (executed safety empty clone).2)
      (executed safety empty clone).1.2 (executed safety empty clone).2).graph.representatives = _
    rw [ran]
    cases clone <;> rfl
  · unfold reached insertWith
    simp only [rows, selected]
    change (Insertion.projected _ _ _ (cell _ _ _ _ (executed safety empty clone).1.2 (executed safety empty clone).2)
      (executed safety empty clone).1.2 (executed safety empty clone).2).graph.table = _
    rw [ran]
    cases clone <;> change (taken safety empty 4).2.world.graph.table = _
    all_goals rw [entry.origin.graph]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredPreparationFailureTests
