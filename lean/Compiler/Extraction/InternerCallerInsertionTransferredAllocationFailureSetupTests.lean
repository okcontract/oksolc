/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionTransferredGrowthSetupTests
import Compiler.Extraction.InternerCallerInsertionTransferredAllocationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredAllocationFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

abbrev object := TransferredGrowthTests.object
abbrev copied := TransferredGrowthTests.copied
abbrev made := TransferredGrowthTests.made
abbrev cloned := TransferredGrowthTests.cloned
abbrev ready := TransferredGrowthTests.ready

/-- The sixth insertion reaches the same full five-row initialized graph. The
backing allocator returns OOM after nondeterministic transfer. The single
argument owner is released; publication, old-backing free and outer normalized
release must not run. -/
def failing : Backing.Registry.Allocate Nat := fun _ _ _ effects => (none, effects * 10 + 7)
def outcome (safety empty : Bool) := invokeWith ops safety empty (before safety empty 4) failing false
def world (safety empty : Bool) := (outcome safety empty).2.world
def executed (safety empty : Bool) := execution ops failing safety 7 6 (parent empty) source Insertion.Tests.model
  input (key empty) (normalized safety empty 4) false (cells safety empty 4) (taken safety empty 4).2.world (some growth)
def reached (safety empty : Bool) :=
  (insertWith ops safety empty (normalized safety empty 4) failing false (taken safety empty 4).2.world).2
def closed := (Storage.Cleanup.sequence [.value, .allocation, .arguments]).run transferredPreparation

theorem completed (safety empty : Bool) (after : Frame Nat)
    (ran : executed safety empty = ((.ok (some .allocationFailure), closed), after)) :
    outcome safety empty = (.error (.language .outOfMemory),
      ⟨reached safety empty, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    (reached safety empty).memory = memory after ∧
    (reached safety empty).graph.representatives = some (cells safety empty 4) ∧
    (reached safety empty).graph.table = (before safety empty 4).graph.table := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have rows : (taken safety empty 4).2.world.graph.representatives.getD [] = cells safety empty 4 := by
    rw [entry.origin.graph]; rfl
  have selected : selectedGrowth (cells safety empty 4) = some growth := by simp only [selectedGrowth, prior.count, ↓reduceIte]
  have inserted : insertWith ops safety empty (normalized safety empty 4) failing false (taken safety empty 4).2.world =
      (.error (.language .outOfMemory), reached safety empty) := by
    apply Prod.ext
    · simp only [insertWith, rows, selected]
      change (match (executed safety empty).1.1 with
        | .error _ => (Except.error (OwnedCall.Fault.language .safetyFault) : Except OwnedCall.Fault NodeId)
        | .ok result => (Interner.insertionOutcome (cells safety empty 4) result).mapError OwnedCall.Fault.language) = _
      rw [ran]
      rfl
    · rfl
  have finished := entry.handoff_insert ops.arguments (fun slice => insertWith ops safety empty slice failing false)
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
    change finish (Publication.external ops.arguments) 7 _ _ = _
    rw [initialized]
    change finish (Publication.external ops.arguments) 7
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (fun slice => insertWith ops safety empty slice failing false) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).1
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (fun slice => insertWith ops safety empty slice failing false) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).2 = _
    simp only [Effect.bind]
    rw [transferred]
    exact finished
  · unfold reached insertWith
    simp only [rows, selected]
    change memory (executed safety empty).2 = _
    rw [ran]
  · unfold reached insertWith
    simp only [rows, selected]
    change (Insertion.projected _ _ _ (cell _ _ _ _ (executed safety empty).1.2 (executed safety empty).2)
      (executed safety empty).1.2 (executed safety empty).2).graph.representatives = _
    rw [ran]
    rfl
  · unfold reached insertWith
    simp only [rows, selected]
    change (Insertion.projected _ _ _ (cell _ _ _ _ (executed safety empty).1.2 (executed safety empty).2)
      (executed safety empty).1.2 (executed safety empty).2).graph.table = _
    rw [ran]
    change (taken safety empty 4).2.world.graph.table = _
    rw [entry.origin.graph]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredAllocationFailureTests
