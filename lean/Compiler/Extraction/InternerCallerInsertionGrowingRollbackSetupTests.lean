/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowingSuccessTests
import Compiler.Extraction.InternerCallerInsertionGrowingRollback

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RollbackTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- The earlier five published rows are unchanged. Only the sixth publication
probe fails; allocation, cloning, relocation and every defer use the same calls. -/
def failing : Operations Nat := { ops with probe := fun _ state => (false, state.effects * 10 + 8) }
def outcome (safety empty : Bool) := invokeWith failing safety empty (before safety empty 4)
def world (safety empty : Bool) := (outcome safety empty).2.world
def executed (safety empty : Bool) := execution failing allocate safety 7 6 (parent empty) source Insertion.Tests.model
  input (key empty) (normalized safety empty 4) true (cells safety empty 4) (taken safety empty 4).2.world (some growth)
def reached (safety empty : Bool) :=
  (insertWith failing safety empty (normalized safety empty 4) allocate true (taken safety empty 4).2.world).2
def closed := (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership

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
  have inserted : insertWith failing safety empty (normalized safety empty 4) allocate true (taken safety empty 4).2.world =
      (.error (.language .outOfMemory), reached safety empty) := by
    apply Prod.ext
    · simp only [insertWith, rows, selected]
      change (match (executed safety empty).1.1 with
        | .error _ => (Except.error (OwnedCall.Fault.language .safetyFault) : Except OwnedCall.Fault NodeId)
        | .ok result => (Interner.insertionOutcome (cells safety empty 4) result).mapError OwnedCall.Fault.language) = _
      rw [ran]
      rfl
    · rfl
  have finished := entry.handoff_insert ops.arguments (insertWith failing safety empty)
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
    simp only [show failing.arguments = ops.arguments from rfl]
    change finish (Publication.external ops.arguments) 7 _ _ = _
    rw [initialized]
    change finish (Publication.external ops.arguments) 7
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (insertWith failing safety empty) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).1
      (Effect.bind (take (Publication.external ops.arguments) 7)
        (fun _ => (do handoff; graph (insertWith failing safety empty) : Action (Publication.Effects Nat) NodeId)) (prepared safety empty 4).2).2 = _
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

def ownerObservation (safety empty : Bool) :=
  ((world safety empty).memory.memory.heap.lookup 6).map (fun allocation => (allocation.type, allocation.writable))

/-- Check the written owner geometry on the actual failed invocation. The
general rollback theorem below supplies the graph, keys and pointee frames. -/
theorem owner_observed (safety empty : Bool) : ownerObservation safety empty = some (Owner.viewType safety, true) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

theorem owner (safety empty : Bool) : ∃ native, (world safety empty).memory.memory.heap.lookup 6 = some native ∧
    native.type = Owner.viewType safety ∧ native.writable = true := by
  have observed := owner_observed safety empty
  unfold ownerObservation at observed
  cases found : (world safety empty).memory.memory.heap.lookup 6 with
  | none => simp only [found, Option.map_none] at observed; contradiction
  | some native =>
    simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    exact ⟨native, rfl, observed⟩

def dead (safety empty : Bool) (id : Nat) :=
  ((world safety empty).memory.heap id).isNone && ((world safety empty).memory.memory.heap.lookup id).isNone
def cleanupObservation (safety empty : Bool) :=
  (dead safety empty (object safety empty 4), dead safety empty (object safety empty 4 + 1),
   if empty then true else dead safety empty (operands safety empty 4).address && dead safety empty (normalized safety empty 4).address,
   (world safety empty).memory.effects.allocator)
def expectedEffects (safety empty : Bool) :=
  (((((ready safety empty 4).effects.allocator * 10 + 7) * 10 + 9) * 10 + 8) * 10 + 2) * 10 + 3 + (if empty then 0 else 202)

/-- Both nonempty argument owners are freed once. Empty sentinels cause no
argument free; the new item and cloned payload still die. Allocator effects
retain growth, old-backing release, failed probe and the source-order cleanup. -/
theorem cleanup_observed (safety empty : Bool) : cleanupObservation safety empty = (true, true, true, expectedEffects safety empty) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RollbackTests
