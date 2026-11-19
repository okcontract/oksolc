/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTransferredPreparationFailureSetupTests
import Compiler.Extraction.InternerNativeGrowingInsertionTests
import Compiler.Extraction.InternerEnclosingInsertionFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredPreparationFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- Actual failing observations instantiate the two generic caller theorems.
Ownership and memory frames come from those theorems, not fixture reduction. -/
theorem native_contract (safety empty clone : Bool) : ∃ after,
    executed safety empty clone = ((.ok (some .allocationFailure), closed clone), after) ∧
    CallerPreparationFailure 7 (normalized safety empty 4) (before safety empty 4) (failed safety empty clone) after ∧
    (clone = true → (memory after).heap (object empty) = none ∧ (memory after).memory.heap.lookup (object empty) = none) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observed := failure_results safety empty
  cases clone
  · obtain ⟨after, ran, post, _⟩ := entry.transferred_create_oom (actions false) allocate safety 7 6 (parent empty) source
      Insertion.Tests.model (request empty) (values empty) input (key empty) (normalized safety empty 4) (lookup empty)
      (before safety empty 4) (taken safety empty 4).2 (cells safety empty 4) (some growth)
      (made safety empty false).2 (by rw [prior.count]; decide) (Prod.ext observed.1 rfl)
    exact ⟨after, ran, post, by intro impossible; cases impossible⟩
  · obtain ⟨destroyed, after, ran, post, _, _, _, dead⟩ := entry.transferred_clone_oom (actions true) allocate safety 7 6 (parent empty) source
      Insertion.Tests.model (request empty) (values empty) input (key empty) (normalized safety empty 4) (lookup empty)
      (before safety empty 4) (taken safety empty 4).2 (cells safety empty 4) (some growth)
      (object empty) (made safety empty true).2 (cloned safety empty).2 (by rw [prior.count]; decide)
      (Prod.ext observed.2.1 rfl) (Prod.ext observed.2.2 rfl)
    exact ⟨after, ran, post, fun _ => dead⟩

/-- The same observed allocation failures drive the general insertion-frame
reducer. No final native frame or parent-preservation law is supplied. -/
theorem shared_completion (safety empty clone : Bool) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert (actions clone) allocate safety 7 6
      (parent empty) source Insertion.Tests.model input (key empty) slice false (some growth)) : Action (Publication.Effects Nat) NodeId)
      ⟨(taken safety empty 4).2.world, ⟨some (lookup empty), some (normalized safety empty 4), false⟩⟩
    ConstructorItem.NativeRecursion.FramePost
      (ConstructorItem.NativeRecursion.GraphFrame safety 7 6 (cells safety empty 4) (fun _ => True))
      (OwnedCall.finish (Publication.external (actions clone).arguments) 7 ran.1 ran.2) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observed := failure_results safety empty
  have failed : PreparationOOMAt (actions clone) 7 input (normalized safety empty 4) false (taken safety empty 4).2.world.memory := by
    cases clone with
    | false => exact .create (made safety empty false).2 (Prod.ext observed.1 rfl)
    | true =>
      exact .clone (object empty) (made safety empty true).2 (cloned safety empty).2
        (Prod.ext observed.2.1 rfl) (Prod.ext observed.2.2 rfl)
  let stack : ConstructorItem.NativeRecursion.Enclosing (σ := Nat) safety 7 6 (fun _ => True) := .root
  exact stack.insertion_frame trivial entry.origin (NativeGrowingTests.reached_frame safety empty)
    (actions clone) allocate (some growth) Insertion.Tests.model (key empty) false
    (Normalization.Tests.external_admitted _) (fun _ absent _ => False.elim (absent failed))

theorem derived_contract (safety empty clone : Bool) :
    outcome safety empty clone = (.error (.language .outOfMemory),
      ⟨world safety empty clone, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    GraphFacts safety (lifetime empty) 5 (world safety empty clone) (cells safety empty 4) ∧
    Consumed (normalized safety empty 4) (world safety empty clone).memory ∧
    (world safety empty clone).memory.effects.keys = (before safety empty 4).memory.effects.keys ∧
    (world safety empty clone).memory.memory.nextId = (failed safety empty clone).memory.nextId ∧
    (world safety empty clone).memory.memory.nextAddress = (failed safety empty clone).memory.nextAddress ∧
    (∀ id native, (before safety empty 4).memory.memory.heap.lookup id = some native →
      (world safety empty clone).memory.memory.heap.lookup id = some native) ∧
    (clone = true → (world safety empty clone).memory.heap (object empty) = none ∧
      (world safety empty clone).memory.memory.heap.lookup (object empty) = none) := by
  obtain ⟨after, ran, post, dead⟩ := native_contract safety empty clone
  have complete := completed safety empty clone after ran
  have same : world safety empty clone = reached safety empty clone := congrArg (fun result => result.2.world) complete.1
  have memorySame : (world safety empty clone).memory = memory after := by rw [same]; exact complete.2.1
  have prior := initialized_prefix safety empty 4 (by decide)
  refine ⟨?_, ?_, memorySame ▸ post.consumed, memorySame ▸ post.keys,
    memorySame ▸ post.nextId, memorySame ▸ post.nextAddress, ?_, ?_⟩
  · simpa only [← same] using complete.1
  · exact prior.facts.frame (by rw [prior.count]; decide) (memorySame ▸ post.valid)
      (by rw [same]; exact complete.2.2.1) (by rw [same]; exact complete.2.2.2) (memorySame ▸ post.keys)
      (fun id native found => memorySame ▸ post.native id native found)
      (fun id block stored => memorySame ▸ post.registry id block stored)
  · intro id native found
    rw [memorySame]
    exact post.native id native found
  · intro isClone
    rw [memorySame]
    exact dead isClone

theorem parent_borrow_after_oom (safety empty clone : Bool) :
    Operation.run (world safety empty clone).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (CallerInputTests.operands empty)))) ∧
    Good (parent empty) (request empty).arguments (world safety empty clone) :=
  (derived_contract safety empty clone).2.1.first_borrow (initialized_prefix safety empty 4 (by decide)).first

theorem key_unchanged (safety empty clone : Bool) :
    (world safety empty clone).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
  have previous : (before safety empty 4).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (congrFun (derived_contract safety empty clone).2.2.2.1 (key empty)).trans previous

def expectedEffects (safety empty clone : Bool) :=
  (if clone then (failed safety empty clone).effects.allocator * 10 + 3 else (failed safety empty clone).effects.allocator) +
    (if empty then 0 else 101)

/-- The exact reached effects exclude payload deinit, append, publication and
a second argument free. Empty sentinels cause no argument-free effect. -/
theorem effects_observed (safety empty clone : Bool) :
    (world safety empty clone).memory.effects.allocator = expectedEffects safety empty clone := by
  cases safety <;> cases empty <;> cases clone <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredPreparationFailureTests
