/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionTransferredAllocationFailureSetupTests
import Compiler.Extraction.InternerNativeGrowingInsertionTests
import Compiler.Extraction.InternerEnclosingInsertionFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredAllocationFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- The existing initialized transfer execution supplies the selected source
observations used by the general step, without a final storage/frame premise. -/
theorem backing_observed (safety empty : Bool) :
    BackingAllocationOOMAt ops failing 7 6 input (normalized safety empty 4) false (some growth)
      (taken safety empty 4).2.world := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observed := TransferredGrowthTests.preparation_results safety empty
  obtain ⟨owner, found, typed, _⟩ := prior.facts.owner
  have nativeFrame := entry.native_frame 6 owner found
  have projected : (taken safety empty 4).2.world.graph.representatives.getD [] = cells safety empty 4 := by
    rw [entry.origin.graph, prior.facts.projected]
    rfl
  refine ⟨normalized safety empty 4, lookup empty, (taken safety empty 4).2.world.memory, object empty,
    (made safety empty).2, copied empty, (cloned safety empty).2, (ready safety empty).effects.allocator * 10 + 7,
    ⟨rfl, rfl⟩, Prod.ext observed.1 rfl, Prod.ext observed.2 rfl, ?_, Or.inr ?_⟩
  · exact (Owner.NativeLock.checkHeader_eq_of_lookup safety (before safety empty 4).memory.memory
      (taken safety empty 4).2.world.memory.memory 6 owner entry.origin.held.1.1.memory found typed nativeFrame).trans
      (growth_entry_unlocked safety empty)
  · refine ⟨5, 13, 17, 23, releaseBacking, ?_, by decide, ?_, ?_, by decide, rfl, ?_⟩
    · exact (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) capacityOffset nativeFrame).trans prior.facts.capacity_read
    · rw [projected, prior.count]; decide
    · rw [projected, prior.count]; decide
    · intro installed assigned
      have same : ready safety empty = installed := by
        simp only [ready, TransferredGrowthTests.ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      rfl

theorem shared_completion (safety empty : Bool) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops failing safety 7 6
      (parent empty) source Insertion.Tests.model input (key empty) slice false (some growth)) : Action (Publication.Effects Nat) NodeId)
      ⟨(taken safety empty 4).2.world, ⟨some (lookup empty), some (normalized safety empty 4), false⟩⟩
    ConstructorItem.NativeRecursion.FramePost
      (ConstructorItem.NativeRecursion.GraphFrame safety 7 6 (cells safety empty 4) (fun _ => True))
      (OwnedCall.finish (Publication.external ops.arguments) 7 ran.1 ran.2) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  let stack : ConstructorItem.NativeRecursion.Enclosing (σ := Nat) safety 7 6 (fun _ => True) := .root
  exact stack.insertion_frame trivial entry.origin (NativeGrowingTests.reached_frame safety empty)
    ops failing (some growth) Insertion.Tests.model (key empty) false (Normalization.Tests.external_admitted _)
    (fun _ _ absent => False.elim (absent (backing_observed safety empty)))

/-- The generic caller theorem supplies preservation and cleanup from the same
execution. Final graph/native query facts do not come from fixture evaluation. -/
theorem derived_contract (safety empty : Bool) :
    outcome safety empty = (.error (.language .outOfMemory),
      ⟨world safety empty, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    GraphFacts safety (lifetime empty) 5 (world safety empty) (cells safety empty 4) ∧
    (world safety empty).memory.effects.keys = (before safety empty 4).memory.effects.keys ∧
    (world safety empty).memory.memory.nextId = (cloned safety empty).2.memory.nextId ∧
    (world safety empty).memory.memory.nextAddress = (cloned safety empty).2.memory.nextAddress ∧
    (∀ id native, (before safety empty 4).memory.memory.heap.lookup id = some native →
      (world safety empty).memory.memory.heap.lookup id = some native) ∧
    (∀ id, id = object empty ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload (copied empty)) id ∨
      ((normalized safety empty 4).items ≠ [] ∧ id = (normalized safety empty 4).address) →
      (world safety empty).memory.heap id = none ∧ (world safety empty).memory.memory.heap.lookup id = none) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observations := TransferredGrowthTests.preparation_results safety empty
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  obtain ⟨after, ran, valid, nextId, nextAddress, table, live, unique, _, _, _, frame, registry, destroyed⟩ :=
    entry.transferred_growing_allocation_oom ops failing releaseBacking safety 7 6 (lifetime empty) 5 13 (object empty) 17 23 owner
      (parent empty) source Insertion.Tests.model (request empty) (values empty) input (copied empty) (key empty)
      (normalized safety empty 4) (lookup empty) (before safety empty 4) (taken safety empty 4).2
      (cells safety empty 4) (made safety empty).2 (cloned safety empty).2
      prior.facts.valid found typed prior.facts.owned (readHeader_items _ _ _ _ prior.facts.header)
      prior.facts.capacity_read prior.facts.live (by decide) (by rw [prior.count]; decide) (by rw [prior.count]; decide)
      (by decide) (by rw [prior.count]; decide) (Prod.ext observations.1 rfl) (Prod.ext observations.2 rfl)
      ((ready safety empty).effects.allocator * 10 + 7) (by
        intro installed assigned
        have same : ready safety empty = installed := by simp only [ready, TransferredGrowthTests.ready, assigned, Except.toOption, Option.getD_some]
        rw [← same]
        rfl) (growth_entry_unlocked safety empty)
  have complete := completed safety empty after ran
  have same : world safety empty = reached safety empty := congrArg (fun result => result.2.world) complete.1
  have memorySame : (world safety empty).memory = memory after := by rw [same]; exact complete.2.1
  refine ⟨?_, ?_, memorySame ▸ table, memorySame ▸ nextId, memorySame ▸ nextAddress,
    (fun id native found => memorySame ▸ frame id native found), ?_⟩
  · simpa only [← same] using complete.1
  · exact prior.facts.frame (by rw [prior.count]; decide) (memorySame ▸ valid)
      (by rw [same]; exact complete.2.2.1) (by rw [same]; exact complete.2.2.2) (memorySame ▸ table)
      (fun id native found => memorySame ▸ frame id native found)
      (fun id block stored => memorySame ▸ registry id block stored)
  · intro id selected
    rw [memorySame]
    exact destroyed id selected

theorem parent_borrow_after_oom (safety empty : Bool) :
    Operation.run (world safety empty).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 254 =
      .ok (.ok (some (Operation.returned (CallerInputTests.operands empty)))) ∧
    Good (parent empty) (request empty).arguments (world safety empty) :=
  (derived_contract safety empty).2.1.first_borrow (initialized_prefix safety empty 4 (by decide)).first

theorem key_unchanged (safety empty : Bool) :
    (world safety empty).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
  have previous : (before safety empty 4).memory.effects.keys (key empty) = some ⟨if empty then 22 else 30, 4⟩ := by
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (congrFun (derived_contract safety empty).2.2.1 (key empty)).trans previous

def expectedEffects (safety empty : Bool) :=
  (((ready safety empty).effects.allocator * 10 + 7) * 10 + 2) * 10 + 3 + (if empty then 0 else 101)

/-- Exact reached effects include failed backing allocation and local cleanup;
neither the old-backing free, map probe, nor a second normalized free is executed. -/
theorem effects_observed (safety empty : Bool) :
    (world safety empty).memory.effects.allocator = expectedEffects safety empty := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.TransferredAllocationFailureTests
