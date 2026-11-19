/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowthAllocationFailureSetupTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.AllocationFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)

/-- The generic caller theorem supplies preservation and cleanup from the same
execution. Final graph/native query facts do not come from fixture evaluation. -/
theorem derived_contract (safety empty : Bool) :
    outcome safety empty = (.error (.language .outOfMemory),
      ⟨world safety empty, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    GraphFacts safety (lifetime empty) 5 (world safety empty) (cells safety empty 4) ∧
    (world safety empty).memory.effects.keys = (before safety empty 4).memory.effects.keys ∧
    (world safety empty).memory.memory.nextId = (cloned safety empty 4).2.memory.nextId ∧
    (world safety empty).memory.memory.nextAddress = (cloned safety empty 4).2.memory.nextAddress ∧
    (∀ id native, (before safety empty 4).memory.memory.heap.lookup id = some native →
      (world safety empty).memory.memory.heap.lookup id = some native) ∧
    (∀ id, id = object safety empty 4 ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload (copied safety empty 4)) id ∨
      ((operands safety empty 4).items ≠ [] ∧ id = (operands safety empty 4).address) ∨
      ((normalized safety empty 4).items ≠ [] ∧ id = (normalized safety empty 4).address) →
      (world safety empty).memory.heap id = none ∧ (world safety empty).memory.memory.heap.lookup id = none) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observations := preparation_results safety empty 4 (by decide)
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  obtain ⟨after, ran, valid, nextId, nextAddress, table, live, unique, _, _, _, frame, registry, destroyed⟩ :=
    entry.growing_allocation_oom ops failing releaseBacking safety 7 6 (lifetime empty) 5 13 (object safety empty 4) 17 23 owner
      (parent empty) source Insertion.Tests.model (request empty) (values empty) input (copied safety empty 4) (key empty)
      (normalized safety empty 4) (operands safety empty 4) (lookup empty) (handle safety empty 4) (before safety empty 4) (taken safety empty 4).2
      (cells safety empty 4) (duplicated safety empty 4).2 (made safety empty 4).2 (cloned safety empty 4).2
      (Normalization.Tests.external_admitted _) prior.facts.valid found typed prior.facts.owned (readHeader_items _ _ _ _ prior.facts.header)
      prior.facts.capacity_read prior.facts.live (by decide) (by rw [prior.count]; decide) (by rw [prior.count]; decide)
      (by decide) (by rw [prior.count]; decide) observations.1 observations.2.1 observations.2.2
      ((ready safety empty 4).effects.allocator * 10 + 7) (by
        intro installed assigned
        have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
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
  (((ready safety empty 4).effects.allocator * 10 + 7) * 10 + 2) * 10 + 3 + (if empty then 0 else 202)

/-- Exact reached effects include failed backing allocation and local cleanup;
neither the old-backing free nor map probe is executed. -/
theorem effects_observed (safety empty : Bool) :
    (world safety empty).memory.effects.allocator = expectedEffects safety empty := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.AllocationFailureTests
