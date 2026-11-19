/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStep
import Compiler.Extraction.InternerCallerInsertionGrowingSuccessTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeGrowingTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values request key)
open CallerGrowingChainTests
open ConstructorItem.NativeRecursion

/-- Reuse the existing five-row prefix, including its original borrowed
arguments and every reached caller. No populated native graph is postulated. -/
theorem reached_frame (safety empty : Bool) :
    CallFrame safety 7 6 (cells safety empty 4) (parent empty) (request empty).arguments
      (CallerGrowingChainTests.normalized safety empty 4) source input (fun _ => True) (taken safety empty 4).2.world := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have array : ArraySource (parent empty) (before safety empty 4).memory.memory :=
    ArraySource.registered prior.facts.valid (prior.facts.resident _ (List.mem_of_head? prior.first)).2
  exact CallFrame.caller entry (prior.facts.native (by rw [prior.count]; decide)) prior.source_private array (fun _ => True) trivial

def probeEffects (safety empty : Bool) :=
  (memory (append safety CallerGrowingChainTests.allocate 7 6 (cells safety empty 4) input (key empty) (CallerGrowingChainTests.normalized safety empty 4)
    (value safety empty 4) preparationOwnership (preparedFrame (object safety empty 4) (copied safety empty 4)
      (operands safety empty 4) (ready safety empty 4)) (some growth)).2).effects.allocator * 10 + 8

theorem published_observed (safety empty : Bool) :
    RelocatedPublished ops CallerGrowingChainTests.allocate safety 7 6 Insertion.Tests.model input (key empty) (CallerGrowingChainTests.normalized safety empty 4)
      (some growth) (taken safety empty 4).2.world := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have observed := preparation_results safety empty 4 (by decide)
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  have nativeFrame := entry.native_frame 6 owner found
  have projected : (taken safety empty 4).2.world.graph.representatives.getD [] = cells safety empty 4 := by
    rw [entry.origin.graph, prior.facts.projected]
    rfl
  refine ⟨by decide, 5, 13, ?_, by decide, ?_, ?_, by decide, 17, 23, releaseBacking, rfl,
    operands safety empty 4, handle safety empty 4, (duplicated safety empty 4).2, object safety empty 4,
    (made safety empty 4).2, copied safety empty 4, (cloned safety empty 4).2, 8192,
    (ready safety empty 4).effects.allocator * 10 + 7, probeEffects safety empty,
    observed.1, observed.2.1, observed.2.2, ?_, ?_, ?_⟩
  · exact (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) capacityOffset nativeFrame).trans prior.facts.capacity_read
  · rw [projected, prior.count]
    decide
  · rw [projected, prior.count]
    decide
  · intro installed assigned
    have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
    rw [← same]
    exact ⟨rfl, backing_fits safety empty⟩
  · intro installed assigned
    have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
    rw [← same, projected]
    rfl
  · exact (Owner.NativeLock.checkHeader_eq_of_lookup safety (before safety empty 4).memory.memory
      (taken safety empty 4).2.world.memory.memory 6 owner entry.origin.held.1.1.memory found typed nativeFrame).trans
      (growth_entry_unlocked safety empty)

def actual (safety empty : Bool) :=
  Insertion.Native.insert ops CallerGrowingChainTests.allocate safety 7 6 (parent empty) source Insertion.Tests.model input
    (key empty) (CallerGrowingChainTests.normalized safety empty 4) true (some growth) (taken safety empty 4).2.world

/-- The actual sixth insertion instantiates the general completion used by the
proper-child step, for both runtime-safety modes and empty/nonempty arguments. -/
theorem completed (safety empty : Bool) :
    (actual safety empty).1 = .ok 5 ∧
      ∃ added data capacity, NativeGraph.Facts safety 7 6 data capacity (actual safety empty).2
        (cells safety empty 4 ++ added) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have checked := (reached_frame safety empty).published ops CallerGrowingChainTests.allocate (some growth) Insertion.Tests.model (key empty)
    (Normalization.Tests.external_admitted _) entry.publication.aligned
    (by rw [entry.origin.graph, prior.facts.projected]; simpa only [Option.getD_some, prior.count] using (show 5 < 2 ^ 32 - 1 by decide))
    (Or.inr (Or.inr (published_observed safety empty)))
  simpa only [entry.origin.graph, prior.facts.projected, Option.getD_some, Storage.idFor, prior.count] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeGrowingTests
