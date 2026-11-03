/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGrowingInsertionTests
import Compiler.Extraction.InternerNativePublicationRollback
import Compiler.Extraction.InternerCallerInsertionGrowingRollbackTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeRollbackTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (request key)
open CallerGrowingChainTests ConstructorItem.NativeRecursion

/-- Reuse the existing initialized prefix and preparation/backing observations.
The existing rollback fixture changes only the publication probe's result. -/
theorem refused_observed (safety empty : Bool) :
    RelocatedPublication RollbackTests.failing CallerGrowingChainTests.allocate safety 7 6 Insertion.Tests.model input (key empty)
      (CallerGrowingChainTests.normalized safety empty 4) (some growth) false (taken safety empty 4).2.world := by
  obtain ⟨_, oldCapacity, capacity, capacityRead, nonempty, full, selected, size,
    context, returnAddress, release, growthIdentity, operands, remaining, duplicated, object, allocated,
    copied, middle, base, effects, probeEffects, duplicateCall, createCall, cloneCall, backing, response, unlocked⟩ :=
    NativeGrowingTests.published_observed safety empty
  refine ⟨oldCapacity, capacity, capacityRead, nonempty, full, selected, size,
    context, returnAddress, release, growthIdentity, operands, remaining, duplicated, object, allocated,
    copied, middle, base, effects, probeEffects, duplicateCall, createCall, cloneCall, backing, ?_, unlocked⟩
  intro installed assigned
  have effectsEqual := congrArg Prod.snd (response installed assigned)
  change (false, _) = (false, probeEffects)
  exact Prod.ext rfl effectsEqual

def actual (safety empty : Bool) :=
  Insertion.Native.insert RollbackTests.failing CallerGrowingChainTests.allocate safety 7 6 (parent empty) source
    Insertion.Tests.model input (key empty) (CallerGrowingChainTests.normalized safety empty 4)
    true (some growth) (taken safety empty 4).2.world

/-- Both safety modes and both operand sizes instantiate the general completion.
This uses the reached native frame, not the legacy fixture's final graph facts. -/
theorem completed (safety empty : Bool) :
    (actual safety empty).1 = .error (.language .outOfMemory) ∧
      (∃ added data capacity, NativeGraph.Facts safety 7 6 data capacity (actual safety empty).2
        (cells safety empty 4 ++ added)) ∧
      (actual safety empty).2.graph = (taken safety empty 4).2.world.graph ∧
      Consumed (CallerGrowingChainTests.normalized safety empty 4) (actual safety empty).2.memory := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have reads : (taken safety empty 4).2.world.graph.read =
      Storage.readValue ((taken safety empty 4).2.world.graph.representatives.getD []) := by
    rw [entry.origin.graph]
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (NativeGrowingTests.reached_frame safety empty).publication_rollback RollbackTests.failing CallerGrowingChainTests.allocate
    (some growth) Insertion.Tests.model (key empty) reads (Normalization.Tests.external_admitted _) entry.publication.aligned
    (by rw [entry.origin.graph, prior.facts.projected]; simpa only [Option.getD_some, prior.count] using (show 5 < 2 ^ 32 - 1 by decide))
    (Or.inr (Or.inr (refused_observed safety empty)))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeRollbackTests
