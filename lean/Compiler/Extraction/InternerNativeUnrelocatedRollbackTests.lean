/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFirstInsertionTests
import Compiler.Extraction.InternerNativeSpareInsertionTests
import Compiler.Extraction.InternerNativePublicationRollback

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.UnrelocatedRollbackTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (request key)
open ConstructorItem.NativeRecursion

/-- Reuse the successful fixtures' effects and preparation; change only the
actual publication decision. -/
def refuse (ops : Operations Nat) : Operations Nat :=
  { ops with probe := fun key state => (false, (ops.probe key state).2) }

namespace First
open CallerInputTests (taken argumentView)

theorem observed (safety empty : Bool) :
    FirstPublication (refuse CallerFirstSuccessTests.ops) CallerInputTests.allocate safety 7 6 Insertion.Tests.model input
      (key empty) (CallerInputTests.normalized empty) false (taken safety empty).2.world := by
  obtain ⟨_, capacityRead, operands, remaining, duplicated, object, allocated, copied, middle,
    base, allocationEffects, probeEffects, duplicateCall, createCall, cloneCall, backing, response, unlocked⟩ :=
    NativeFirstTests.published_observed safety empty
  refine ⟨capacityRead, operands, remaining, duplicated, object, allocated, copied, middle,
    base, allocationEffects, probeEffects, duplicateCall, createCall, cloneCall, backing, ?_, unlocked⟩
  intro installed assigned
  have effectsEqual := congrArg Prod.snd (response installed assigned)
  change (false, _) = (false, probeEffects)
  exact Prod.ext rfl effectsEqual

def actual (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :=
  Insertion.Native.insert (refuse CallerFirstSuccessTests.ops) CallerInputTests.allocate safety 7 6 (argumentView empty) source
    Insertion.Tests.model input (key empty) (CallerInputTests.normalized empty) true growth (taken safety empty).2.world

/-- Both safety and operand modes use the single completion consumed by the
general step. Arbitrary growth callbacks remain unobserved on this path. -/
theorem completed (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    (actual safety empty growth).1 = .error (.language .outOfMemory) ∧
      (∃ added data capacity, NativeGraph.Facts safety 7 6 data capacity (actual safety empty growth).2 added) ∧
      (actual safety empty growth).2.graph = (taken safety empty).2.world.graph ∧
      Consumed (CallerInputTests.normalized empty) (actual safety empty growth).2.memory := by
  have entry := CallerInputTests.derived_input safety empty
  have reads : (taken safety empty).2.world.graph.read =
      Storage.readValue ((taken safety empty).2.world.graph.representatives.getD []) := by
    rw [entry.origin.graph]
    cases safety <;> cases empty <;> insertion_kernel_rfl
  have checked := (NativeFirstTests.reached_frame safety empty).publication_rollback
    (refuse CallerFirstSuccessTests.ops) CallerInputTests.allocate growth Insertion.Tests.model (key empty)
    reads (Normalization.Tests.external_admitted _) entry.publication.aligned
    (by rw [entry.origin.graph, (NativeFirstTests.initial_facts safety).projected]; decide)
    (Or.inl (observed safety empty))
  simpa only [List.nil_append] using checked

end First

namespace Spare
open CallerSpareSuccessTests (taken argumentView itemSource old)

theorem observed (safety empty : Bool) :
    SparePublication (refuse CallerSpareSuccessTests.ops) CallerSpareSuccessTests.allocate safety 7 6 Insertion.Tests.model input
      (key empty) (CallerSpareSuccessTests.normalized empty) false (taken safety empty).2.world := by
  obtain ⟨_, capacity, capacityRead, spare, operands, remaining, duplicated, object, allocated, copied, middle,
    probeEffects, duplicateCall, createCall, cloneCall, response⟩ := NativeSpareTests.published_observed safety empty
  refine ⟨capacity, capacityRead, spare, operands, remaining, duplicated, object, allocated, copied, middle,
    probeEffects, duplicateCall, createCall, cloneCall, ?_⟩
  intro installed assigned
  have effectsEqual := congrArg Prod.snd (response installed assigned)
  change (false, _) = (false, probeEffects)
  exact Prod.ext rfl effectsEqual

def actual (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :=
  Insertion.Native.insert (refuse CallerSpareSuccessTests.ops) CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource
    Insertion.Tests.model input (key empty) (CallerSpareSuccessTests.normalized empty) true growth (taken safety empty).2.world

/-- The initialized row and key survive refusal. The fixture's backing
allocator refuses allocations, exercising the spare-capacity selection. -/
theorem completed (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    (actual safety empty growth).1 = .error (.language .outOfMemory) ∧
      (∃ added data capacity, NativeGraph.Facts safety 7 6 data capacity (actual safety empty growth).2 ([old safety empty] ++ added)) ∧
      (actual safety empty growth).2.graph = (taken safety empty).2.world.graph ∧
      Consumed (CallerSpareSuccessTests.normalized empty) (actual safety empty growth).2.memory := by
  have entry := CallerSpareSuccessTests.derived_input safety empty
  have reads : (taken safety empty).2.world.graph.read =
      Storage.readValue ((taken safety empty).2.world.graph.representatives.getD []) := by
    rw [entry.origin.graph]
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (NativeSpareTests.reached_frame safety empty).publication_rollback
    (refuse CallerSpareSuccessTests.ops) CallerSpareSuccessTests.allocate growth Insertion.Tests.model (key empty)
    reads (Normalization.Tests.external_admitted _) entry.publication.aligned
    (by rw [entry.origin.graph, (NativeSpareTests.initial_facts safety empty).projected]; simp)
    (Or.inr (Or.inl (observed safety empty)))

end Spare
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.UnrelocatedRollbackTests
