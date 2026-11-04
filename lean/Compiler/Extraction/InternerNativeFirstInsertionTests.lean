/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeStep
import Compiler.Extraction.InternerCallerInsertionFirstSuccessTests
import Compiler.Extraction.RepresentativeFirstRegistryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeFirstTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (world raw sentinel argumentView values request key taken remaining duplicated made cloned ready object operands copied owner)
open ConstructorItem.NativeRecursion

/-- Reuse the actual initialized caller, whose sentinel has offset nineteen. -/
theorem initial_facts (safety : Bool) :
    NativeGraph.Facts safety 7 6 sentinel 0 (world safety) [] := by
  obtain ⟨after, ran, facts, _⟩ := NativeGraph.initialized safety 7 6 (raw safety)
    (AssemblyClone.NativeFields.QueryTests.ownerCell safety true) sentinel Insertion.Tests.model
    (AssemblyClone.NativeFields.QueryTests.initial_valid safety true) (by cases safety <;> rfl) rfl rfl rfl
  have same := (Prod.mk.inj (Except.ok.inj (ran.symm.trans (CallerInputTests.initializer safety)))).2
  exact same ▸ facts

theorem reached_frame (safety empty : Bool) :
    CallFrame safety 7 6 [] (argumentView empty) (request empty).arguments
      (CallerInputTests.normalized empty) source input (fun _ => True) (taken safety empty).2.world := by
  have entry := CallerInputTests.derived_input safety empty
  have array : ArraySource (argumentView empty) (world safety).memory.memory := by
    cases empty with
    | true => exact ArraySource.empty rfl
    | false =>
      exact ArraySource.registered (initial_facts safety).valid
        (allocator := 7) (slice := ⟨0, [0]⟩) (Or.inr (by cases safety <;> insertion_kernel_rfl))
  exact CallFrame.caller entry (initial_facts safety) (by
    intro key old impossible
    rw [CallerFirstSuccessTests.initial_key_table safety] at impossible
    cases impossible) array (fun _ => True) trivial

theorem published_observed (safety empty : Bool) :
    FirstPublished CallerFirstSuccessTests.ops CallerInputTests.allocate safety 7 6 Insertion.Tests.model input
      (key empty) (CallerInputTests.normalized empty) (taken safety empty).2.world := by
  have entry := CallerInputTests.derived_input safety empty
  have observed := CallerInputTests.preparation safety empty
  have original := CallerInputTests.initialized_owner safety
  have nativeFrame := entry.native_frame 6 (owner safety) original.1
  refine ⟨by decide, ?_, operands empty, CallerInputTests.handle empty, (duplicated safety empty).2,
    object empty, (made safety empty).2, copied empty, (cloned safety empty).2, 4096,
    (ready safety empty).effects.allocator * 10 + 7, CallerInputTests.probeEffects safety empty,
    observed.1, observed.2.1, observed.2.2.1, ?_, ?_, ?_⟩
  · exact (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) capacityOffset nativeFrame).trans original.2.2.2.2
  · intro installed assigned
    have same := Except.ok.inj (assigned.symm.trans observed.2.2.2)
    rw [same]
    exact CallerInputTests.backing_response safety empty
  · intro installed assigned
    have same := Except.ok.inj (assigned.symm.trans observed.2.2.2)
    rw [same]
    exact CallerFirstSuccessTests.probe_result safety empty
  · exact (Owner.NativeLock.checkHeader_eq_of_lookup safety (world safety).memory.memory
      (taken safety empty).2.world.memory.memory 6 (owner safety) entry.origin.held.1.1.memory
      original.1 original.2.1 nativeFrame).trans (CallerInputTests.initialized_lock safety)

def actual (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :=
  Insertion.Native.insert CallerFirstSuccessTests.ops CallerInputTests.allocate safety 7 6 (argumentView empty) source
    Insertion.Tests.model input (key empty) (CallerInputTests.normalized empty) true growth (taken safety empty).2.world

/-- The existing execution specializes the single publication completion used
by the general step, with arbitrary optional growth callbacks. -/
theorem completed (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    (actual safety empty growth).1 = .ok 0 ∧
      ∃ added data capacity, NativeGraph.Facts safety 7 6 data capacity (actual safety empty growth).2 added := by
  have entry := CallerInputTests.derived_input safety empty
  have checked := (reached_frame safety empty).published CallerFirstSuccessTests.ops CallerInputTests.allocate growth
    Insertion.Tests.model (key empty) (Normalization.Tests.external_admitted _) entry.publication.aligned
    (by rw [entry.origin.graph, (initial_facts safety).projected]; decide)
    (Or.inl (published_observed safety empty))
  simpa only [entry.origin.graph, (initial_facts safety).projected, Option.getD_some, List.nil_append] using checked

/-- The unsupported remap callback is unreachable at zero old capacity. -/
theorem unsupported_callback_skipped (safety empty : Bool) :
    (actual safety empty (some ⟨.unsupported, fun _ _ _ _ effects => effects + 999⟩)).1 = .ok 0 :=
  (completed safety empty _).1

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.NativeFirstTests

namespace Compiler.Extraction.RepresentativeArray.Append.Registered.FirstAdapterTests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Preserve the existing first-append fixture while varying only its empty
sentinel: absent, the owner itself, or the imminent fresh allocation, all with
a nonzero offset. None is an old allocation to remap or release. -/
def before (safety : Bool) (sentinel : Address) :=
  let original := DescriptorRelation.FirstRegistryTests.before safety true
  let owner := DescriptorRelation.FirstRegistryTests.owner safety true
  let changed := { owner with cells := owner.cells.set 16 (.pointer Publication.pointerType sentinel) }
  { original with memory := { original.memory with heap := original.memory.heap.replace 3 changed } }

def actual (safety : Bool) (sentinel : Address) :=
  runWithGrowth ⟨.unsupported, fun _ _ _ _ effects => effects ++ [(999, 999)]⟩ safety
    (DescriptorRelation.FirstRegistryTests.registeredRequest (some 800)) 7 3 [] DescriptorRelation.Tests.first (before safety sentinel)

theorem sentinel_aliases (safety : Bool) :
    ∀ sentinel ∈ ([⟨99, 64⟩, ⟨3, 19⟩, ⟨4, 13⟩] : List Address),
      (actual safety sentinel).2.memory = (run safety (DescriptorRelation.FirstRegistryTests.registeredRequest (some 800))
        7 3 [] DescriptorRelation.Tests.first (before safety sentinel)).2.memory ∧
      (actual safety sentinel).1 = .ok true ∧
      (actual safety sentinel).2.heap 4 = some ⟨7, .representatives [DescriptorRelation.Tests.first]⟩ ∧
      (actual safety sentinel).2.memory.nextId = 5 ∧
      (actual safety sentinel).2.effects = [(160, 8)] := by
  intro sentinel member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> cases safety <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> insertion_kernel_rfl

end Compiler.Extraction.RepresentativeArray.Append.Registered.FirstAdapterTests
