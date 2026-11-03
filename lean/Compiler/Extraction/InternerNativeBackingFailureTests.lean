/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFirstInsertionTests
import Compiler.Extraction.InternerNativeGrowingInsertionTests
import Compiler.Extraction.InternerCallerInsertionGrowthAllocationFailureTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.BackingFailureTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open ConstructorItem.NativeRecursion

abbrev failing := CallerGrowingChainTests.AllocationFailureTests.failing

/-- Reuse the first execution's preparation observations, changing only the
backing response. Its arbitrary optional growth callback is never invoked. -/
theorem first_observed (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    BackingAllocationOOM CallerFirstSuccessTests.ops failing 7 6 input (CallerInputTests.normalized empty)
      growth (CallerInputTests.taken safety empty).2.world := by
  obtain ⟨_, capacity, operands, remaining, duplicated, object, allocated, copied, middle, base,
    effects, probeEffects, duplicateCall, createCall, cloneCall, response, _, unlocked⟩ :=
    NativeFirstTests.published_observed safety empty
  refine ⟨operands, remaining, duplicated, object, allocated, copied, middle, effects,
    duplicateCall, createCall, cloneCall, unlocked, Or.inl ⟨capacity, ?_⟩⟩
  intro installed assigned
  have effectsEqual : installed.effects.allocator * 10 + 7 = effects :=
    congrArg Prod.snd (response installed assigned).1
  change (none, installed.effects.allocator * 10 + 7) = (none, effects)
  rw [effectsEqual]

def first (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :=
  Insertion.Native.insert CallerFirstSuccessTests.ops failing safety 7 6 (CallerInputTests.argumentView empty) source
    Insertion.Tests.model input (CallerInputTests.key empty) (CallerInputTests.normalized empty) true growth
    (CallerInputTests.taken safety empty).2.world

theorem first_completed (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat)) :
    (first safety empty growth).1 = .error (.language .outOfMemory) ∧
      GraphFrame safety 7 6 [] (fun _ => True) (first safety empty growth).2 ∧
      Consumed (CallerInputTests.normalized empty) (first safety empty growth).2.memory := by
  have entry := CallerInputTests.derived_input safety empty
  have reads : (CallerInputTests.taken safety empty).2.world.graph.read =
      Storage.readValue ((CallerInputTests.taken safety empty).2.world.graph.representatives.getD []) := by
    rw [entry.origin.graph]
    cases safety <;> insertion_kernel_rfl
  exact (NativeFirstTests.reached_frame safety empty).backing_oom CallerFirstSuccessTests.ops failing growth
    Insertion.Tests.model (CallerInputTests.key empty) reads
    (by rw [entry.origin.graph, (NativeFirstTests.initial_facts safety).projected]; decide)
    (Normalization.Tests.external_admitted _) (first_observed safety empty growth) (fun _ _ _ => trivial)

theorem first_unsupported_callback_skipped (safety empty : Bool) :
    (first safety empty (some ⟨.unsupported, fun _ _ _ _ effects => effects + 999⟩)).1 =
      .error (.language .outOfMemory) :=
  (first_completed safety empty _).1

/-- The same reached five-row prefix supplies preparation, geometry and lock
observations; refusal changes neither the selected no-remap callback nor the
allocator's recorded effect. -/
theorem growing_observed (safety empty : Bool) :
    BackingAllocationOOM CallerGrowingChainTests.ops failing 7 6 input
      (CallerGrowingChainTests.normalized safety empty 4) (some CallerGrowingChainTests.growth)
      (CallerGrowingChainTests.taken safety empty 4).2.world := by
  obtain ⟨_, oldCapacity, capacity, capacityRead, nonempty, full, selected, size,
    context, returnAddress, release, growth, operands, remaining, duplicated, object, allocated,
    copied, middle, base, effects, probeEffects, duplicateCall, createCall, cloneCall, response, _, unlocked⟩ :=
    NativeGrowingTests.published_observed safety empty
  refine ⟨operands, remaining, duplicated, object, allocated, copied, middle, effects,
    duplicateCall, createCall, cloneCall, unlocked, Or.inr ⟨oldCapacity, capacity, context, returnAddress,
      release, capacityRead, nonempty, full, selected, size, growth, ?_⟩⟩
  intro installed assigned
  have effectsEqual : installed.effects.allocator * 10 + 7 = effects :=
    congrArg Prod.snd (response installed assigned).1
  change (none, installed.effects.allocator * 10 + 7) = (none, effects)
  rw [effectsEqual]

def growing (safety empty : Bool) :=
  Insertion.Native.insert CallerGrowingChainTests.ops failing safety 7 6 (CallerGrowingChainTests.parent empty) source
    Insertion.Tests.model input (CallerInputTests.key empty) (CallerGrowingChainTests.normalized safety empty 4)
    true (some CallerGrowingChainTests.growth) (CallerGrowingChainTests.taken safety empty 4).2.world

theorem growing_completed (safety empty : Bool) :
    (growing safety empty).1 = .error (.language .outOfMemory) ∧
      GraphFrame safety 7 6 (CallerGrowingChainTests.cells safety empty 4) (fun _ => True) (growing safety empty).2 ∧
      Consumed (CallerGrowingChainTests.normalized safety empty 4) (growing safety empty).2.memory := by
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have entry := prior.caller_input (by decide)
  have reads : (CallerGrowingChainTests.taken safety empty 4).2.world.graph.read =
      Storage.readValue ((CallerGrowingChainTests.taken safety empty 4).2.world.graph.representatives.getD []) := by
    rw [entry.origin.graph]
    cases safety <;> cases empty <;> insertion_kernel_rfl
  exact (NativeGrowingTests.reached_frame safety empty).backing_oom CallerGrowingChainTests.ops failing
    (some CallerGrowingChainTests.growth) Insertion.Tests.model (CallerInputTests.key empty) reads
    (by rw [entry.origin.graph, prior.facts.projected]; simpa only [Option.getD_some, prior.count] using (show 5 < 2 ^ 32 - 1 by decide))
    (Normalization.Tests.external_admitted _) (growing_observed safety empty) (fun _ _ _ => trivial)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.BackingFailureTests
