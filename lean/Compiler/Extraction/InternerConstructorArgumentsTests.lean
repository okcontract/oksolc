/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorArguments
import Compiler.Extraction.InternerRecursiveChildTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Arguments.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native RecursiveTests
open CallerGrowingChainTests (ops cells lifetime growth GraphFacts)

attribute [local irreducible] rootArguments RecursiveNonemptyTests.ready

theorem literal_prefix (safety : Bool) : prepare [0, 0] (old safety) = (.ok rootSource, (parent safety).before) := by
  have program : prepare [0, 0] (old safety) = rootArguments safety := by unfold prepare rootArguments; rfl
  rw [program]
  exact Prod.ext (root_observed safety).1 rfl

/-- The parent's native input now comes from the literal, item and normalizer
execution together. No initial Good or fresh-map-key premise is supplied. -/
theorem native_entry (safety : Bool) : ∃ normalized remaining,
    CallerInput 7 rootSource (parent safety).address (parent safety).request [0, 0]
      (parent safety).native (parent safety).key (parent safety).constructed (parent safety).taken.2 normalized remaining := by
  have prior := (RecursiveNonemptyTests.zero_contract safety).2.1
  obtain ⟨made, count, allocated, initialized, transferred, _, _, keyed⟩ :=
    (parent safety).prefix_results (observed safety false)
  apply caller_input ops.arguments 160 7 20 [0, 0] debug (old safety) (parent safety).before
    (parent safety).constructed rootSource (parent safety).address (parent safety).stack _ [0, 0]
    (parent safety).prepared.2 (parent safety).taken.2 (parent safety).key prior.valid
    (literal_prefix safety) AssemblyItem.Initializers.Tests.debug_valid (Normalization.Tests.external_admitted _)
    made allocated ?_ ?_ keyed prior.live prior.unique
  · rw [count]; exact Prod.ext initialized rfl
  · simpa only [Call.taken] using (Prod.ext transferred rfl : (parent safety).taken = (.ok (), (parent safety).taken.2))

abbrev complete := RecursiveTests.complete

theorem complete_route (safety : Bool) : complete safety =
    TemporaryArguments.unwind (old safety).memory.memory.nextId (full safety) :=
  RecursiveTests.complete_route safety

theorem literal_stack (safety : Bool) : ∃ cell,
    (parent safety).before.memory.memory.heap.lookup rootSource.allocation = some cell ∧ cell.stack = true := by
  obtain ⟨cell, found, _, _, stack⟩ := prepare_storage [0, 0] (old safety) (parent safety).before rootSource (literal_prefix safety) (by decide)
  exact ⟨cell, found, stack⟩

/-- Enter through the actual literal and complete native constructor, execute
the recursive child and parent defers, then retire the source literal. Rebuild
the reached native graph from original allocation frames, not a final snapshot. -/
theorem complete_contract (safety : Bool) :
    (complete safety).1 = .error (.language .outOfMemory) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (complete safety).2 (RecursiveNonemptyTests.rows safety) ∧
    (complete safety).2.graph = (old safety).graph ∧
    Good (CallerInputTests.argumentView false) [0] (complete safety).2 ∧
    (complete safety).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (complete safety).2.memory.memory.nextId = (full safety).2.world.memory.memory.nextId ∧
    (complete safety).2.memory.memory.nextAddress = (full safety).2.world.memory.memory.nextAddress ∧
    (∀ id cell, (old safety).memory.memory.heap.lookup id = some cell → (complete safety).2.memory.memory.heap.lookup id = some cell) ∧
    (∃ normalized remaining, CallerInput 7 rootSource (parent safety).address (parent safety).request [0, 0]
      (parent safety).native (parent safety).key (parent safety).constructed (parent safety).taken.2 normalized remaining) := by
  obtain ⟨failed, facts, graph, dead, nextId, nextAddress, frame, caller⟩ := RecursiveTests.complete_contract safety
  exact ⟨failed, facts, graph, caller, dead, nextId, nextAddress, frame, native_entry safety⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Arguments.Tests
