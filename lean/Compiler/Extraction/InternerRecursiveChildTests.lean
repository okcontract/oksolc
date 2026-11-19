/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveChildDispatchTests
import Compiler.Extraction.InternerRecursiveCallFailureTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)

-- Use the established root-state facts instead of reducing the initialized
-- constructor prefix while elaborating each field of the final frame.
attribute [local irreducible] rootArguments RecursiveNonemptyTests.ready

theorem held_after_child (safety : Bool) (world : World (Publication.Effects Nat)) (valid : Valid world.memory)
    (native : ∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →
      world.memory.memory.heap.lookup id = some cell)
    (registry : ∀ id block, (parent safety).taken.2.world.memory.heap id = some block → world.memory.heap id = some block) :
    Held 7 (parent safety).source (parent safety).request.arguments (parent safety).normalized world :=
  held_retained 7 (parent safety).source (parent safety).request.arguments (parent safety).normalized
    (parent safety).taken.2.world world (parent_established safety).entry.origin.held valid native registry

theorem cleanup_missing (state : Compiler.ZigAir.Memory.State) (mark id : Nat)
    (valid : state.valid = true) (missing : state.heap.lookup id = none) :
    (Compiler.ZigAir.Memory.cleanup mark state).heap.lookup id = none := Call.cleanup_missing state mark id valid missing

/-- Actual EQ(x,x) dispatch calls the full constant constructor, attempts
nonempty backing growth, receives allocation OOM and returns to the parent's
ordinary defer. Input, cleanup and all old-allocation frames are derived from
that one execution. The initialized prefix and this path do not close RC's
remaining constructor closure or recursive induction. -/
theorem full_contract (safety : Bool) : ∃ childAfter cleaned,
    childFull safety = (.error (.language .outOfMemory),
      ⟨childReturned safety childAfter, ⟨none, some (child safety).normalized, true⟩⟩) ∧
    Held 7 rootSource [0, 0] (parent safety).normalized (childReturned safety childAfter) ∧
    free (Publication.external ops.arguments) 7 (parent safety).normalized (childReturned safety childAfter).memory =
      (.ok (), cleaned.world.memory) ∧
    full safety = (.error (.language .outOfMemory), (parent safety).returned cleaned) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (full safety).2.world (RecursiveNonemptyTests.rows safety) ∧
    (full safety).2.world.graph = (parent safety).before.graph ∧
    Good rootSource [0, 0] (full safety).2.world ∧
    Good (CallerInputTests.argumentView false) [0] (full safety).2.world ∧
    Closed (full safety).2.scope ∧
    Consumed (parent safety).normalized (full safety).2.world.memory ∧
    (full safety).2.world.memory.effects.allocator = (childReturned safety childAfter).memory.effects.allocator + 102 ∧
    (∀ id native, (parent safety).before.memory.memory.heap.lookup id = some native →
      (full safety).2.world.memory.memory.heap.lookup id = some native) ∧
    (full safety).2.world.memory.effects.keys = (parent safety).before.memory.effects.keys ∧
    (∀ id block, (parent safety).before.memory.heap id = some block → (full safety).2.world.memory.heap id = some block) := by
  obtain ⟨childAfter, called, childFacts, childKeys, native, registry⟩ := child_contract safety
  have established := parent_established safety
  have bounded : (RecursiveNonemptyTests.rows safety).length ≤ 5 := by rw [RecursiveNonemptyTests.rows_count]; decide
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, RecursiveNonemptyTests.rows_count]; decide
  have childGraph : (childReturned safety childAfter).graph = (parent safety).taken.2.world.graph :=
    (child_established safety).entry.origin.graph.trans (child_established safety).item.graph
  obtain ⟨cleaned, held, freed, routed, graphFacts, graph, closed, consumed, effects, frame, keys, registry⟩ :=
    (parent safety).simplifier_oom (parentPrimitives safety) safety ReachablePrefixTests.backing 5
      (RecursiveNonemptyTests.rows safety) (root_facts safety).2.1 bounded established (observed safety false)
      room rfl rfl _ (parent_simplified safety childAfter called) childFacts.valid childGraph childKeys native registry
  have result : full safety = (.error (.language .outOfMemory), (parent safety).returned cleaned) := routed
  refine ⟨childAfter, cleaned, called, held, freed, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result]; exact graphFacts
  · rw [result]; exact graph
  · rw [result]; exact good_frame _ _ _ _ (root_facts safety).1 graphFacts.valid frame
  · rw [result]; exact good_frame _ _ _ _ (root_facts safety).2.2 graphFacts.valid frame
  · rw [result]; exact closed
  · rw [result]; exact consumed
  · rw [result]; exact congrArg Publication.Effects.allocator effects
  · rw [result]; exact frame
  · rw [result]; exact keys
  · rw [result]; exact registry

/-- Failure preserves all prior graph-word observations; this says nothing
about successful results or the still-open recursive induction. -/
theorem prior_words (safety : Bool) (id : NodeId) :
    (full safety).2.world.graph.read id = (parent safety).before.graph.read id := by
  obtain ⟨_, _, _, _, _, _, _, graph, _⟩ := full_contract safety
  exact congrArg (fun heap => heap.read id) graph

theorem complete_route (safety : Bool) : complete safety =
    TemporaryArguments.unwind (old safety).memory.memory.nextId (full safety) := by
  have literal : Arguments.prepare [0, 0] (old safety) = (.ok rootSource, (parent safety).before) := by
    change TemporaryArguments.prepare 0 0 (old safety) = (.ok rootSource, (rootArguments safety).2)
    simpa only [rootArguments] using
      (Prod.ext (root_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [complete, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  exact Arguments.returned_nonempty [0, 0] _ _ rfl

/-- The same constant-error execution returns through the original literal's
scope. Existing graph cleanup and literal retirement contracts retain all
initial caller allocations and remove only the reached temporary lifetime. -/
theorem complete_contract (safety : Bool) :
    (complete safety).1 = .error (.language .outOfMemory) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (complete safety).2 (RecursiveNonemptyTests.rows safety) ∧
    (complete safety).2.graph = (old safety).graph ∧
    (complete safety).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (complete safety).2.memory.memory.nextId = (full safety).2.world.memory.memory.nextId ∧
    (complete safety).2.memory.memory.nextAddress = (full safety).2.world.memory.memory.nextAddress ∧
    (∀ id cell, (old safety).memory.memory.heap.lookup id = some cell →
      (complete safety).2.memory.memory.heap.lookup id = some cell) ∧
    Good (CallerInputTests.argumentView false) [0] (complete safety).2 := by
  obtain ⟨_, _, _, _, _, result, facts, graph, _, _, _, _, _, native, _, _⟩ := full_contract safety
  have literal := (root_literal safety).1
  have prior := (RecursiveNonemptyTests.zero_contract safety).2.1
  have failed : (full safety).1 = .error (.language .outOfMemory) := congrArg Prod.fst result
  have ordinary : ordinary (full safety).1 = true := by rw [failed]; rfl
  have reached : (complete safety).2 = { (full safety).2.world with memory := { (full safety).2.world.memory with
      memory := Compiler.ZigAir.Memory.cleanup (old safety).memory.memory.nextId (full safety).2.world.memory.memory } } := by
    rw [complete_route]; simp only [TemporaryArguments.unwind, ordinary, ↓reduceIte]
  have finalFacts : GraphFacts safety ReachablePrefixTests.backing 5 (complete safety).2 (RecursiveNonemptyTests.rows safety) := by
    rw [reached]
    exact facts.cleanup _ (by rw [(root_observed safety).2.1]; decide)
      (by change 5 < (old safety).memory.memory.nextId; rw [(root_observed safety).2.1]; decide)
      (by rw [RecursiveNonemptyTests.rows_count]; decide)
  have frame : ∀ id cell, (old safety).memory.memory.heap.lookup id = some cell →
      (complete safety).2.memory.memory.heap.lookup id = some cell := by
    intro id cell found
    rw [reached]
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id
      (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1).trans (native id cell (literal.frame id cell found))
  obtain ⟨cell, found, _, _, _⟩ := literal.storage (by decide)
  have dead : (complete safety).2.memory.memory.heap.lookup rootSource.allocation = none := by
    rw [reached]
    exact literal.retire [0, 0] _ _ rootSource (by decide) _ facts.valid.memory ((native _ _ found).trans found.symm)
  refine ⟨?_, finalFacts, ?_, dead, ?_, ?_, frame,
    good_frame _ _ _ _ (RecursiveNonemptyTests.caller_source safety) finalFacts.valid frame⟩
  · rw [complete_route]; exact failed
  · rw [reached]; exact graph.trans literal.graph
  · rw [reached]; rfl
  · rw [reached]; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
