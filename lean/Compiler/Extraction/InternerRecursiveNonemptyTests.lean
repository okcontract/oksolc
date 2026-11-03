/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveNonemptyDispatchTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (Call debug cleanup_missing)

-- Use the established root-state facts instead of reducing the five-insertion
-- history while elaborating each field of the final frame.
attribute [local irreducible] ready rootArguments childArguments Arguments.operation

theorem held_after_child (safety : Bool) (world : World (Publication.Effects Nat)) (valid : Valid world.memory)
    (native : ∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →
      world.memory.memory.heap.lookup id = some cell)
    (registry : ∀ id block, (parent safety).taken.2.world.memory.heap id = some block → world.memory.heap id = some block) :
    Held 7 (parent safety).source (parent safety).request.arguments (parent safety).normalized world := by
  have held := (parent_established safety).entry.origin.held
  refine ⟨good_frame _ _ _ _ held.1 valid native, ?_, held.2.2⟩
  rcases held.2.1 with empty | stored
  · exact Or.inl empty
  · exact Or.inr (registry _ _ stored)

/-- Actual EQ(x,0) dispatch calls the full nonempty ISZERO constructor,
attempts backing growth, receives allocation OOM and returns to the parent's
ordinary defer. Input, cleanup and all old-allocation frames are derived from
that one execution. The initialized prefix and this path do not close RC's
remaining constructor closure or recursive induction. -/
theorem full_contract (safety : Bool) : ∃ childAfter cleaned,
    childFull safety = (.error (.language .outOfMemory), childReturned safety childAfter) ∧
    Held 7 rootSource [0, 4] (parent safety).normalized (childReturned safety childAfter) ∧
    free (Publication.external ops.arguments) 7 (parent safety).normalized (childReturned safety childAfter).memory =
      (.ok (), cleaned.world.memory) ∧
    full safety = (.error (.language .outOfMemory), (parent safety).returned cleaned) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (full safety).2.world (rows safety) ∧
    (full safety).2.world.graph = (parent safety).before.graph ∧
    Good rootSource [0, 4] (full safety).2.world ∧
    Closed (full safety).2.scope ∧
    Consumed (parent safety).normalized (full safety).2.world.memory ∧
    (full safety).2.world.memory.effects.allocator = (childReturned safety childAfter).memory.effects.allocator + 102 ∧
    (∀ id native, (parent safety).before.memory.memory.heap.lookup id = some native →
      (full safety).2.world.memory.memory.heap.lookup id = some native) ∧
    (full safety).2.world.memory.effects.keys = (parent safety).before.memory.effects.keys ∧
    (∀ id block, (parent safety).before.memory.heap id = some block → (full safety).2.world.memory.heap id = some block) := by
  obtain ⟨childAfter, called, childFacts, childGraph, childKeys, native, registry, _⟩ := child_contract safety
  have established := parent_established safety
  have origin := established.entry.origin
  have held := held_after_child safety (childReturned safety childAfter) childFacts.valid native registry
  let reached : OwnedCall.State (Publication.Effects Nat) := ⟨childReturned safety childAfter, (parent safety).taken.2.scope⟩
  obtain ⟨cleaned, finished, post⟩ := finish_taken (Publication.external ops.arguments) 7 (parent safety).source
    (parent safety).request.arguments (parent safety).normalized (parent safety).lookup reached
    (Except.error (.language .outOfMemory) : Except OwnedCall.Fault NodeId) rfl
    (by change (parent safety).taken.2.scope.lookup = _; rw [origin.scope]) origin.detached
    (by change (parent safety).taken.2.scope.slice = _; rw [origin.scope]) held.1 (fun _ => held.2.1) held.2.2
  have owned : reached.scope.handedOff = false := by change (parent safety).taken.2.scope.handedOff = false; rw [origin.scope]
  have freed := (post.freed owned).1
  obtain ⟨memory, freeCall, _, released, effects⟩ := free_valid (Publication.external ops.arguments) 7
    (parent safety).normalized (childReturned safety childAfter).memory held.1.1 held.2.1
  have same : memory = cleaned.world.memory := congrArg Prod.snd (freeCall.symm.trans freed)
  rw [same] at released effects
  have bounded : (rows safety).length ≤ 5 := by rw [rows_count]; decide
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have routed := (parent safety).route (parentPrimitives safety) (calls_observed safety false) established.item.graph room rfl
  rw [parent_continuation safety childAfter called] at routed
  change full safety = (let done := OwnedCall.finish (Publication.external ops.arguments) 7 (.error (.language .outOfMemory)) reached
    if ordinary done.1 then (done.1, (parent safety).returned done.2) else done) at routed
  rw [finished] at routed
  have result : full safety = (.error (.language .outOfMemory), (parent safety).returned cleaned) := routed
  have initialNative : ∀ id cell, (parent safety).before.memory.memory.heap.lookup id = some cell →
      cleaned.world.memory.memory.heap.lookup id = some cell := by
    intro id cell found
    have constructed := established.item.memory id cell found
    exact (released.frame id (origin.freshNative id cell constructed).symm).2.trans
      (native id cell (origin.memory id cell constructed))
  have initialRegistry : ∀ id block, (parent safety).before.memory.heap id = some block → cleaned.world.memory.heap id = some block := by
    intro id block found
    have constructed : (parent safety).constructed.memory.heap id = some block := by rw [established.item.heap]; exact found
    exact (released.frame id (origin.fresh id block constructed).symm).1.trans
      (registry id block (origin.registry id block constructed))
  have returnedValid := (parent safety).returned_valid cleaned.world post.good.1
  have frame := (parent safety).returned_frame cleaned.world (parent_literal safety).1.good.1 initialNative
  have graph : cleaned.world.graph = (parent safety).before.graph :=
    post.graph.trans (childGraph.trans (origin.graph.trans established.item.graph))
  have keys : cleaned.world.memory.effects.keys = (parent safety).before.memory.effects.keys := by
    have kept := free_keys ops.arguments 7 (parent safety).normalized (childReturned safety childAfter).memory
    rw [freed] at kept
    exact kept.trans (childKeys.trans (established.entry.keys.trans (congrArg Publication.Effects.keys established.item.effects)))
  have graphFacts : GraphFacts safety ReachablePrefixTests.backing 5 ((parent safety).returned cleaned).world (rows safety) := by
    apply (parent_literal safety).2.frame bounded returnedValid
    · exact (congrArg Interner.Heap.representatives graph).trans (parent_literal safety).2.projected
    · exact congrArg Interner.Heap.table graph
    · exact keys
    · exact frame
    · exact initialRegistry
  have consumed := (post.freed owned).2
  have dead := consumed.resolve_left (by change [0, 4] ≠ []; decide)
  have returnedDead : Consumed (parent safety).normalized ((parent safety).returned cleaned).world.memory := by
    refine Or.inr ⟨dead.1, ?_⟩
    apply cleanup_missing _ _ _ (post.good.1.cleanup _ ((parent safety).before.memory.memory.nextId + 1)).memory
    exact cleanup_missing _ _ _ post.good.1.memory dead.2
  refine ⟨childAfter, cleaned, called, held, freed, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result]; exact graphFacts
  · rw [result]; exact graph
  · rw [result]; exact good_frame _ _ _ _ (parent_literal safety).1.good returnedValid frame
  · rw [result]; exact post.closed
  · rw [result]; exact returnedDead
  · rw [result]
    exact congrArg Publication.Effects.allocator effects
  · rw [result]; exact frame
  · rw [result]; exact keys
  · rw [result]; exact initialRegistry

/-- Failure preserves all prior graph-word observations; this says nothing
about successful results or the still-open recursive induction. -/
theorem prior_words (safety : Bool) (id : NodeId) :
    (full safety).2.world.graph.read id = (parent safety).before.graph.read id := by
  obtain ⟨_, _, _, _, _, _, _, graph, _⟩ := full_contract safety
  exact congrArg (fun heap => heap.read id) graph

theorem complete_route (safety : Bool) : complete safety =
    TemporaryArguments.unwind (ready safety).memory.memory.nextId (full safety) := by
  have literal : Arguments.prepare [0, 4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [complete, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  exact Arguments.returned_nonempty [0, 4] _ _ rfl

theorem literal_stack (safety : Bool) : ∃ cell,
    (parent safety).before.memory.memory.heap.lookup rootSource.allocation = some cell ∧ cell.stack = true := by
  obtain ⟨cell, found, _, _, stack⟩ := (parent_literal safety).1.storage (by decide)
  exact ⟨cell, found, stack⟩

/-- Enter through the actual literal and complete native constructor, execute
the recursive child and parent defers, then retire the source literal. Rebuild
the reached native graph from original allocation frames, not a final snapshot. -/
theorem complete_contract (safety : Bool) :
    (complete safety).1 = .error (.language .outOfMemory) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (complete safety).2 (rows safety) ∧
    (complete safety).2.graph = (ready safety).graph ∧
    (complete safety).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (complete safety).2.memory.memory.nextId = (full safety).2.world.memory.memory.nextId ∧
    (complete safety).2.memory.memory.nextAddress = (full safety).2.world.memory.memory.nextAddress ∧
    (∀ id cell, (ready safety).memory.memory.heap.lookup id = some cell → (complete safety).2.memory.memory.heap.lookup id = some cell) ∧
    (∀ id, (complete safety).2.graph.read id = (ready safety).graph.read id) := by
  obtain ⟨childAfter, cleaned, _, _, _, result, facts, graph, _, _, _, _, native, keys, registered⟩ := full_contract safety
  have prior := (zero_contract safety).2.1
  have literal := (parent_literal safety).1
  have failed : (full safety).1 = .error (.language .outOfMemory) := congrArg Prod.fst result
  have ordinary : ordinary (full safety).1 = true := by rw [failed]; rfl
  have reached : (complete safety).2 = { (full safety).2.world with memory := { (full safety).2.world.memory with
      memory := Compiler.ZigAir.Memory.cleanup (ready safety).memory.memory.nextId (full safety).2.world.memory.memory } } := by
    rw [complete_route]; simp only [TemporaryArguments.unwind, ordinary, ↓reduceIte]
  have valid : Valid (complete safety).2.memory := by rw [reached]; exact facts.valid.cleanup _ _
  have frame : ∀ id cell, (ready safety).memory.memory.heap.lookup id = some cell →
      (complete safety).2.memory.memory.heap.lookup id = some cell := by
    intro id cell found
    rw [reached]
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id
      (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1).trans (native id cell (literal.frame id cell found))
  have graph : (complete safety).2.graph = (ready safety).graph := by rw [reached]; exact graph.trans literal.graph
  have graphFacts : GraphFacts safety ReachablePrefixTests.backing 5 (complete safety).2 (rows safety) := by
    apply prior.frame (by rw [rows_count]; decide) valid
    · rw [graph]; exact prior.projected
    · exact congrArg Interner.Heap.table graph
    · rw [reached]; exact keys.trans (congrArg Publication.Effects.keys literal.effects)
    · exact frame
    · intro id block found
      rw [reached]
      apply registered id block
      change (rootArguments safety).2.memory.heap id = _
      rw [literal.heap]; exact found
  obtain ⟨cell, found, _⟩ := literal_stack safety
  have dead : (complete safety).2.memory.memory.heap.lookup rootSource.allocation = none := by
    rw [reached]
    exact literal.retire [0, 4] _ _ rootSource (by decide) _ facts.valid.memory
      ((native _ _ found).trans found.symm)
  refine ⟨?_, graphFacts, graph, dead, ?_, ?_, frame,
    fun id => congrArg (fun heap => heap.read id) graph⟩
  · rw [complete_route]; exact failed
  · rw [reached]; rfl
  · rw [reached]; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
