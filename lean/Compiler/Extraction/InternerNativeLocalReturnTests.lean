/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeLocalParentTests
import Compiler.Extraction.InternerNativeGraphPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime)
open RecursiveTests (Call debug)

attribute [local irreducible] BinaryPreludeTests.ready rootArguments copied localReturned

def published (safety : Bool) := Publication.freshWorld (parent safety).key (parent safety).normalized 4
  ((localReturned safety).2.memory.effects.allocator * 10 + 8) (localReturned safety).2

def returnedRoot (safety : Bool) :=
  let reached := (parent safety).returnedWorld (published safety)
  { reached with memory := { reached.memory with
    memory := Compiler.ZigAir.Memory.cleanup (BinaryPreludeTests.ready safety false).memory.memory.nextId reached.memory.memory } }

theorem root_prepared (safety : Bool) :
    Arguments.Prepared [0, 4] (BinaryPreludeTests.ready safety false) rootSource (parent safety).before :=
  Arguments.prepare_success _ _ _ _ (BinaryPreludeTests.contract safety false).2.1.valid (root_literal safety)

/-- The existing cache-hit/local return retains the full live parent using the
same unchanged-graph adapter as the general early-return leaves. -/
theorem local_parent (safety : Bool) :
    NativeRecursion.CallFrame safety 7 6 (BinaryPreludeTests.rows safety false)
      rootSource [0, 4] (parent safety).normalized (parent safety).address (parent safety).native
      (fun _ => True) (localReturned safety).2 := by
  have literal := root_prepared safety
  have prior := (BinaryPreludeTests.contract safety false).2.1
  have entry := parent_established safety
  have privateSource : Caller.SourcePrivate rootSource (parent safety).constructed.memory.effects.keys := by
    rw [congrArg Publication.Effects.keys entry.item.effects, congrArg Publication.Effects.keys literal.effects]
    exact fun key => literal.key_apart [0, 4] _ _ rootSource prior.valid 7 key prior.live
  have initial := NativeRecursion.CallFrame.caller entry.entry
    (entry.constructed.native (by rw [BinaryPreludeTests.rows_count]; decide)) privateSource
    (literal.arraySource.frame (fun _ cell found => entry.item.memory _ cell found)) (fun _ => True) trivial
  obtain ⟨facts, graph, keys, memory, registry, _⟩ := local_native safety
  have reached : NativeRecursion.GraphFrame safety 7 6 (BinaryPreludeTests.rows safety false)
      (NativeRecursion.Retains (parent safety).taken.2.world) (localReturned safety).2 :=
    ⟨⟨[], _, _, by simpa only [List.append_nil] using facts⟩, keys, memory, registry⟩
  exact (reached.retained_parent graph initial trivial).2

/-- The actual cache-hit child retains the parent's normalized owner and leaves
its missed key absent. Publication consumes that reached ownership and derives
the native graph; neither a final graph nor a child frame is a premise. -/
theorem parent_publication (safety : Bool) :
    Publication.publish ops.probe ops.arguments 7 rootSource (parent safety).key (parent safety).normalized 4
      (localReturned safety).2 = (.ok (), published safety) ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (published safety) (BinaryPreludeTests.rows safety false) := by
  obtain ⟨facts, graph, _⟩ := local_native safety
  have entry := parent_established safety
  obtain ⟨_, _, _, _, custody, _⟩ := (local_parent safety).1.1
  have absent : (localReturned safety).2.memory.effects.keys (parent safety).key = none := by
    have missed := (parent safety).prefix_results (parent_observed safety).2.1 |>.2.2.2.2.2.2.1
    have table : (localReturned safety).2.graph.table (parent safety).key = none := by
      rw [graph, entry.entry.origin.graph, entry.item.graph]; exact missed
    rw [facts.linked] at table
    cases found : (localReturned safety).2.memory.effects.keys (parent safety).key with
    | none => rfl
    | some old => simp only [OwnedKeys.view, found, Option.map_some] at table; cases table
  have fresh : OwnedKeys.Fresh (localReturned safety).2.memory.effects.keys (parent safety).key
      ⟨(parent safety).normalized.address, 4⟩ := by
    intro query old found incoming nonempty alias
    exact custody.apart query old found nonempty ⟨incoming, alias.symm⟩
  exact facts.publish_absent ops.probe ops.arguments rootSource (parent safety).key (parent safety).normalized 4
    ((localReturned safety).2.memory.effects.allocator * 10 + 8) rfl absent custody.live fresh
    (fun row member nonempty => custody.operands (by change [0, 4] ≠ []; decide)
      row (List.mem_append_left _ member) nonempty) rfl

/-- Resume the same parent publication, handoff, detached lookup destruction
and three captured cleanup marks after the named-local child returns. -/
theorem reduced_result (safety : Bool) : reduced safety = (.ok 4, returnedRoot safety) := by
  have scope := (parent_established safety).entry.origin.scope
  have publication := (parent_publication safety).1
  have resumedCall : resumed safety =
      (.ok 4, ⟨published safety, ⟨some (parent safety).lookup, some (parent safety).normalized, true⟩⟩) := by
    simp only [resumed, graph, scope, bind, Effect.bind, publication, handoff, pure, Effect.pure]
  have closed := deinit_detached (Publication.external ops.arguments) 7
    (⟨published safety, ⟨some (parent safety).lookup, some (parent safety).normalized, true⟩⟩ : State _)
    (parent safety).lookup rfl (parent_established safety).entry.origin.detached
  simp only [reduced, resumedCall, OwnedCall.finish, ordinary, ↓reduceIte, OwnedCall.cleanup, closed]
  rfl

/-- Native correspondence and source death follow through the child's frame,
publication and actual returns. Preparation supplies both stack metadata and
cleanup geometry; no final heap observation is reduced as a fixture. -/
theorem reduced_native (safety : Bool) :
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (reduced safety).2 (BinaryPreludeTests.rows safety false) ∧
    (reduced safety).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (reduced safety).2.memory.memory.heap.lookup localSource.allocation = none ∧
    (reduced safety).2.graph.read = (BinaryPreludeTests.ready safety false).graph.read ∧
    (reduced safety).2.memory.effects.keys = OwnedKeys.store (localReturned safety).2.memory.effects.keys
      (parent safety).key ⟨(parent safety).normalized.address, 4⟩ := by
  have preparedRoot := root_prepared safety
  have initial := (BinaryPreludeTests.contract safety false).2.1.native (by rw [BinaryPreludeTests.rows_count]; decide)
  obtain ⟨ownerCell, ownerFound, _, _⟩ := initial.ownerLive
  have ownerOlder := (Compiler.ZigAir.Memory.valid_lookup _ _ _ initial.valid.memory ownerFound).1
  have parentOlder : 6 < (parent safety).before.memory.memory.nextId := by
    rw [preparedRoot.counter]; exact Nat.lt_trans ownerOlder (Nat.lt_succ_self _)
  have publishedFacts := (parent_publication safety).2
  have scratchFacts := publishedFacts.cleanup ((parent safety).before.memory.memory.nextId + 1)
    (Nat.lt_trans parentOlder (Nat.lt_succ_self _))
  have itemFacts := scratchFacts.cleanup (parent safety).before.memory.memory.nextId parentOlder
  have finalFacts := itemFacts.cleanup (BinaryPreludeTests.ready safety false).memory.memory.nextId ownerOlder
  obtain ⟨_, graph, _, frame, _, localGone⟩ := local_native safety
  have entry := parent_established safety
  have parentFrame : ∀ id cell, (parent safety).before.memory.memory.heap.lookup id = some cell →
      (published safety).memory.memory.heap.lookup id = some cell := by
    intro id cell found
    exact frame id cell (entry.entry.origin.memory id cell (entry.item.memory id cell found))
  have returnedFrame := (parent safety).returned_frame (published safety) preparedRoot.good.1 parentFrame
  obtain ⟨sourceCell, sourceFound, _⟩ := preparedRoot.storage (by decide)
  rw [reduced_result]
  refine ⟨finalFacts, ?_, ?_, ?_, rfl⟩
  · exact preparedRoot.retire [0, 4] _ _ rootSource (by decide) _ itemFacts.valid.memory
      ((returnedFrame _ _ sourceFound).trans sourceFound.symm)
  · apply RecursiveTests.cleanup_missing _ _ _ itemFacts.valid.memory
    apply RecursiveTests.cleanup_missing _ _ _ scratchFacts.valid.memory
    exact RecursiveTests.cleanup_missing _ _ _ publishedFacts.valid.memory localGone
  · change (localReturned safety).2.graph.read = _
    rw [graph, entry.entry.origin.graph, entry.item.graph, preparedRoot.graph]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
