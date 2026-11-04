/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveGrowthReturnTests
import Compiler.Extraction.InternerNativeGraphPublicationCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug)
open RecursiveNonemptyTests

attribute [local irreducible] ready rootArguments childArguments Arguments.operation

def published (safety : Bool) (world : World (Publication.Effects Nat)) :=
  Publication.freshWorld (parent safety).key (parent safety).normalized 5 (world.memory.effects.allocator * 10 + 8) world

def returnedRoot (safety : Bool) (world : World (Publication.Effects Nat)) :=
  let reached := (parent safety).returnedWorld (published safety world)
  { reached with memory := { reached.memory with
    memory := Compiler.ZigAir.Memory.cleanup (ready safety).memory.memory.nextId reached.memory.memory } }

def root (safety : Bool) (depth : Nat) := (children safety depth).operation 20 [0, 4] debug (ready safety)

/-- Publication consumes the parent's actual retained normalized allocation.
The child's returned custody is derived from actual normalization, duplication
and publication, including separation from its newly appended operand. -/
theorem parent_ownership (safety : Bool) (world : World (Publication.Effects Nat))
    (custody : Caller.GraphCustody 7 (parent safety).normalized (appendedRows safety) world.memory)
    (keys : world.memory.effects.keys = OwnedKeys.store (parent safety).taken.2.world.memory.effects.keys
      (child safety).key ⟨(child safety).normalized.address, 5⟩) :
    world.memory.effects.keys (parent safety).key = none ∧
    OwnedKeys.Apart world.memory.effects.keys
      (fun address => (parent safety).normalized.items ≠ [] ∧ address = (parent safety).normalized.address) ∧
    (∀ logical ∈ appendedRows safety, logical.arguments ≠ [] → (parent safety).normalized.address ≠ logical.argumentsAddress) := by
  have absent : world.memory.effects.keys (parent safety).key = none := by
    rw [keys, OwnedKeys.store, if_neg (by
      intro equal
      have impossible : (20 : Opcode) = 21 := congrArg Key.instruction equal
      contradiction), ← (prefix_keys safety).1]
    exact (prefix_keys safety).2.2
  exact ⟨absent, custody.apart, custody.operands (by change [0, 4] ≠ []; decide)⟩

theorem parent_publication (safety : Bool) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety (backing safety) 13 world (appendedRows safety))
    (held : Held 7 rootSource [0, 4] (parent safety).normalized world)
    (custody : Caller.GraphCustody 7 (parent safety).normalized (appendedRows safety) world.memory)
    (privateSource : Caller.SourcePrivate rootSource world.memory.effects.keys)
    (keys : world.memory.effects.keys = OwnedKeys.store (parent safety).taken.2.world.memory.effects.keys
      (child safety).key ⟨(child safety).normalized.address, 5⟩) :
    Publication.publish ops.probe ops.arguments 7 rootSource (parent safety).key (parent safety).normalized 5 world =
      (.ok (), published safety world) ∧
    NativeGraph.Facts safety 7 6 ⟨backing safety, 0⟩ 13 (published safety world) (appendedRows safety) := by
  have absent := (parent_ownership safety world custody keys).1
  have called := Publication.publish_absent ops.probe ops.arguments 7 rootSource (parent safety).key
    (parent safety).normalized 5 (world.memory.effects.allocator * 10 + 8) world rfl absent rfl
  have nativeFacts := facts.native (by simp only [appendedRows, List.length_append, List.length_singleton, rows_count]; decide)
  have preserved := nativeFacts.publish ops.probe ops.arguments rootSource [0, 4] (parent safety).key
    (parent safety).normalized 5 true (world.memory.effects.allocator * 10 + 8) rfl held custody privateSource rfl
  exact ⟨called, by simpa only [called] using preserved.2.1⟩

theorem parent_simplifier (safety : Bool) (depth : Nat) (world : World (Publication.Effects Nat))
    (publishOK : Bool)
    (called : (children safety (depth + 1) publishOK).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, world)) :
    (primitives safety (depth + 1) rootSource publishOK (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world = (.ok (some 5), world) := by
  have facts := (parent_established safety).taken.native (by rw [rows_count]; decide)
  simp only [primitives, NativeRecursion.dispatcher_snapshot]
  rw [facts.reads]
  exact iszero_result (input := NativeRecursion.operand) (address := (parent safety).normalized.address)
    (Interner.representativeReads (parent safety).taken.2.world.graph)
    (children safety (depth + 1) publishOK) (parent safety).taken.2.world world (.ok 5)
    (first_constant safety _ (parent_established safety).taken).1 (parent_zero safety).1 called

theorem parent_continuation (safety : Bool) (depth : Nat) (world : World (Publication.Effects Nat))
    (called : (children safety (depth + 1)).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, world))
    (publication : Publication.publish ops.probe ops.arguments 7 rootSource (parent safety).key (parent safety).normalized 5 world =
      (.ok (), published safety world)) :
    (parent safety).continuation (primitives safety (depth + 1) rootSource true (parent safety).address (parent safety).native) =
      (.ok 5, ⟨published safety world, ⟨some (parent safety).lookup, some (parent safety).normalized, true⟩⟩) := by
  have scope := (parent_established safety).entry.origin.scope
  have simplified := parent_simplifier safety depth world true called
  simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
    show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
    graph, scope, simplified, bind, Effect.bind]
  simp only [primitives, NativeRecursion.context, base, callerPrimitives, show publicationProbe true = ops.probe from rfl,
    Interner.findCode, Interner.ResultId.run, publication, handoff, pure, Effect.pure]

/-- The successful child result resumes the parent publication, handoff and
both local defers, then the root literal's cleanup. -/
theorem root_result (safety : Bool) (depth : Nat) (world : World (Publication.Effects Nat))
    (called : (children safety (depth + 1)).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, world))
    (publication : Publication.publish ops.probe ops.arguments 7 rootSource (parent safety).key (parent safety).normalized 5 world =
      (.ok (), published safety world)) :
    root safety (depth + 2) = (.ok 5, returnedRoot safety world) := by
  have established := parent_established safety
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have routed := (parent safety).route (primitives safety (depth + 1) rootSource true) (calls_observed safety false)
    established.item.graph room rfl
  rw [parent_continuation safety depth world called publication] at routed
  simp only [ordinary] at routed
  have literal : Arguments.prepare [0, 4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [root, children, show depth + 2 = (depth + 1) + 1 from rfl, NativeRecursion.operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0, 4] _ ((parent safety).invoked (primitives safety (depth + 1) rootSource true)) = _
  rw [routed]; rfl

theorem parent_mark (safety : Bool) : (parent safety).before.memory.memory.nextId = 25 := by
  change (rootArguments safety).2.memory.memory.nextId = 25
  rw [(parent_literal safety).1.counter, (literals_observed safety).2.1]
  rfl

/-- The final graph invariant is derived through parent publication and all
three parent/outer cleanup marks, including the relocated backing. -/
theorem root_native (safety : Bool) (depth : Nat) : ∃ after,
    root safety (depth + 2) = (.ok 5, returnedRoot safety (returnedChild safety after)) ∧
    NativeGraph.Facts safety 7 6 ⟨backing safety, 0⟩ 13 (root safety (depth + 2)).2 (appendedRows safety) ∧
    (children safety (depth + 1)).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, returnedChild safety after) ∧
    Held 7 rootSource [0, 4] (parent safety).normalized (returnedChild safety after) ∧
    (root safety (depth + 2)).2.memory.effects.keys = OwnedKeys.store
      (OwnedKeys.store (parent safety).taken.2.world.memory.effects.keys (child safety).key ⟨(child safety).normalized.address, 5⟩)
      (parent safety).key ⟨(parent safety).normalized.address, 5⟩ ∧
    (root safety (depth + 2)).2.memory.heap ReachablePrefixTests.backing = none ∧
    (root safety (depth + 2)).2.memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (root safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none := by
  obtain ⟨after, called, facts, held, keys, native, _, oldDead, nativeDead, custody, privateSource, _⟩ := child_contract safety depth
  have publication := parent_publication safety (returnedChild safety after) facts held custody privateSource keys
  have result := root_result safety depth _ called publication.1
  have innerFacts := (publication.2.cleanup ((parent safety).before.memory.memory.nextId + 1)
    (by rw [parent_mark]; decide)).cleanup (parent safety).before.memory.memory.nextId (by rw [parent_mark]; decide)
  have finalFacts := innerFacts.cleanup (ready safety).memory.memory.nextId (by rw [(literals_observed safety).2.1]; decide)
  obtain ⟨sourceCell, sourceFound, _⟩ := literal_stack safety
  have entry := parent_established safety
  have sourceLocated := native _ sourceCell (entry.entry.origin.memory _ _ (entry.item.memory _ _ sourceFound))
    (parent_input safety).2.1 (parent_input safety).2.2
  have sourceInner := (Compiler.ZigAir.Memory.cleanup_lookup_older (published safety (returnedChild safety after)).memory.memory
    ((parent safety).before.memory.memory.nextId + 1) rootSource.allocation (by rw [parent_mark]; decide)).trans sourceLocated
  have sourceOuter := (Compiler.ZigAir.Memory.cleanup_lookup_older _ (parent safety).before.memory.memory.nextId rootSource.allocation
    (by rw [parent_mark]; decide)).trans sourceInner
  refine ⟨after, result, ?_, called, held, ?_, ?_, ?_, ?_⟩
  · rw [result]; exact finalFacts
  · rw [result]
    exact congrArg (fun table => OwnedKeys.store table (parent safety).key ⟨(parent safety).normalized.address, 5⟩) keys
  · rw [result]; exact oldDead
  · rw [result]
    apply RecursiveTests.cleanup_missing _ _ _ innerFacts.valid.memory
    apply RecursiveTests.cleanup_missing _ _ _ (publication.2.valid.cleanup _ ((parent safety).before.memory.memory.nextId + 1)).memory
    exact RecursiveTests.cleanup_missing _ _ _ publication.2.valid.memory nativeDead
  · rw [result]
    exact (parent_literal safety).1.retire [0, 4] _ _ rootSource (by decide) _ innerFacts.valid.memory
      (sourceOuter.trans sourceFound.symm)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
