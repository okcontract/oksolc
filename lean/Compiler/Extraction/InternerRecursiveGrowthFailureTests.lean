/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveGrowthParentTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime GraphFacts)
open RecursiveTests (Call debug cleanup_missing)
open RecursiveNonemptyTests

attribute [local irreducible] ready rootArguments childArguments Arguments.operation

def failedRoot (safety : Bool) (depth : Nat) :=
  (children safety depth false).operation 20 [0, 4] debug (ready safety)

def failedReturn (safety : Bool) (world : World (Publication.Effects Nat)) :=
  let reached := (parent safety).returnedWorld world
  { reached with memory := { reached.memory with
    memory := Compiler.ZigAir.Memory.cleanup (ready safety).memory.memory.nextId reached.memory.memory } }

/-- The same recursive family reaches publication after the successful child.
Probe failure skips handoff; finish consumes the parent's still-private owner. -/
theorem failed_root_result (safety : Bool) (depth : Nat) (world probed : World (Publication.Effects Nat))
    (cleaned : OwnedCall.State (Publication.Effects Nat))
    (called : (children safety (depth + 1) false).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, world))
    (publication : Publication.publish (publicationProbe false) ops.arguments 7 rootSource
      (parent safety).key (parent safety).normalized 5 world = (.error (.language .outOfMemory), probed))
    (finished : OwnedCall.finish (Publication.external ops.arguments) 7 (.error (.language .outOfMemory) : Except Fault NodeId)
      ⟨probed, (parent safety).taken.2.scope⟩ = (.error (.language .outOfMemory), cleaned)) :
    failedRoot safety (depth + 2) = (.error (.language .outOfMemory), failedReturn safety cleaned.world) := by
  have established := parent_established safety
  have scope := established.entry.origin.scope
  have simplified := parent_simplifier safety depth world false called
  have continued : (parent safety).continuation
      (primitives safety (depth + 1) rootSource false (parent safety).address (parent safety).native) =
      (.error (.language .outOfMemory), ⟨probed, (parent safety).taken.2.scope⟩) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, scope, simplified, bind, Effect.bind]
    simp only [primitives, NativeRecursion.context, base, callerPrimitives,
      Interner.findCode, Interner.ResultId.run, publication]
  have room : Interner.Queries.queries.atCapacity (parent safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have routed := (parent safety).route (primitives safety (depth + 1) rootSource false)
    (calls_observed safety false) established.item.graph room rfl
  rw [continued] at routed
  simp only [finished] at routed
  simp only [ordinary, Fault.recoverable, ↓reduceIte] at routed
  have literal : Arguments.prepare [0, 4] (ready safety) = (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  rw [failedRoot, children, show depth + 2 = (depth + 1) + 1 from rfl, NativeRecursion.operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0, 4] _ ((parent safety).invoked (primitives safety (depth + 1) rootSource false)) = _
  rw [routed]; rfl

/-- Successful nonempty relocation survives a later parent OOM. Ownership and
separation come from that child return and both actual normalizations. Native
query correspondence survives free and every parent/outer stack cleanup. -/
theorem failed_root_native (safety : Bool) (depth : Nat) :
    (failedRoot safety (depth + 2)).1 = .error (.language .outOfMemory) ∧
    NativeGraph.Facts safety 7 6 ⟨backing safety, 0⟩ 13 (failedRoot safety (depth + 2)).2 (appendedRows safety) ∧
    (failedRoot safety (depth + 2)).2.memory.effects.keys (parent safety).key = none ∧
    (failedRoot safety (depth + 2)).2.memory.effects.keys (child safety).key = some ⟨(child safety).normalized.address, 5⟩ ∧
    Consumed (parent safety).normalized (failedRoot safety (depth + 2)).2.memory ∧
    (failedRoot safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (failedRoot safety (depth + 2)).2.memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (failedRoot safety (depth + 2)).2.graph.read = Storage.readValue (appendedRows safety) := by
  obtain ⟨after, called, facts, held, keys, native, _, _, nativeDead, custody, privateSource, _⟩ := child_contract safety depth false
  have ownership := parent_ownership safety (returnedChild safety after) custody keys
  let world := returnedChild safety after
  have nativeFacts := facts.native (by simp only [appendedRows, List.length_append, List.length_singleton, rows_count]; decide)
  have established := parent_established safety
  have origin := established.entry.origin
  let entered : OwnedCall.State (Publication.Effects Nat) := ⟨world, (parent safety).taken.2.scope⟩
  obtain ⟨probed, cleaned, publication, _, finished, cleanFacts, post, keptKeys, consumed, _⟩ :=
    nativeFacts.finish_publication (before := entered) (publicationProbe false) ops.arguments rootSource [0, 4]
      (parent safety).key (parent safety).normalized (parent safety).lookup 5 false
      (world.memory.effects.allocator * 10 + 8) origin.scope origin.detached rfl held custody privateSource rfl
  have scope : { entered.scope with handedOff := false } = (parent safety).taken.2.scope := by
    change { (parent safety).taken.2.scope with handedOff := false } = _
    rw [origin.scope]
  simp only [Bool.false_eq_true, ↓reduceIte, scope] at publication finished post keptKeys consumed
  have owned : (parent safety).taken.2.scope.handedOff = false := by rw [origin.scope]
  have freed := (post.freed owned).1
  have publishedSame : probed = { world with memory := { world.memory with
      effects := { world.memory.effects with allocator := world.memory.effects.allocator * 10 + 8 } } } := by
    have ran := Publication.publish_oom (publicationProbe false) ops.arguments 7 rootSource
      (parent safety).key (parent safety).normalized 5 world (world.memory.effects.allocator * 10 + 8)
      (Publication.admit_complete _ _ _ _ _ (custody.publication rootSource (parent safety).key rfl privateSource nativeFacts.live)) rfl
    exact congrArg Prod.snd (publication.symm.trans ran)
  have heldProbed : Held 7 rootSource [0, 4] (parent safety).normalized probed := by
    rw [publishedSame]
    exact ⟨⟨⟨held.1.1.memory, held.1.1.related, held.1.1.injected⟩, held.1.2⟩, held.2⟩
  obtain ⟨memory, freeCall, _, released, _⟩ := free_valid (Publication.external ops.arguments) 7
    (parent safety).normalized probed.memory heldProbed.1.1 heldProbed.2.1
  have same : memory = cleaned.world.memory := congrArg Prod.snd (freeCall.symm.trans freed)
  rw [same] at released
  have result := failed_root_result safety depth world probed cleaned called publication finished
  have innerFacts := (cleanFacts.cleanup ((parent safety).before.memory.memory.nextId + 1)
    (by rw [parent_mark]; decide)).cleanup (parent safety).before.memory.memory.nextId (by rw [parent_mark]; decide)
  have finalFacts := innerFacts.cleanup (ready safety).memory.memory.nextId (by rw [(literals_observed safety).2.1]; decide)
  have cleanDead := consumed.resolve_left (by change [0, 4] ≠ []; decide)
  have keepMissing (id : Nat) (missing : cleaned.world.memory.memory.heap.lookup id = none) :
      (failedReturn safety cleaned.world).memory.memory.heap.lookup id = none := by
    apply cleanup_missing _ _ _ innerFacts.valid.memory
    apply cleanup_missing _ _ _ (cleanFacts.valid.cleanup _ ((parent safety).before.memory.memory.nextId + 1)).memory
    exact cleanup_missing _ _ _ cleanFacts.valid.memory missing
  obtain ⟨sourceCell, sourceFound, _⟩ := literal_stack safety
  have sourceLocated := native _ sourceCell (origin.memory _ _ (established.item.memory _ _ sourceFound))
    (parent_input safety).2.1 (parent_input safety).2.2
  have sourceClean : cleaned.world.memory.memory.heap.lookup rootSource.allocation = some sourceCell :=
    (released.frame rootSource.allocation (held.2.2 (by decide))).2.trans
      (by rw [publishedSame]; exact sourceLocated)
  have sourceInner := (Compiler.ZigAir.Memory.cleanup_lookup_older cleaned.world.memory.memory
    ((parent safety).before.memory.memory.nextId + 1) rootSource.allocation (by rw [parent_mark]; decide)).trans sourceClean
  have sourceOuter := (Compiler.ZigAir.Memory.cleanup_lookup_older _ (parent safety).before.memory.memory.nextId rootSource.allocation
    (by rw [parent_mark]; decide)).trans sourceInner
  rw [result]
  refine ⟨rfl, finalFacts, ?_, ?_, Or.inr ⟨cleanDead.1, keepMissing _ cleanDead.2⟩, ?_, ?_, ?_⟩
  · change cleaned.world.memory.effects.keys (parent safety).key = none
    rw [keptKeys]; exact ownership.1
  · change cleaned.world.memory.effects.keys (child safety).key = _
    rw [keptKeys, keys, OwnedKeys.store, if_pos rfl]
  · exact (parent_literal safety).1.retire [0, 4] _ _ rootSource (by decide) _ innerFacts.valid.memory
      (sourceOuter.trans sourceFound.symm)
  · exact keepMissing _ ((released.frame ReachablePrefixTests.backing (by rw [(prefix_geometry safety).2]; decide)).2.trans
      (by rw [publishedSame]; exact nativeDead))
  · change cleaned.world.graph.read = _
    rw [post.graph, publishedSame]
    rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
