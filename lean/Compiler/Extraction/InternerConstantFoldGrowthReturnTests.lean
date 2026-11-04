/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantFoldGrowthAllocationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)
open ConstantFoldTests

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

def childPrimitives (safety : Bool) := ConstantPublicationTests.primitives ReachablePrefixTests.allocate (some growth) safety
def fullChild (safety : Bool) (value : Word) := (child safety value).invoked (childPrimitives safety)
def returnedChild (safety : Bool) (value : Word) (after : Native.Frame Nat) :=
  (child safety value).returnedWorld (appended safety value after)

theorem source_private (safety : Bool) (value : Word) :
    Caller.SourcePrivate (rootSource safety value) (parent safety value).taken.2.world.memory.effects.keys ∧
    (rootSource safety value).allocation ≠ 6 ∧
    (rootSource safety value).allocation ≠ ReachablePrefixTests.backing := by
  have literal := (ConstantFoldTests.literal safety value).2.1
  have initial := (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.1
  have current := established safety value
  have privateSource : Caller.SourcePrivate (rootSource safety value) (parent safety value).taken.2.world.memory.effects.keys := by
    rw [current.entry.keys, current.item.effects, literal.effects]
    exact fun key => literal.key_apart [4] _ _ (rootSource safety value) initial.valid 7 key initial.live
  obtain ⟨owner, ownerFound, _⟩ := initial.owner
  obtain ⟨_, _, array, arrayFound, _⟩ := initial.owned
  exact ⟨privateSource,
    literal.native_apart [4] _ _ (rootSource safety value) initial.valid 6 owner ownerFound (by change (1 : Nat) ≠ 0; decide),
    literal.native_apart [4] _ _ (rootSource safety value) initial.valid ReachablePrefixTests.backing array arrayFound (by change (1 : Nat) ≠ 0; decide)⟩

theorem child_contract (safety : Bool) (value : Word) : ∃ after,
    ((fullChild safety value).1, (fullChild safety value).2.world) = (.ok 5, returnedChild safety value after) ∧
    GraphFacts safety (backing safety value) 13 (returnedChild safety value after) (rows safety value) ∧
    AssemblyClone.NativeFields.Represents (returnedChild safety value after).memory.memory
      ⟨childObject safety value, 0⟩ (child safety value).native ∧
    (returnedChild safety value after).memory.effects.keys = OwnedKeys.store (child safety value).before.memory.effects.keys
      (child safety value).key ⟨(child safety value).normalized.address, 5⟩ ∧
    (∀ id native, (child safety value).before.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety value after).memory.memory.heap.lookup id = some native) ∧
    (∀ id block, (child safety value).before.memory.heap id = some block → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety value after).memory.heap id = some block) ∧
    (returnedChild safety value after).memory.heap ReachablePrefixTests.backing = none ∧
    (returnedChild safety value after).memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    Held 7 (rootSource safety value) [4] (parent safety value).normalized (returnedChild safety value after) ∧
    Caller.GraphCustody 7 (parent safety value).normalized (rows safety value) (returnedChild safety value after).memory ∧
    Caller.SourcePrivate (rootSource safety value) (returnedChild safety value after).memory.effects.keys := by
  obtain ⟨after, inserted, facts, oldDead, nativeDead, keys, frame, registry, custody, privateSource, itemReads⟩ := child_native safety value
  have current := child_established safety value
  have prior := (established safety value).taken
  have room : Interner.Queries.queries.atCapacity (child safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, ConstantPublicationTests.rows_count]; decide
  have routed := (child safety value).route (childPrimitives safety) (child_observed safety value) current.item.graph room rfl
  change (child safety value).invoked (childPrimitives safety) =
    (let done := finishInsertion ops ReachablePrefixTests.allocate safety 7 6 (child safety value).source
      (child safety value).address Insertion.Tests.model (child safety value).native (child safety value).key true
      (child safety value).taken.2 (some growth)
     if ordinary done.1 then (done.1, (child safety value).returned done.2) else done) at routed
  obtain ⟨owner, found, _⟩ := prior.owner
  have sameInsert : Native.insert ops ReachablePrefixTests.allocate safety 7 6 (child safety value).source (child safety value).address
      Insertion.Tests.model (child safety value).native (child safety value).key (child safety value).normalized true
      (some growth) (child safety value).taken.2.world =
      (.ok (Storage.idFor (ConstantPublicationTests.rows safety value)), appended safety value after) := by
    simpa only [Storage.idFor, ConstantPublicationTests.rows_count] using inserted
  have complete := (child safety value).publication_return ReachablePrefixTests.allocate (some growth) safety
    (backing safety value) 13 (childObject safety value) ReachablePrefixTests.backing (ConstantPublicationTests.rows safety value)
    (child safety value).normalized (childPrimitives safety) after current.entry sameInsert facts itemReads prior.valid
    (fun id native found ownerApart backingApart _ => frame id native (current.item.memory id native found) ownerApart backingApart)
    (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1
    (by simp only [List.length_append, List.length_singleton, ConstantPublicationTests.rows_count]; decide) routed
  have finished := current.entry.finish_native ops ReachablePrefixTests.allocate safety 7 6
    (child safety value).source (child safety value).address Insertion.Tests.model (child safety value).request
    (child safety value).request.arguments (child safety value).native (child safety value).key (child safety value).normalized
    (child safety value).lookup (child safety value).constructed (child safety value).taken.2 true (some growth)
  rw [inserted] at finished
  rw [finished] at routed
  have result : ((fullChild safety value).1, (fullChild safety value).2.world) = (.ok 5, returnedChild safety value after) :=
    congrArg (fun ran => (ran.1, ran.2.world)) routed
  have reached : (fullChild safety value).2.world = returnedChild safety value after := congrArg Prod.snd result
  have named : (child safety value).invoked (childPrimitives safety) = fullChild safety value := rfl
  rw [named] at complete
  rw [reached] at complete
  have retained : ∀ id native, (child safety value).before.memory.memory.heap.lookup id = some native →
      id ≠ 6 → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety value after).memory.memory.heap.lookup id = some native := by
    intro id native found ownerApart backingApart
    exact complete.2.2.2.2 id native found ownerApart backingApart
      (by intro old _ nonempty; exact False.elim (nonempty rfl))
  have registered : ∀ id block, (child safety value).before.memory.heap id = some block → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety value after).memory.heap id = some block := by
    intro id block found apart
    exact registry id block (by rw [current.item.heap]; exact found) apart
  have parentCurrent := established safety value
  have held := parentCurrent.entry.origin.held
  obtain ⟨sourceCell, sourceFound⟩ := held.1.backed (by change (1 : Nat) ≠ 0; decide)
  have sourceFrame := (retained _ sourceCell sourceFound (source_private safety value).2.1
    (source_private safety value).2.2).trans sourceFound.symm
  refine ⟨after, result, complete.2.1, complete.2.2.1, ?_, retained, registered, oldDead, ?_, ?_, ?_, ?_⟩
  · change (memory after).effects.keys = _
    rw [keys, current.item.effects]
  · apply Call.cleanup_missing _ _ _ (facts.valid.cleanup _ ((child safety value).before.memory.memory.nextId + 1)).memory
    exact Call.cleanup_missing _ _ _ facts.valid.memory nativeDead
  · refine ⟨⟨complete.2.1.valid, represented_frame _ [4] held.1.2 sourceFrame⟩, ?_, held.2.2⟩
    rcases held.2.1 with empty | stored
    · exact Or.inl empty
    · obtain ⟨_, _, array, arrayFound, _⟩ := parentCurrent.constructed.owned
      exact Or.inr (registered _ _ stored (parentCurrent.entry.origin.freshNative _ array arrayFound))
  · have initial := parentCurrent.entry.graph_custody _ parentCurrent.constructed.resident
    have prepared : Caller.GraphCustody 7 (parent safety value).normalized (ConstantPublicationTests.rows safety value)
        (child safety value).constructed.memory := by
      refine ⟨⟨?_, ?_⟩, initial.operands⟩
      · rw [current.item.heap]; exact initial.live
      · rw [current.item.effects]; exact initial.apart
    have kept := custody _ prepared
    exact ⟨⟨kept.live, kept.apart⟩, kept.operands⟩
  · have good : Good (rootSource safety value) [4] (child safety value).constructed :=
      ⟨current.constructed.valid, represented_frame _ [4] held.1.2
        ((current.item.memory _ sourceCell sourceFound).trans sourceFound.symm)⟩
    apply privateSource _ [4] good
    rw [current.item.effects]
    exact (source_private safety value).1


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
