/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItemGrowthTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (parent cells startId lifetime ops growth grownLifetime GraphFacts)
open CallerInputTests (values)

abbrev seed := CallerGrowingChainTests.RoutingTests.seed
def primitives (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat))
    (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops reserve safety 7 6 (parent empty) address Insertion.Tests.model input (seed empty find) (some growth)
def callee (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :=
  ConstructorFrame.find (Publication.external ops.arguments) 160 7 (primitives safety empty find (itemSource empty) (native empty))
    Interner.Queries.queries (parent empty) (request empty) (constructed safety empty)
def full (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :=
  operation (Publication.external ops.arguments) 160 7 (primitives safety empty find) Interner.Queries.queries
    (parent empty) 254 (values empty) debug (before safety empty)

theorem simplified (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :
    (seed empty find).simplify (key empty) (normalized empty) (taken safety empty).2.world =
      (.ok none, (taken safety empty).2.world) := by
  have constant := CallerGrowingChainTests.RoutingTests.first_nonconstant safety empty
  rw [(CallerGrowingChainTests.RoutingTests.entry safety empty).origin.graph] at constant
  have first : (Interner.representativeReads (taken safety empty).2.world.graph).constant 0 = .ok none := by
    rw [(entry safety empty).origin.graph, (construction safety empty).graph]
    exact constant
  change Dispatch.simplify (Interner.representativeReads (taken safety empty).2.world.graph)
    (Recursive.constructors find) 64 254 (values empty) () (taken safety empty).2.world = _
  generalize (taken safety empty).2.world = world at first ⊢
  generalize Interner.representativeReads world.graph = reads at first ⊢
  cases empty with
  | true => rfl
  | false =>
    have collected : Dispatch.collectConstants reads [0] = .ok none := by
      unfold Dispatch.collectConstants; rw [first]; rfl
    change Dispatch.simplify reads (Recursive.constructors find) 64 254 [0] () world = _
    simp only [Dispatch.simplify, Dispatch.simplifyWithInputs, Dispatch.simplifyOptionsWithInputs, Dispatch.constantStage,
      List.length_cons, List.length_nil, List.isEmpty_cons, Nat.reduceAdd, Bool.false_eq_true,
      collected, Nested.readAction, Dispatch.orNext]
    rfl

theorem native_insert (safety empty : Bool) (after : Native.Frame Nat)
    (ran : execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : cell (native empty) (key empty) (normalized empty) (value safety empty) Storage.publishedOwnership after = row safety empty) :
    Native.insert ops reserve safety 7 6 (parent empty) (itemSource empty) Insertion.Tests.model (native empty) (key empty)
      (normalized empty) true (some growth) (taken safety empty).2.world = (.ok 5, projected safety empty after) := by
  have facts := constructed_graph safety empty
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have incoming := entry safety empty
  obtain ⟨owner, found, _, _⟩ := facts.owner
  have checked := incoming.checked_execution ops reserve safety 7 6 (parent empty) (itemSource empty) Insertion.Tests.model
    (request empty) (values empty) (native empty) (key empty) (normalized empty) (lookup empty)
    (constructed safety empty) (taken safety empty).2 true (cells safety empty 4) (some growth) owner ⟨lifetime empty, 0⟩
    found (readHeader_items _ _ _ _ facts.header)
  change checkedExecution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = .ok (execute safety empty) at checked
  rw [ran] at checked
  have rows : (taken safety empty).2.world.graph.representatives = some (cells safety empty 4) := by
    rw [incoming.origin.graph]; exact facts.projected
  simp only [value] at candidate
  simp only [Native.insert, rows, Native.body, checked, candidate, Interner.insertionOutcome, Except.mapError, Storage.idFor, prior.count]
  rfl

def childReturned (safety empty : Bool) (after : Native.Frame Nat) :=
  { projected safety empty after with memory := { (projected safety empty after).memory with
    memory := Compiler.ZigAir.Memory.cleanup (constructed safety empty).memory.memory.nextId (memory after).memory } }
def returned (safety empty : Bool) (after : Native.Frame Nat) :=
  { childReturned safety empty after with memory := { (childReturned safety empty after).memory with
    memory := Compiler.ZigAir.Memory.cleanup (before safety empty).memory.memory.nextId (childReturned safety empty after).memory.memory } }

theorem callee_result (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) (after : Native.Frame Nat)
    (ran : execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : cell (native empty) (key empty) (normalized empty) (value safety empty) Storage.publishedOwnership after = row safety empty) :
    callee safety empty find = (.ok 5, ⟨childReturned safety empty after, ⟨none, some (normalized empty), true⟩⟩) := by
  have incoming := entry safety empty
  have calls := prefix_results safety empty
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have facts := constructed_graph safety empty
  have room : Interner.Queries.queries.atCapacity (constructed safety empty).graph = false := by
    rw [Interner.Queries.capacity_exact _ _ facts.projected, prior.count]; decide
  have initialized : Caller.initLookup (Publication.external ops.arguments) 160 7 (parent empty)
      ⟨(constructed safety empty).memory.memory.nextId, 0, 2⟩ (request empty)
      ⟨{ constructed safety empty with memory := { (constructed safety empty).memory with memory := stack safety empty } }, { lookup := none }⟩ =
        (.ok (values empty), (prepared safety empty).2) := by
    rw [calls.2.1]; exact Prod.ext calls.2.2.2.1 rfl
  have routed := incoming.find_after_simplify ops reserve safety 160 7 6 (parent empty) (itemSource empty) Insertion.Tests.model (native empty)
    (seed empty find) Interner.Queries.queries (request empty) (constructed safety empty) (taken safety empty).2.world
    (stack safety empty) _ (values empty) (prepared safety empty).2 (taken safety empty).2 (key empty) (normalized empty) (lookup empty)
    (some growth) room calls.2.2.1 initialized rfl (made_key empty)
    (by rw [(construction safety empty).graph]; exact calls.2.2.2.2.2.2)
    (Prod.ext calls.2.2.2.2.1 rfl) rfl (simplified safety empty find)
  have completed := incoming.finish_native ops reserve safety 7 6 (parent empty) (itemSource empty) Insertion.Tests.model
    (request empty) (values empty) (native empty) (key empty) (normalized empty) (lookup empty)
    (constructed safety empty) (taken safety empty).2 true (some growth)
  rw [native_insert safety empty after ran candidate] at completed
  change callee safety empty find = _ at routed
  rw [completed] at routed
  exact routed

theorem full_result (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) (after : Native.Frame Nat)
    (ran : execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : cell (native empty) (key empty) (normalized empty) (value safety empty) Storage.publishedOwnership after = row safety empty) :
    full safety empty find = (.ok 5, ⟨returned safety empty after, ⟨none, some (normalized empty), true⟩⟩) := by
  have routed := invoke_prepared (Publication.external ops.arguments) 160 7 (primitives safety empty find) Interner.Queries.queries
    (parent empty) (request empty) debug (before safety empty) (constructed safety empty) (itemSource empty) (prefix_results safety empty).1
  change full safety empty find = _ at routed
  have called := callee_result safety empty find after ran candidate
  simp only [callee, native] at called
  rw [called] at routed
  exact routed

/-- The actual constructor local, caller, native growth and both returns derive
the result and reached graph together. Complete clone fields persist; the local
source item is retired, private parent arguments survive, and history advances.
The dispatcher makes no recursive callback in this fixture. -/
theorem full_contract (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) : ∃ after,
    full safety empty find = (.ok 5, ⟨returned safety empty after, ⟨none, some (normalized empty), true⟩⟩) ∧
    GraphFacts safety (grownLifetime empty) 13 (full safety empty find).2.world (cells safety empty 4 ++ [row safety empty]) ∧
    Good (parent empty) (values empty) (full safety empty find).2.world ∧
    Caller.Custody 7 (CallerInputTests.operands empty) (full safety empty find).2.world.memory ∧
    AssemblyItem.Owned 7 (object empty) (full safety empty find).2.world.memory ∧
    AssemblyClone.NativeFields.Represents (full safety empty find).2.world.memory.memory ⟨object empty, 0⟩ (native empty) ∧
    (full safety empty find).2.world.memory.memory.heap.lookup (itemSource empty).allocation = none ∧
    (full safety empty find).2.world.memory.effects.keys = OwnedKeys.store (before safety empty).memory.effects.keys (key empty)
      ⟨(normalized empty).address, 5⟩ ∧
    (full safety empty find).2.world.memory.heap (lifetime empty) = none ∧
    (full safety empty find).2.world.memory.memory.heap.lookup (lifetime empty) = none ∧
    (full safety empty find).2.world.memory.memory.nextId = grownLifetime empty + 1 := by
  obtain ⟨after, ran, candidate, facts, dead, nativeDead, nextId, keys, owned, cloneReads, custody, itemFrame⟩ := native_contract safety empty
  have completed := full_result safety empty find after ran candidate
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have post := construction safety empty
  have calls := prefix_results safety empty
  have oldMark := congrArg Prod.fst (CallerGrowingChainTests.reached_observations safety empty 4 (by decide))
  change (before safety empty).memory.memory.nextId = startId empty 4 at oldMark
  have bounded : (cells safety empty 4 ++ [row safety empty]).length ≤ 13 := by
    simp only [List.length_append, List.length_singleton, prior.count]; decide
  have childClosed := facts.cleanup (constructed safety empty).memory.memory.nextId
    (by rw [calls.2.1]; cases empty <;> decide) (by rw [calls.2.1]; cases empty <;> decide) bounded
  have closed := childClosed.cleanup (before safety empty).memory.memory.nextId
    (by rw [oldMark]; cases empty <;> decide) (by rw [oldMark]; cases empty <;> decide) bounded
  have originalHeld := CallerGrowingChainTests.CustodyTests.parent_custody safety empty
  have constructedHeld : Caller.Custody 7 (CallerInputTests.operands empty) (constructed safety empty).memory := by
    constructor
    · rw [post.heap]; exact originalHeld.live
    · rw [post.effects]; exact originalHeld.apart
  have held := (custody _ constructedHeld).1
  have returnedHeld : Caller.Custody 7 (CallerInputTests.operands empty) (returned safety empty after).memory :=
    ⟨held.live, held.apart⟩
  obtain ⟨registered, cloneCell, cloneFound, cloneType, cloneWritable, clonePersistent⟩ := owned
  have childClone := persistent_cleanup (memory after).memory (constructed safety empty).memory.memory.nextId
    (object empty) cloneCell cloneFound clonePersistent
  have finalClone := persistent_cleanup (childReturned safety empty after).memory.memory (before safety empty).memory.memory.nextId
    (object empty) cloneCell childClone clonePersistent
  have finalReads : AssemblyClone.NativeFields.Represents (returned safety empty after).memory.memory ⟨object empty, 0⟩ (native empty) :=
    cloneReads.frame (finalClone.trans cloneFound.symm)
  obtain ⟨itemCell, itemFound, itemStack⟩ := post.stack
  have sourceId : (itemSource empty).allocation = (before safety empty).memory.memory.nextId := oldMark.symm
  have nativeItem := itemFrame itemCell (by rw [sourceId]; exact itemFound)
  have childItem := (Compiler.ZigAir.Memory.cleanup_lookup_older (memory after).memory
    (constructed safety empty).memory.memory.nextId (itemSource empty).allocation
    (by rw [sourceId, oldMark, calls.2.1]; omega)).trans nativeItem
  have retired := Compiler.ZigAir.Memory.cleanup_lookup_stack (childReturned safety empty after).memory.memory
    (before safety empty).memory.memory.nextId (itemSource empty).allocation itemCell childClosed.valid.memory childItem itemStack
    (by rw [sourceId]; exact Nat.le_refl _)
  refine ⟨after, completed, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [completed]; exact closed
  · rw [completed]; exact returnedHeld.good closed.valid _
  · rw [completed]; exact returnedHeld
  · rw [completed]; exact ⟨registered, cloneCell, finalClone, cloneType, cloneWritable, clonePersistent⟩
  · rw [completed]; exact finalReads
  · rw [completed]; exact retired
  · rw [completed]; exact keys
  · rw [completed]; exact dead
  · rw [completed]
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ (lifetime empty)
      (by rw [oldMark]; cases empty <;> decide)).trans
      ((Compiler.ZigAir.Memory.cleanup_lookup_older _ _ (lifetime empty)
        (by rw [calls.2.1]; cases empty <;> decide)).trans nativeDead)
  · rw [completed]; exact nextId

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
