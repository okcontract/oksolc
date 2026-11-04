/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerNativeRoutingGrowthTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)

/-- Constructor return removes only child stack allocations. Registry-backed
rows, items and argument buffers persist; caller-owned container/input storage
predates the child mark. Rebuild all query facts from those native frames. -/
theorem GraphFacts.cleanup {safety : Bool} {backing capacity : Nat} {world : World (Publication.Effects Nat)}
    {rows : List Storage.Cell} (facts : GraphFacts safety backing capacity world rows) (mark : Nat)
    (ownerOlder : 6 < mark) (inputOlder : source.allocation < mark) (bounded : rows.length ≤ capacity) :
    GraphFacts safety backing capacity
      { world with memory := { world.memory with memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } } rows := by
  have retained := (facts.native bounded).cleanup mark ownerOlder
  obtain ⟨offset, registered, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := facts.owned
  have backingFrame := (persistent_cleanup world.memory.memory mark backing backingCell backingFound backingPersistent).trans backingFound.symm
  have descriptors := DescriptorRelation.frame _ _ backing rows facts.descriptors backingFrame
  obtain ⟨native, found, typed, represented⟩ := facts.nativeInput
  have inputFrame := Compiler.ZigAir.Memory.cleanup_lookup_older world.memory.memory mark source.allocation inputOlder
  exact ⟨retained.projected, retained.linked, retained.valid, retained.ownerLive,
    ⟨offset, registered, backingCell, backingFrame.trans backingFound, backingTyped, backingWritable, backingPersistent⟩,
    facts.vector, retained.header, descriptors, retained.resident, retained.items,
    ⟨native, inputFrame.trans found, typed, represented.frame inputFrame⟩,
    retained.live, retained.unique, retained.apart, retained.accepted, retained.data⟩

namespace RoutingTests
open CallerInputTests (values)

theorem native_insert (safety empty : Bool) (after : Frame Nat)
    (ran : execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : cell input (key empty) (normalized safety empty 4) (value safety empty) Storage.publishedOwnership after = row safety empty) :
    Native.insert ops allocate safety 7 6 (parent empty) source Insertion.Tests.model input (key empty)
      (normalized safety empty 4) true (some growth) (taken safety empty 4).2.world =
      (.ok 5, projected safety empty after) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have incoming := entry safety empty
  obtain ⟨owner, found, _, _⟩ := prior.facts.owner
  have checked := incoming.checked_execution ops allocate safety 7 6 (parent empty) source Insertion.Tests.model
    (request empty) (values empty) input (key empty) (normalized safety empty 4) (lookup empty)
    (before safety empty 4) (taken safety empty 4).2 true (cells safety empty 4) (some growth) owner ⟨lifetime empty, 0⟩
    found (readHeader_items _ _ _ _ prior.facts.header)
  change checkedExecution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = .ok (execute safety empty) at checked
  rw [ran] at checked
  have rows : (taken safety empty 4).2.world.graph.representatives = some (cells safety empty 4) := by
    rw [incoming.origin.graph]; exact prior.facts.projected
  simp only [value] at candidate
  simp only [Native.insert, rows, body, checked, candidate, Interner.insertionOutcome, Except.mapError, Storage.idFor, prior.count]
  rfl

def returned (safety empty : Bool) (after : Frame Nat) :=
  { projected safety empty after with memory := { (projected safety empty after).memory with
    memory := Compiler.ZigAir.Memory.cleanup (before safety empty 4).memory.memory.nextId (memory after).memory } }

/-- Full source caller, with capacity/classification/cache decisions, actual
dispatcher, checked native growth, outer defers and child-frame return. The
arbitrary recursive callback is unused because the dispatcher proves no match. -/
theorem full_result (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) (after : Frame Nat)
    (ran : execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after))
    (candidate : cell input (key empty) (normalized safety empty 4) (value safety empty) Storage.publishedOwnership after = row safety empty) :
    full safety empty find = (.ok 5, ⟨returned safety empty after, ⟨none, some (normalized safety empty 4), true⟩⟩) := by
  have incoming := entry safety empty
  have calls := prefix_results safety empty 4 (by decide)
  have routed := incoming.find_after_simplify ops allocate safety 160 7 6 (parent empty) source Insertion.Tests.model input
    (seed empty find) Interner.Queries.queries (request empty) (before safety empty 4) (taken safety empty 4).2.world
    (stack safety empty 4) _ (values empty) (prepared safety empty 4).2 (taken safety empty 4).2 (key empty)
    (normalized safety empty 4) (lookup empty) (some growth) (room safety empty) calls.1 (Prod.ext calls.2.1 rfl)
    (classified empty) (made empty) (missed safety empty) (Prod.ext calls.2.2.1 rfl) rfl (simplified safety empty find)
  have completed := incoming.finish_native ops allocate safety 7 6 (parent empty) source Insertion.Tests.model
    (request empty) (values empty) input (key empty) (normalized safety empty 4) (lookup empty)
    (before safety empty 4) (taken safety empty 4).2 true (some growth)
  rw [native_insert safety empty after ran candidate] at completed
  change full safety empty find = _ at routed
  rw [completed] at routed
  exact routed

/-- The complete caller's result, reached graph, native queries, key owners,
parent borrow and allocation history are derived together from initialization
and the actual native insertion. No final graph or Good premise is accepted. -/
theorem full_contract (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) : ∃ after,
    full safety empty find = (.ok 5, ⟨returned safety empty after, ⟨none, some (normalized safety empty 4), true⟩⟩) ∧
    GraphFacts safety (grownLifetime empty) 13 (full safety empty find).2.world (cells safety empty 4 ++ [row safety empty]) ∧
    Good (parent empty) (values empty) (full safety empty find).2.world ∧
    Caller.Custody 7 (CallerInputTests.operands empty) (full safety empty find).2.world.memory ∧
    (full safety empty find).2.world.memory.effects.keys = OwnedKeys.store (before safety empty 4).memory.effects.keys (key empty)
      ⟨(normalized safety empty 4).address, 5⟩ ∧
    (full safety empty find).2.world.memory.heap (lifetime empty) = none ∧
    (full safety empty find).2.world.memory.memory.heap.lookup (lifetime empty) = none ∧
    (full safety empty find).2.world.memory.memory.nextId = grownLifetime empty + 1 := by
  obtain ⟨after, ran, candidate, facts, dead, nativeDead, nextId, keys, custody⟩ := native_contract safety empty
  have completed := full_result safety empty find after ran candidate
  have prior := initialized_prefix safety empty 4 (by decide)
  have history := congrArg Prod.fst (reached_observations safety empty 4 (by decide))
  change (before safety empty 4).memory.memory.nextId = startId empty 4 at history
  have closed := facts.cleanup (before safety empty 4).memory.memory.nextId
    (by rw [history]; cases empty <;> decide) (by rw [history]; cases empty <;> decide)
    (by simp only [List.length_append, List.length_singleton, prior.count]; decide)
  have parentHeld := (custody _ (CustodyTests.parent_custody safety empty)).1
  have returnedHeld : Caller.Custody 7 (CallerInputTests.operands empty) (returned safety empty after).memory :=
    ⟨parentHeld.live, parentHeld.apart⟩
  refine ⟨after, completed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [completed]; exact closed
  · rw [completed]
    exact returnedHeld.good closed.valid _
  · rw [completed]; exact returnedHeld
  · rw [completed]; exact keys
  · rw [completed]; exact dead
  · rw [completed]
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ (lifetime empty)
      (by rw [history]; cases empty <;> decide)).trans nativeDead
  · rw [completed]; exact nextId

end RoutingTests
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests
