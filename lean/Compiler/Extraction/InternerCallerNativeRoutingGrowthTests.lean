/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerNativeRoutingSetupTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RoutingTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input source)
open CallerInputTests (values)

def value (safety empty : Bool) := ((key empty).eval Insertion.Tests.model (taken safety empty 4).2.world.graph.read).getD 0
def row (safety empty : Bool) : Storage.Cell :=
  ⟨(copied safety empty 4).item, value safety empty, object safety empty 4, values empty, 0, (operands safety empty 4).address⟩
def execute (safety empty : Bool) := execution ops allocate safety 7 6 (parent empty) source Insertion.Tests.model input
  (key empty) (normalized safety empty 4) true (cells safety empty 4) (taken safety empty 4).2.world (some growth)
def projected (safety empty : Bool) (after : Frame Nat) := Insertion.projected (cells safety empty 4)
  (taken safety empty 4).2.world (key empty) (row safety empty) Storage.publishedOwnership after

/-- Derive the cache-miss insertion's reached graph and parent custody from the
same generic native preparation/growth/publication theorem. This uses the new
key's actual caller entry, not the earlier repeated-key insertion result. -/
theorem native_contract (safety empty : Bool) : ∃ after,
    execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after) ∧
    cell input (key empty) (normalized safety empty 4) (value safety empty) Storage.publishedOwnership after = row safety empty ∧
    GraphFacts safety (grownLifetime empty) 13 (projected safety empty after) (cells safety empty 4 ++ [row safety empty]) ∧
    (memory after).heap (lifetime empty) = none ∧ (memory after).memory.heap.lookup (lifetime empty) = none ∧
    (memory after).memory.nextId = grownLifetime empty + 1 ∧
    (memory after).effects.keys = OwnedKeys.store (before safety empty 4).memory.effects.keys (key empty)
      ⟨(normalized safety empty 4).address, 5⟩ ∧
    (∀ parent, Caller.Custody 7 parent (before safety empty 4).memory →
      Caller.Custody 7 parent (memory after) ∧ Good (view parent) parent.items (projected safety empty after)) := by
  have prior := initialized_prefix safety empty 4 (by decide)
  have incoming := entry safety empty
  have observations := preparation_results safety empty 4 (by decide)
  obtain ⟨owner, found, typed, writable⟩ := prior.facts.owner
  let probeEffects := (memory (append safety allocate 7 6 (cells safety empty 4) input (key empty) (normalized safety empty 4)
    (value safety empty) preparationOwnership (preparedFrame (object safety empty 4) (copied safety empty 4)
      (operands safety empty 4) (ready safety empty 4)) (some growth)).2).effects.allocator * 10 + 8
  have result := incoming.growing_success ops allocate releaseBacking safety 7 6 (lifetime empty) 5 13 (object safety empty 4) 8192 17 23 owner
    (parent empty) source Insertion.Tests.model (request empty) (values empty) input (copied safety empty 4) (key empty)
    (normalized safety empty 4) (operands safety empty 4) (lookup empty) (handle safety empty 4) (before safety empty 4) (taken safety empty 4).2
    (cells safety empty 4) (duplicated safety empty 4).2 (CallerGrowingChainTests.made safety empty 4).2 (cloned safety empty 4).2
    (Normalization.Tests.external_admitted _) found typed writable prior.facts.owned (readHeader_items _ _ _ _ prior.facts.header)
    prior.facts.capacity_read prior.facts.vector prior.facts.descriptors prior.facts.resident prior.facts.apart prior.facts.items
    (by decide) (by decide) (by rw [prior.count]; decide) (by rw [prior.count]; decide) (by decide) (by rw [prior.count]; decide)
    observations.1 observations.2.1 observations.2.2 ((ready safety empty 4).effects.allocator * 10 + 7) (by
      intro installed assigned
      have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      exact ⟨rfl, backing_fits safety empty⟩)
    probeEffects (by
      intro installed assigned
      have same : ready safety empty 4 = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      rfl) (CallerGrowingChainTests.growth_entry_unlocked safety empty)
  obtain ⟨_, _, after, finalOwner, _, _, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header,
      descriptors, resident, _, _, _, _, _, live, unique, apart, accepted, table, _,
      nextId, _, oldDead, nativeDead, _, frame, _, items, custody, _, _, candidate⟩ := result
  have fresh := (Prod.mk.inj (prepared_geometry safety empty)).1
  refine ⟨after, ran, candidate, ?_, oldDead, nativeDead, by rw [nextId, fresh], ?_, ?_⟩
  · obtain ⟨native, located, inputTyped, inputReads⟩ := prior.facts.nativeInput
    have inputFrame := frame source.allocation native located (by decide)
      (by cases empty <;> decide) (prior.facts.input_apart (key empty))
    rw [fresh] at vector owned header descriptors
    refine ⟨rfl, ?_, valid, ⟨finalOwner, ownerFound, ownerTyped, ownerWritable⟩, owned, vector, ?_,
      descriptors, resident, items, ⟨native, inputFrame, inputTyped, inputReads.frame (inputFrame.trans located.symm)⟩,
      live, unique, apart, accepted, ?_⟩
    · change Cache.put equalityFields (taken safety empty 4).2.world.graph.table (key empty) (Storage.idFor (cells safety empty 4)) =
        OwnedKeys.view (memory after).effects.keys
      rw [table, OwnedKeys.view_store, incoming.origin.graph, prior.facts.linked]
      rfl
    · simpa only [List.length_append, List.length_singleton] using header
    · intro logical member
      rcases List.mem_append.mp member with old | added
      · exact prior.facts.data_after (key empty) (memory after).memory frame logical old
      · have sameRow := List.mem_singleton.mp added
        subst logical
        exact Constant.Data.nonpush (memory after).memory (row safety empty)
          (by change (1#32) ≠ 2#32; decide)
  · simpa only [prior.count] using table
  · intro parent held
    exact ⟨(custody parent held).1, (custody parent held).2 _⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CallerGrowingChainTests.RoutingTests
