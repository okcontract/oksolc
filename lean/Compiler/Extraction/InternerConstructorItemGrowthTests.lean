/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItemPreparationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (parent cells startId lifetime ops growth grownLifetime releaseBacking GraphFacts)
open CallerInputTests (values)

theorem keys_absent (safety empty : Bool) : (constructed safety empty).memory.effects.keys (key empty) = none := by
  have facts := constructed_graph safety empty
  have absent := (prefix_results safety empty).2.2.2.2.2.2
  rw [← (construction safety empty).graph, facts.linked] at absent
  cases stored : (constructed safety empty).memory.effects.keys (key empty) with
  | none => rfl
  | some old => simp only [OwnedKeys.view, stored, Option.map_some] at absent; contradiction

/-- Native growth now clones the actual constructor-local item. The full graph
and private parent borrow are derived from insertion, while the still-live
constructor local is framed until its own return. -/
theorem native_contract (safety empty : Bool) : ∃ after,
    execute safety empty = ((.ok (some .success), Storage.publishedOwnership), after) ∧
    cell (native empty) (key empty) (normalized empty) (value safety empty) Storage.publishedOwnership after = row safety empty ∧
    GraphFacts safety (grownLifetime empty) 13 (projected safety empty after) (cells safety empty 4 ++ [row safety empty]) ∧
    (memory after).heap (lifetime empty) = none ∧ (memory after).memory.heap.lookup (lifetime empty) = none ∧
    (memory after).memory.nextId = grownLifetime empty + 1 ∧
    (memory after).effects.keys = OwnedKeys.store (before safety empty).memory.effects.keys (key empty) ⟨(normalized empty).address, 5⟩ ∧
    AssemblyItem.Owned 7 (object empty) (memory after) ∧
    AssemblyClone.NativeFields.Represents (memory after).memory ⟨object empty, 0⟩ (native empty) ∧
    (∀ parent, Caller.Custody 7 parent (constructed safety empty).memory →
      Caller.Custody 7 parent (memory after) ∧ Good (view parent) parent.items (projected safety empty after)) ∧
    (∀ itemCell, (constructed safety empty).memory.memory.heap.lookup (itemSource empty).allocation = some itemCell →
      (memory after).memory.heap.lookup (itemSource empty).allocation = some itemCell) := by
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have facts := constructed_graph safety empty
  have incoming := entry safety empty
  have calls := preparation_results safety empty
  obtain ⟨owner, found, typed, writable⟩ := facts.owner
  let probeEffects := (memory (append safety reserve 7 6 (cells safety empty 4) (native empty) (key empty) (normalized empty)
    (value safety empty) preparationOwnership (preparedFrame (object empty) (native empty)
      (operands empty) (ready safety empty)) (some growth)).2).effects.allocator * 10 + 8
  have result := incoming.growing_success ops reserve releaseBacking safety 7 6 (lifetime empty) 5 13 (object empty) 8192 17 23 owner
    (parent empty) (itemSource empty) Insertion.Tests.model (request empty) (values empty) (native empty) (native empty) (key empty)
    (normalized empty) (operands empty) (lookup empty) (handle empty) (constructed safety empty) (taken safety empty).2
    (cells safety empty 4) (duplicated safety empty).2 (created safety empty).2 (cloned safety empty).2
    (Normalization.Tests.external_admitted _) found typed writable facts.owned (readHeader_items _ _ _ _ facts.header)
    facts.capacity_read facts.vector facts.descriptors facts.resident facts.apart facts.items
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    (by decide) (by rw [prior.count]; decide) (by rw [prior.count]; decide) (by decide) (by rw [prior.count]; decide)
    calls.1 calls.2.1 calls.2.2.1 ((ready safety empty).effects.allocator * 10 + 7) (by
      intro installed assigned
      have same : ready safety empty = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      exact ⟨rfl, backing_fits safety empty⟩)
    probeEffects (by
      intro installed assigned
      have same : ready safety empty = installed := by simp only [ready, assigned, Except.toOption, Option.getD_some]
      rw [← same]
      rfl) (by cases safety <;> cases empty <;> insertion_kernel_rfl)
  obtain ⟨_, _, after, finalOwner, _, _, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header,
      descriptors, resident, objectOwned, cloneReads, _, _, _, live, unique, apart, accepted, table, _,
      nextId, _, oldDead, nativeDead, _, frame, _, items, custody, _, _, candidate⟩ := result
  have fresh := calls.2.2.2.1
  refine ⟨after, ran, candidate, ?_, oldDead, nativeDead, by rw [nextId, fresh], ?_, objectOwned, cloneReads, ?_, ?_⟩
  · obtain ⟨native, located, inputTyped, inputReads⟩ := facts.nativeInput
    have inputFrame := frame AssemblyItem.Creation.NativeFields.Tests.source.allocation native located (by decide)
      (by cases empty <;> decide) (facts.input_apart (key empty))
    rw [fresh] at vector owned header descriptors
    refine ⟨rfl, ?_, valid, ⟨finalOwner, ownerFound, ownerTyped, ownerWritable⟩, owned, vector, ?_,
      descriptors, resident, items, ⟨native, inputFrame, inputTyped, inputReads.frame (inputFrame.trans located.symm)⟩,
      live, unique, apart, accepted, ?_⟩
    · change Cache.put equalityFields (taken safety empty).2.world.graph.table (key empty) (Storage.idFor (cells safety empty 4)) =
        OwnedKeys.view (memory after).effects.keys
      rw [table, OwnedKeys.view_store, incoming.origin.graph, facts.linked]
      rfl
    · simpa only [List.length_append, List.length_singleton] using header
    · intro logical member
      rcases List.mem_append.mp member with old | added
      · exact facts.data_after (key empty) (memory after).memory frame logical old
      · have sameRow := List.mem_singleton.mp added
        subst logical
        exact Constant.Data.nonpush (memory after).memory (row safety empty)
          (by change (1#32) ≠ 2#32; decide)
  · simpa only [prior.count, (construction safety empty).effects] using table
  · intro parent held
    exact ⟨(custody parent held).1, (custody parent held).2 _⟩
  · intro itemCell located
    exact frame _ itemCell located (by cases empty <;> decide) (by cases empty <;> decide)
      (by intro old impossible; rw [keys_absent] at impossible; cases impossible)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
