/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapSearchMemory
import Compiler.Extraction.ExpressionMapProbeTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapSearchTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap.Buckets ExpressionMap
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)
open MapTableTests (firstKey secondKey empty_custody)
open MapProbeTests (collision second)

def thirdKey : Key := ⟨0, 2, 0, [], 0⟩

theorem third_probe (safety : Bool) :
    Search.insertionAfterHash .localMap safety (second safety).memory.memory 4 (collision thirdKey) thirdKey (view ⟨0, []⟩) =
      .ok (.miss 1 8) := by cases safety <;> decide +kernel

/-- The existing twice-populated owner fixture feeds the receiver-based producer.
This adds no prepared bucket or capacity to the runtime call. Its maintained
invariant then supplies the receiver-based reads of all three keys. -/
theorem publication_and_lookup (safety : Bool) (meaning : Meaning) :
    ∃ after,
      publishFromReceiver .localMap safety 4 1 8 (collision thirdKey) thirdKey ⟨0, []⟩ 71 (second safety) = (.ok (), after) ∧
      Facts safety 7 3 sentinel 0 after [] ∧
      Search.withHash .localMap safety after.memory.memory 4 collision firstKey (view ⟨0, []⟩) = .ok (some 37) ∧
      Search.withHash .localMap safety after.memory.memory 4 collision secondKey (view ⟨0, []⟩) = .ok (some 53) ∧
      Search.withHash .localMap safety after.memory.memory 4 collision thirdKey (view ⟨0, []⟩) = .ok (some 71) := by
  obtain ⟨facts, inv, firstRead, secondRead⟩ := MapProbeTests.repeated_from_initialized_owner safety meaning
  obtain ⟨outcome, probed, post⟩ := facts.probe_receiver_then_publish collision .localMap 4 5 8 4
    (by intro impossible; cases impossible) inv (by decide) thirdKey ⟨0, []⟩ 71 rfl (empty_custody _)
  have selected : outcome = .miss 1 8 := Except.ok.inj (probed.symm.trans (third_probe safety))
  subst outcome
  obtain ⟨after, published, afterFacts, afterInv, keys, _⟩ := post
  refine ⟨after, published, afterFacts, ?_, ?_, ?_⟩
  · rw [afterFacts.lookup_from_receiver collision .localMap 4 5 8 3 afterInv firstKey ⟨0, []⟩ rfl (empty_custody _), keys]
    simp only [OwnedKeys.store, show firstKey ≠ thirdKey by decide, ↓reduceIte]
    exact (facts.lookup_hashed collision .localMap 4 5 8 4 inv firstKey ⟨0, []⟩ rfl (empty_custody _)).symm.trans firstRead
  · rw [afterFacts.lookup_from_receiver collision .localMap 4 5 8 3 afterInv secondKey ⟨0, []⟩ rfl (empty_custody _), keys]
    simp only [OwnedKeys.store, show secondKey ≠ thirdKey by decide, ↓reduceIte]
    exact (facts.lookup_hashed collision .localMap 4 5 8 4 inv secondKey ⟨0, []⟩ rfl (empty_custody _)).symm.trans secondRead
  · rw [afterFacts.lookup_from_receiver collision .localMap 4 5 8 3 afterInv thirdKey ⟨0, []⟩ rfl (empty_custody _), keys]
    simp [OwnedKeys.store]

/-- Neither an allocated bucket nor a usable argument pointer is required on
getIndex's zero-count branch. The hash function remains arbitrary. -/
theorem empty_owner (safety : Bool) (hashes : Key → BitVec 64) (key : Key) (source : View) :
    Search.withHash .embedded safety (owned safety).memory.memory 3 hashes key source = .ok none := by
  have zero : Search.readCount .embedded safety (owned safety).memory.memory 3 = .ok 0 := by cases safety <;> decide +kernel
  simp only [Search.withHash, zero, bind, Except.bind, ↓reduceIte]

theorem empty_after_hash_rejected (safety : Bool) :
    Search.lookupAfterHash .embedded safety (owned safety).memory.memory 3 0 firstKey ⟨999, 0, 1⟩ =
      .error (Capacity.rejected safety) := by cases safety <;> decide +kernel

def missingCapacity : Compiler.ZigAir.Memory.State :=
  { MapNewTests.initialized with heap := MapNewTests.initialized.heap.map fun (id, cell) =>
      if id = 1 then (id, { cell with cells := cell.cells.filter fun pair => pair.1 != 16 }) else (id, cell) }

theorem empty_skips_missing_header :
    Search.withHash .localMap true missingCapacity 2 collision firstKey ⟨999, 0, 1⟩ = .ok none := by decide +kernel

theorem missing_header_rejected :
    Search.lookupAfterHash .localMap true missingCapacity 2 (collision firstKey) firstKey ⟨0, 0, 0⟩ =
      .error .uninitialized := by decide +kernel

theorem missing_header_publication_retains_world (world : World (Publication.Effects σ))
    (memory : world.memory.memory = missingCapacity) :
    publishFromReceiver .localMap true 2 0 8 (collision firstKey) firstKey ⟨0, []⟩ 37 world = (.error .uninitialized, world) := by
  apply publish_from_receiver_rejected
  rw [memory]
  decide +kernel

def missingCount : Compiler.ZigAir.Memory.State :=
  { MapNewTests.initialized with heap := MapNewTests.initialized.heap.map fun (id, cell) =>
      if id = 2 then (id, { cell with cells := cell.cells.filter fun pair => pair.1 != sizeOffset true }) else (id, cell) }

theorem missing_count_rejected :
    Search.withHash .localMap true missingCount 2 collision firstKey ⟨0, 0, 0⟩ = .error .uninitialized := by decide +kernel

theorem receiver_placement_rejected :
    Search.withHash .embedded true MapNewTests.initialized 2 collision firstKey ⟨0, 0, 0⟩ ≠ .ok none := by decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapSearchTests
