/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbeInvariant
import Compiler.Extraction.ExpressionMapCandidateMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap

/-- Complete post-hash lookup consumes original graph/caller admission. The
logical hash function is universally quantified, with no collision assumption;
connecting native Wyhash remains an explicit caller obligation. -/
theorem Facts.lookup_hashed {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (hashes : Key → BitVec 64) (place : Initialization.Placement) (receiver bucket : Nat)
    (bucketCapacity available : BitVec 32)
    (inv : Probe.Invariant hashes place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    Probe.getHashed before.memory.memory bucketCapacity bucket (hashes key) key (view owned) =
      .ok ((before.memory.effects.keys key).map OwnedKeys.Entry.id) := by
  obtain ⟨contents, bounded⟩ := facts.query_view key owned aligned custody
  exact Probe.get_hashed_verified _ _ _ _ _ _ _ inv.binding inv.power inv.routing contents bounded

/-- The actual complete scan selects the branch. On a miss it derives absence,
vacancy, bounds and the fingerprint, immediately consumes native publication,
and maintains the same invariant for the next call. On a hit it exposes the
existing entry; replacement/retirement is deliberately a separate obligation. -/
theorem Facts.probe_then_publish {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (hashes : Key → BitVec 64) (place : Initialization.Placement) (receiver bucket : Nat)
    (bucketCapacity available : BitVec 32) (embedded : place = .embedded → receiver = owner)
    (inv : Probe.Invariant hashes place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (room : 0 < available.toNat) (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (aligned : key.arguments = owned.items) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    ∃ outcome, Probe.run before.memory.memory bucketCapacity bucket (hashes key) key (view owned) = .ok outcome ∧
      match outcome with
      | .hit index => index < bucketCapacity.toNat ∧ ∃ entry, before.memory.effects.keys key = some entry ∧
          Table.EntryView bucketCapacity bucket index before.memory.memory key entry
      | .miss index first => ∃ after,
          publishSelectedNew place safety receiver bucketCapacity bucket (Probe.select bucketCapacity index first)
            (Probe.fingerprint (hashes key)) key owned id before = (.ok (), after) ∧
          Facts safety allocator owner data capacity after rows ∧
          Probe.Invariant hashes place safety receiver bucket bucketCapacity (available - 1#32) after.memory.memory after.memory.effects.keys ∧
          after.memory.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ ∧
          after.memory.effects.allocator = before.memory.effects.allocator := by
  obtain ⟨contents, bounded⟩ := facts.query_view key owned aligned custody
  obtain ⟨outcome, ran, completed⟩ := Probe.run_verified _ _ _ _ _ _ _ inv.binding inv.power contents bounded
  refine ⟨outcome, ran, ?_⟩
  cases outcome with
  | hit index => exact ⟨completed.1, completed.2.2⟩
  | miss index first =>
    have absent := completed.absent inv.routing
    obtain ⟨inside, vacant, route⟩ := completed.vacancy inv.power inv.canonical (inv.room room)
    obtain ⟨after, published, afterFacts, _, keys, effects, post⟩ := facts.publish_selected_new place receiver bucketCapacity bucket
      (Probe.select bucketCapacity index first) embedded inv.binding (Probe.fingerprint (hashes key)) available inside inv.availableRead room
      vacant key owned id aligned absent custody
    have found : after.memory.effects.keys key = some ⟨owned.address, id⟩ := by rw [keys]; simp [OwnedKeys.store]
    have entry := Table.EntryView.of_live afterFacts.valid (afterFacts.live key _ found) post.stored
    refine ⟨after, published, afterFacts, ?_, keys, effects⟩
    rw [keys]
    exact inv.published key ⟨owned.address, id⟩ post inside vacant absent route entry

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
