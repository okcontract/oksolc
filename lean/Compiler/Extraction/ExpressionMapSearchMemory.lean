/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapSearchLoop

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap

/-- The source miss tail re-reads capacity for tombstone selection and metadata
for the selected pointer. A rejected read retains the original world; publication
rejections retain the reached prefix through the existing operation. -/
def publishFromReceiver (place : Initialization.Placement) (safety : Bool) (receiver index first : Nat)
    (hash : BitVec 64) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault Unit × World (Publication.Effects σ) :=
  match Capacity.readCapacity place safety before.memory.memory receiver with
  | .error fault => (.error fault, before)
  | .ok capacity => match Search.readBucket place safety before.memory.memory receiver with
    | .error fault => (.error fault, before)
    | .ok bucket => publishSelectedNew place safety receiver capacity bucket (Probe.select capacity index first)
        (Probe.fingerprint hash) key owned id before

theorem publish_from_receiver_rejected (place : Initialization.Placement) (safety : Bool) (receiver index first : Nat)
    (hash : BitVec 64) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Publication.Effects σ))
    (fault : Compiler.ZigAir.Memory.Fault)
    (rejected : Capacity.readCapacity place safety before.memory.memory receiver = .error fault) :
    publishFromReceiver place safety receiver index first hash key owned id before = (.error fault, before) := by
  simp only [publishFromReceiver, rejected]

theorem publish_from_receiver_eq
    (layout : Insertion.Layout place safety receiver bucket bucketCapacity before.memory.memory)
    (power : Probe.Power bucketCapacity) (index first : Nat) (hash : BitVec 64) (key : Key) (owned : ArgumentSlice) (id : NodeId) :
    publishFromReceiver place safety receiver index first hash key owned id before =
      publishSelectedNew place safety receiver bucketCapacity bucket (Probe.select bucketCapacity index first)
        (Probe.fingerprint hash) key owned id before := by
  simp only [publishFromReceiver, layout.read_capacity power.positive, layout.read_bucket]

theorem Facts.lookup_from_receiver {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (hashes : Key → BitVec 64) (place : Initialization.Placement) (receiver bucket : Nat)
    (bucketCapacity available : BitVec 32)
    (inv : Probe.Invariant hashes place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    Search.withHash place safety before.memory.memory receiver hashes key (view owned) =
      .ok ((before.memory.effects.keys key).map OwnedKeys.Entry.id) := by
  simp only [Search.withHash, inv.binding.read_count, bind, Except.bind]
  split
  · rename_i zero
    have bounded := Table.count_bound bucketCapacity bucket before.memory.memory
    have countZero : Table.count bucketCapacity bucket before.memory.memory = 0 := by
      have same := congrArg BitVec.toNat zero
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded] using same
    rw [inv.binding.empty_of_count_zero countZero key]; rfl
  · rw [Search.lookup_after_hash_eq inv.binding.layout inv.power]
    exact facts.lookup_hashed hashes place receiver bucket bucketCapacity available inv key owned aligned custody

/-- The same full-scan/publication theorem now starts at the native receiver.
Capacity, bucket, repeated field reads and selected-slot readbacks are derived,
while the native hash producer remains the explicit preceding boundary. -/
theorem Facts.probe_receiver_then_publish {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (hashes : Key → BitVec 64) (place : Initialization.Placement) (receiver bucket : Nat)
    (bucketCapacity available : BitVec 32) (embedded : place = .embedded → receiver = owner)
    (inv : Probe.Invariant hashes place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (room : 0 < available.toNat) (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (aligned : key.arguments = owned.items) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    ∃ outcome, Search.insertionAfterHash place safety before.memory.memory receiver (hashes key) key (view owned) = .ok outcome ∧
      match outcome with
      | .hit index => index < bucketCapacity.toNat ∧ ∃ entry, before.memory.effects.keys key = some entry ∧
          Table.EntryView bucketCapacity bucket index before.memory.memory key entry
      | .miss index first => ∃ after,
          publishFromReceiver place safety receiver index first (hashes key) key owned id before = (.ok (), after) ∧
          Facts safety allocator owner data capacity after rows ∧
          Probe.Invariant hashes place safety receiver bucket bucketCapacity (available - 1#32) after.memory.memory after.memory.effects.keys ∧
          after.memory.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ ∧
          after.memory.effects.allocator = before.memory.effects.allocator := by
  obtain ⟨outcome, ran, post⟩ := facts.probe_then_publish hashes place receiver bucket bucketCapacity available embedded inv room
    key owned id aligned custody
  refine ⟨outcome, (Search.insertion_after_hash_eq inv.binding.layout inv.power _ _ _).trans ran, ?_⟩
  cases outcome with
  | hit index => exact post
  | miss index first =>
    simpa only [publish_from_receiver_eq inv.binding.layout inv.power] using post

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
