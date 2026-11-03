/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashInputMemory
import Compiler.Extraction.WyhashHash

namespace Compiler.Extraction.ExpressionMap.HashInput
open Compiler.ZigAir.Memory
open Compiler.Extraction.Cache (Key)

/-- Original caller custody derives this budget. It excludes smallKey and
supplies both total-length and per-update loop arithmetic without new premises. -/
theorem wyhash_bounds (key : Key) (budget : key.arguments.length * 4 + 48 < addressLimit) :
    16 < (encode key).flatten.length ∧ (encode key).flatten.length < addressLimit ∧
      ∀ input ∈ encode key, input.length + 48 < addressLimit := by
  refine ⟨?_, ?_, ?_⟩
  · rw [total_length]; omega
  · rw [total_length]; omega
  · intro input inside
    have width := List.mem_map_of_mem (f := List.length) inside
    rw [shape] at width
    simp only [List.mem_cons, List.not_mem_nil, or_false] at width
    have fixed : 80 < addressLimit := by decide
    omega

theorem wyhash_verified (key : Key) (budget : key.arguments.length * 4 + 48 < addressLimit) :
    WyhashHash.run 0 (encode key) = .ok (WyhashHash.digest (encode key)) := by
  obtain ⟨long, bounded, budgets⟩ := wyhash_bounds key budget
  exact WyhashHash.run_digest _ long bounded budgets

end Compiler.Extraction.ExpressionMap.HashInput

namespace Compiler.Extraction.ExpressionMap.Search
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

/-- Actual byte observation followed by complete local-cell Wyhash execution.
The native stack allocation/frame of those local cells remains to be attached;
this operation does not claim that the complete heap-level hash is verified. -/
def withLocalWyhash (place : Initialization.Placement) (safety : Bool) (state : State) (receiver : Nat)
    (key : Key) (source : View) : Except Fault (Option (BitVec 32)) := do
  let size ← readCount place safety state receiver
  if size = 0 then .ok none else do
    let inputs ← HashInput.read state key source
    let hash ← WyhashHash.run 0 inputs
    lookupAfterHash place safety state receiver hash key source

def insertionWithLocalWyhash (place : Initialization.Placement) (safety : Bool) (state : State) (receiver : Nat)
    (key : Key) (source : View) : Except Fault Probe.Outcome := do
  let inputs ← HashInput.read state key source
  let hash ← WyhashHash.run 0 inputs
  insertionAfterHash place safety state receiver hash key source

theorem with_local_wyhash_eq (observed : HashInput.read state key source = .ok (HashInput.encode key))
    (budget : key.arguments.length * 4 + 48 < addressLimit) :
    withLocalWyhash place safety state receiver key source =
      withInputDigest place safety state receiver WyhashHash.digest key source := by
  simp only [withLocalWyhash, withInputDigest, observed, HashInput.wyhash_verified key budget, bind, Except.bind]

theorem insertion_with_local_wyhash_eq (observed : HashInput.read state key source = .ok (HashInput.encode key))
    (budget : key.arguments.length * 4 + 48 < addressLimit) :
    insertionWithLocalWyhash place safety state receiver key source =
      insertionWithInputDigest place safety state receiver WyhashHash.digest key source := by
  simp only [insertionWithLocalWyhash, insertionWithInputDigest, observed, HashInput.wyhash_verified key budget, bind, Except.bind]

end Compiler.Extraction.ExpressionMap.Search

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray ExpressionMap RepresentativeArray

/-- Removes the arbitrary supplied digest at the local hash consumer. Original
table/graph/caller admission is unchanged; native local heap admission is open. -/
theorem Facts.lookup_from_local_wyhash {safety : Bool} {allocator owner capacity : Nat}
    {data : Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : Initialization.Placement) (receiver bucket : Nat) (bucketCapacity available : BitVec 32)
    (inv : Probe.Invariant (WyhashHash.digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    Search.withLocalWyhash place safety before.memory.memory receiver key (view owned) =
      .ok ((before.memory.effects.keys key).map OwnedKeys.Entry.id) := by
  obtain ⟨observed, _, budget⟩ := facts.hash_input key owned aligned custody
  rw [Search.with_local_wyhash_eq observed (by simpa only [aligned] using budget), Search.with_input_digest_eq observed]
  exact facts.lookup_from_receiver _ place receiver bucket bucketCapacity available inv key owned aligned custody

theorem Facts.probe_local_wyhash_then_publish {safety : Bool} {allocator owner capacity : Nat}
    {data : Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : Initialization.Placement) (receiver bucket : Nat) (bucketCapacity available : BitVec 32)
    (embedded : place = .embedded → receiver = owner)
    (inv : Probe.Invariant (WyhashHash.digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (room : 0 < available.toNat) (key : Key) (owned : ArgumentSlice) (id : Compiler.Algebraic.NodeId)
    (aligned : key.arguments = owned.items) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    ∃ outcome, Search.insertionWithLocalWyhash place safety before.memory.memory receiver key (view owned) = .ok outcome ∧
      match outcome with
      | .hit index => index < bucketCapacity.toNat ∧ ∃ entry, before.memory.effects.keys key = some entry ∧
          Table.EntryView bucketCapacity bucket index before.memory.memory key entry
      | .miss index first => ∃ after,
          publishFromReceiver place safety receiver index first (WyhashHash.digest (HashInput.encode key)) key owned id before = (.ok (), after) ∧
          Facts safety allocator owner data capacity after rows ∧
          Probe.Invariant (WyhashHash.digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity (available - 1#32) after.memory.memory after.memory.effects.keys ∧
          after.memory.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ ∧
          after.memory.effects.allocator = before.memory.effects.allocator := by
  obtain ⟨observed, _, budget⟩ := facts.hash_input key owned aligned custody
  rw [Search.insertion_with_local_wyhash_eq observed (by simpa only [aligned] using budget), Search.insertion_with_input_digest_eq observed]
  simpa only [Function.comp_apply] using facts.probe_receiver_then_publish (WyhashHash.digest ∘ HashInput.encode)
    place receiver bucket bucketCapacity available embedded inv room key owned id aligned custody

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
