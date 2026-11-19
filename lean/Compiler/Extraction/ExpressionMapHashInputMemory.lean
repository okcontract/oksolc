/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashInput
import Compiler.ZigAir.MemoryShapeRegions

namespace Compiler.Extraction.ExpressionMap.Search
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

/-- The digest remains a mathematical input-boundary function. This operation
observes its byte inputs; it does not certify the native hasher's execution. -/
def withInputDigest (place : Initialization.Placement) (safety : Bool) (state : State) (receiver : Nat)
    (digest : List (List (BitVec 8)) → BitVec 64) (key : Key) (source : View) : Except Fault (Option (BitVec 32)) := do
  let size ← readCount place safety state receiver
  if size = 0 then .ok none else do
    let inputs ← HashInput.read state key source
    lookupAfterHash place safety state receiver (digest inputs) key source

def insertionWithInputDigest (place : Initialization.Placement) (safety : Bool) (state : State) (receiver : Nat)
    (digest : List (List (BitVec 8)) → BitVec 64) (key : Key) (source : View) : Except Fault Probe.Outcome := do
  let inputs ← HashInput.read state key source
  insertionAfterHash place safety state receiver (digest inputs) key source

theorem with_input_digest_eq (observed : HashInput.read state key source = .ok (HashInput.encode key)) :
    withInputDigest place safety state receiver digest key source =
      withHash place safety state receiver (digest ∘ HashInput.encode) key source := by
  simp only [withInputDigest, withHash, observed, bind, Except.bind]
  rfl

theorem with_input_digest_rejected
    (count : readCount place safety state receiver = .ok size) (nonzero : size ≠ 0)
    (rejected : HashInput.read state key source = .error fault) :
    withInputDigest place safety state receiver digest key source = .error fault := by
  simp only [withInputDigest, count, nonzero, ↓reduceIte, rejected, bind, Except.bind]

theorem insertion_with_input_digest_eq (observed : HashInput.read state key source = .ok (HashInput.encode key)) :
    insertionWithInputDigest place safety state receiver digest key source =
      insertionAfterHash place safety state receiver (digest (HashInput.encode key)) key source := by
  simp only [insertionWithInputDigest, observed, bind, Except.bind]

end Compiler.Extraction.ExpressionMap.Search

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray ExpressionMap RepresentativeArray

/-- The live compiler owner and the separate argument allocation leave at least
56 bytes of address-space budget. This derives room for the 41 scalar bytes
and Wyhash's 48-byte loop arithmetic, rather than trusting a new size bound. -/
theorem Facts.query_byte_budget {safety : Bool} {allocator owner capacity : Nat}
    {data : Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (owned : ArgumentSlice) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    owned.items.length * 4 + 48 < addressLimit := by
  by_cases empty : owned.items = []
  · simp [empty, addressLimit]
  · obtain ⟨⟨cell, found, typed, _, _⟩, _⟩ := facts.valid.related allocator owned.address owned.items empty
      (custody.live.resolve_left empty)
    obtain ⟨ownerCell, ownerFound, ownerTyped, _⟩ := facts.ownerLive
    have apart := before.memory.memory.heap.lookup_ne_of_type_ne owned.address owner cell ownerCell found ownerFound
      (by simp [typed, ownerTyped, Owner.viewType])
    have shape := typed ▸ array_layout owned.items.length
    have ownerShape := ownerTyped ▸ Owner.view_layout_checked safety
    have separated := valid_regions_separated before.memory.memory owned.address owner cell ownerCell
      ⟨owned.items.length * 4, 4⟩ (Owner.layout safety) facts.valid.memory apart found ownerFound shape ownerShape
    obtain ⟨_, basePositive, actual, actualShape, _, ending, limit⟩ := valid_lookup _ _ _ facts.valid.memory found
    obtain ⟨_, ownerPositive, ownerActual, ownerActualShape, _, ownerEnding, _⟩ := valid_lookup _ _ _ facts.valid.memory ownerFound
    have same : actual = ⟨owned.items.length * 4, 4⟩ := Option.some.inj (actualShape.symm.trans shape)
    have ownerSame : ownerActual = Owner.layout safety := Option.some.inj (ownerActualShape.symm.trans ownerShape)
    subst actual ownerActual
    have ownerBytes : 56 ≤ (Owner.layout safety).bytes := by cases safety <;> decide
    dsimp only at ending separated
    omega

/-- Original custody supplies the complete five input images and arithmetic
budget. No byte-image or total-length admission premise is added. -/
theorem Facts.hash_input {safety : Bool} {allocator owner capacity : Nat}
    {data : Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    HashInput.read before.memory.memory key (view owned) = .ok (HashInput.encode key) ∧
      (HashInput.encode key).flatten.length < addressLimit ∧ owned.items.length * 4 + 48 < addressLimit := by
  obtain ⟨contents, bounded⟩ := facts.query_view key owned aligned custody
  have budget := facts.query_byte_budget owned custody
  refine ⟨HashInput.read_verified _ _ _ contents bounded, ?_, budget⟩
  rw [HashInput.total_length, aligned]
  omega

theorem Facts.lookup_from_hash_input {safety : Bool} {allocator owner capacity : Nat}
    {data : Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (digest : List (List (BitVec 8)) → BitVec 64) (place : Initialization.Placement) (receiver bucket : Nat)
    (bucketCapacity available : BitVec 32)
    (inv : Probe.Invariant (digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    (HashInput.encode key).flatten.length < addressLimit ∧
      Search.withInputDigest place safety before.memory.memory receiver digest key (view owned) =
        .ok ((before.memory.effects.keys key).map OwnedKeys.Entry.id) := by
  obtain ⟨observed, bounded, _⟩ := facts.hash_input key owned aligned custody
  refine ⟨bounded, ?_⟩
  rw [Search.with_input_digest_eq observed]
  exact facts.lookup_from_receiver _ place receiver bucket bucketCapacity available inv key owned aligned custody

/-- The same input observation also feeds the existing insertion/publication
consumer. Only the still-unverified digest operates on the derived byte images. -/
theorem Facts.probe_hash_input_then_publish {safety : Bool} {allocator owner capacity : Nat}
    {data : Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (digest : List (List (BitVec 8)) → BitVec 64) (place : Initialization.Placement) (receiver bucket : Nat)
    (bucketCapacity available : BitVec 32) (embedded : place = .embedded → receiver = owner)
    (inv : Probe.Invariant (digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (room : 0 < available.toNat) (key : Key) (owned : ArgumentSlice) (id : Compiler.Algebraic.NodeId)
    (aligned : key.arguments = owned.items) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    (HashInput.encode key).flatten.length < addressLimit ∧
    ∃ outcome, Search.insertionWithInputDigest place safety before.memory.memory receiver digest key (view owned) = .ok outcome ∧
      match outcome with
      | .hit index => index < bucketCapacity.toNat ∧ ∃ entry, before.memory.effects.keys key = some entry ∧
          Table.EntryView bucketCapacity bucket index before.memory.memory key entry
      | .miss index first => ∃ after,
          publishFromReceiver place safety receiver index first (digest (HashInput.encode key)) key owned id before = (.ok (), after) ∧
          Facts safety allocator owner data capacity after rows ∧
          Probe.Invariant (digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity (available - 1#32) after.memory.memory after.memory.effects.keys ∧
          after.memory.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ ∧
          after.memory.effects.allocator = before.memory.effects.allocator := by
  obtain ⟨observed, bounded, _⟩ := facts.hash_input key owned aligned custody
  refine ⟨bounded, ?_⟩
  simpa only [Search.insertion_with_input_digest_eq observed, Function.comp_apply] using
    facts.probe_receiver_then_publish (digest ∘ HashInput.encode) place receiver bucket bucketCapacity available embedded inv room key owned id aligned custody

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
