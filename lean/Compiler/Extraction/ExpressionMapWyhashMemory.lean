/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHeapFrame
import Compiler.Extraction.ExpressionMapHashBytesRun

set_option maxRecDepth 4096

namespace Compiler.Extraction.ExpressionMap.Search
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

/-- Captured scalar views read the materialized key before scoped hashing.
The reached state retains allocation history; complete caller AIR is open. -/
def scopedHash (state : State) (key : Key) (source : View) : Except Fault (BitVec 64) × State :=
  HashBytes.run state key source

def withScopedWyhash (place : Initialization.Placement) (safety : Bool) (state : State) (receiver : Nat)
    (key : Key) (source : View) : Except Fault (Option (BitVec 32)) × State :=
  match readCount place safety state receiver with
  | .error fault => (.error fault, state)
  | .ok size =>
    if size = 0 then (.ok none, state) else
    let (hashed, after) := scopedHash state key source
    match hashed with
    | .error fault => (.error fault, after)
    | .ok hash => (lookupAfterHash place safety after receiver hash key source, after)

def insertionWithScopedWyhash (place : Initialization.Placement) (safety : Bool) (state : State) (receiver : Nat)
    (key : Key) (source : View) : Except Fault Probe.Outcome × State :=
  let (hashed, after) := scopedHash state key source
  match hashed with
  | .error fault => (.error fault, after)
  | .ok hash => (insertionAfterHash place safety after receiver hash key source, after)

end Compiler.Extraction.ExpressionMap.Search

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray ExpressionMap RepresentativeArray

variable {safety : Bool} {allocator owner capacity : Nat} {data : Address}
  {before : World (Publication.Effects σ)} {rows : List Storage.Cell}

/-- Original custody derives the actual key-field and argument-byte reads.
Local allocation, writable regions and exact cleanup require no extra premise. -/
theorem Facts.scoped_hash (facts : Facts safety allocator owner data capacity before rows)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    (Search.scopedHash before.memory.memory key (view owned)).2.valid = true ∧
    (Search.scopedHash before.memory.memory key (view owned)).2.heap = before.memory.memory.heap ∧
    ((Search.scopedHash before.memory.memory key (view owned)).1 = .ok (WyhashHash.digest (HashInput.encode key)) ∨
      (Search.scopedHash before.memory.memory key (view owned)).1 = .error .outOfMemory) := by
  obtain ⟨represented, _⟩ := facts.query_view key owned aligned custody
  have budget := facts.query_byte_budget owned custody
  exact HashBytes.run_verified _ _ _ facts.valid.memory represented (by simpa only [aligned] using budget)

theorem Facts.lookup_from_scoped_wyhash (facts : Facts safety allocator owner data capacity before rows)
    (place : Initialization.Placement) (receiver bucket : Nat) (bucketCapacity available : BitVec 32)
    (inv : Probe.Invariant (WyhashHash.digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    (Search.withScopedWyhash place safety before.memory.memory receiver key (view owned)).2.valid = true ∧
    (Search.withScopedWyhash place safety before.memory.memory receiver key (view owned)).2.heap = before.memory.memory.heap ∧
    ((Search.withScopedWyhash place safety before.memory.memory receiver key (view owned)).1 =
      .ok ((before.memory.effects.keys key).map OwnedKeys.Entry.id) ∨
      (Search.withScopedWyhash place safety before.memory.memory receiver key (view owned)).1 = .error .outOfMemory) := by
  have count := inv.binding.read_count
  unfold Search.withScopedWyhash
  simp only [count]
  by_cases zero : BitVec.ofNat 32 (Table.count bucketCapacity bucket before.memory.memory) = 0
  · rw [if_pos zero]
    have looked := facts.lookup_from_receiver _ place receiver bucket bucketCapacity available inv key owned aligned custody
    simp only [Search.withHash, count, bind, Except.bind, if_pos zero] at looked
    exact ⟨facts.valid.memory, rfl, Or.inl looked⟩
  · rw [if_neg zero]
    have hashed := facts.scoped_hash key owned aligned custody
    cases reached : Search.scopedHash before.memory.memory key (view owned) with
    | mk result after =>
      rw [reached] at hashed
      obtain ⟨valid, same, succeeded | failed⟩ := hashed
      · dsimp only at valid same succeeded
        rw [succeeded]
        have afterFacts := facts.same_heap after valid same
        have afterInv := HeapFrame.invariant same valid inv
        have looked := afterFacts.lookup_from_receiver _ place receiver bucket bucketCapacity available afterInv key owned aligned
          ⟨⟨custody.live, custody.apart⟩, custody.operands⟩
        have countSame : Search.readCount place safety after receiver = Search.readCount place safety before.memory.memory receiver := by
          simp only [Search.readCount, Capacity.readField, Initialization.read, Initialization.pointer,
            cacheFieldPointer, HeapFrame.loads same, HeapFrame.fields same]
        change Search.withHash place safety after receiver (WyhashHash.digest ∘ HashInput.encode) key (view owned) =
          .ok ((before.memory.effects.keys key).map OwnedKeys.Entry.id) at looked
        dsimp only [Search.withHash, Function.comp] at looked
        rw [countSame, count] at looked
        dsimp only [bind, Except.bind] at looked
        rw [if_neg zero] at looked
        exact ⟨valid, same, Or.inl looked⟩
      · rw [failed]
        exact ⟨valid, same, Or.inr rfl⟩

/-- Publication consumes the reached state, including advanced allocation
cursors. The existing collision/probe and ownership proof is instantiated, not
reconstructed; exhaustion cannot enter the publication branch. -/
theorem Facts.probe_scoped_wyhash_then_publish (facts : Facts safety allocator owner data capacity before rows)
    (place : Initialization.Placement) (receiver bucket : Nat) (bucketCapacity available : BitVec 32)
    (embedded : place = .embedded → receiver = owner)
    (inv : Probe.Invariant (WyhashHash.digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity available before.memory.memory before.memory.effects.keys)
    (room : 0 < available.toNat) (key : Key) (owned : ArgumentSlice) (id : Compiler.Algebraic.NodeId)
    (aligned : key.arguments = owned.items) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    ∃ outcome reached,
      Search.insertionWithScopedWyhash place safety before.memory.memory receiver key (view owned) = (outcome, reached) ∧
      reached.valid = true ∧ reached.heap = before.memory.memory.heap ∧
      match outcome with
      | .error fault => fault = .outOfMemory
      | .ok (.hit index) => index < bucketCapacity.toNat ∧ ∃ entry, before.memory.effects.keys key = some entry ∧
          Table.EntryView bucketCapacity bucket index reached key entry
      | .ok (.miss index first) => ∃ after,
          publishFromReceiver place safety receiver index first (WyhashHash.digest (HashInput.encode key)) key owned id
            (withMemory before reached) = (.ok (), after) ∧
          Facts safety allocator owner data capacity after rows ∧
          Probe.Invariant (WyhashHash.digest ∘ HashInput.encode) place safety receiver bucket bucketCapacity (available - 1#32) after.memory.memory after.memory.effects.keys ∧
          after.memory.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ ∧
          after.memory.effects.allocator = before.memory.effects.allocator := by
  have hashed := facts.scoped_hash key owned aligned custody
  cases reached : Search.scopedHash before.memory.memory key (view owned) with
  | mk result middle =>
    rw [reached] at hashed
    obtain ⟨valid, same, succeeded | failed⟩ := hashed
    · dsimp only at valid same succeeded
      have afterFacts := facts.same_heap middle valid same
      obtain ⟨outcome, probed, post⟩ := afterFacts.probe_receiver_then_publish _ place receiver bucket bucketCapacity available
        embedded (HeapFrame.invariant same valid inv) room key owned id aligned
        ⟨⟨custody.live, custody.apart⟩, custody.operands⟩
      refine ⟨.ok outcome, middle, ?_, valid, same, ?_⟩
      · simp only [Search.insertionWithScopedWyhash, reached, succeeded]
        dsimp only [withMemory, Function.comp] at probed
        exact Prod.ext probed rfl
      · cases outcome <;> simpa only [withMemory, Function.comp_apply] using post
    · exact ⟨.error .outOfMemory, middle,
        by simp only [Search.insertionWithScopedWyhash, reached, failed], valid, same, rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
