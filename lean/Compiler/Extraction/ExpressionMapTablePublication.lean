/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapTableInsertion
import Compiler.Extraction.InternerNativeGraphPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open ExpressionMap

/-- The native selected-slot execution followed by the existing logical table
projection. freshWorld is proof bookkeeping, not another compiler operation.
A native rejection retains its reached memory and does not publish a logical key. -/
def publishSelectedNew (place : Initialization.Placement) (safety : Bool) (receiver : Nat)
    (bucketCapacity : BitVec 32) (bucket index : Nat) (fp : BitVec 7) (key : Key) (owned : ArgumentSlice)
    (id : NodeId) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault Unit × World (Publication.Effects σ) :=
  match publishNewSlot place safety receiver bucketCapacity bucket index fp key ⟨owned.address, 0⟩ id before with
  | (.error fault, reached) => (.error fault, reached)
  | (.ok (), reached) => (.ok (), Publication.freshWorld key owned id reached.memory.effects.allocator reached)

theorem publishSelectedNew_rejected (place : Initialization.Placement) (safety : Bool) (receiver : Nat)
    (bucketCapacity : BitVec 32) (bucket index : Nat) (fp : BitVec 7) (key : Key) (owned : ArgumentSlice)
    (id : NodeId) (before reached : World (Publication.Effects σ)) (fault : Compiler.ZigAir.Memory.Fault)
    (ran : publishNewSlot place safety receiver bucketCapacity bucket index fp key ⟨owned.address, 0⟩ id before = (.error fault, reached)) :
    publishSelectedNew place safety receiver bucketCapacity bucket index fp key owned id before = (.error fault, reached) := by
  simp only [publishSelectedNew, ran]

/-- Derive the native and logical table update together. The original table
binding supplies initialized metadata and the size read; its unused slot derives
the arithmetic bound. Original custody supplies argument contents and lifetime.
Hashing, probe selection, rehash and the replacement branch remain separate. -/
theorem Facts.publish_selected_new {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : Initialization.Placement) (receiver : Nat) (bucketCapacity : BitVec 32) (bucket index : Nat)
    (embedded : place = .embedded → receiver = owner)
    (binding : Table.Binding place safety receiver bucket bucketCapacity before.memory.memory before.memory.effects.keys)
    (fp : BitVec 7) (available : BitVec 32) (inside : index < bucketCapacity.toNat)
    (availableRead : Compiler.ZigAir.Memory.load before.memory.memory (Counter.field place safety receiver .available) = .ok (number available))
    (room : 0 < available.toNat) (vacant : ¬Table.Used before.memory.memory bucket index)
    (key : Key) (owned : ArgumentSlice) (id : NodeId) (aligned : key.arguments = owned.items)
    (absent : before.memory.effects.keys key = none) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    ∃ after, publishSelectedNew place safety receiver bucketCapacity bucket index fp key owned id before = (.ok (), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      Table.Binding place safety receiver bucket bucketCapacity after.memory.memory after.memory.effects.keys ∧
      after.memory.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ ∧
      after.memory.effects.allocator = before.memory.effects.allocator ∧
      Insertion.Published place safety receiver bucket index bucketCapacity fp available
        (BitVec.ofNat 32 (Table.count bucketCapacity bucket before.memory.memory)) key ⟨owned.address, 0⟩ id
        before.memory.memory after.memory.memory := by
  have length : key.arguments.length < Compiler.ZigAir.Memory.addressLimit := by
    by_cases empty : key.arguments = []
    · simp [empty, Compiler.ZigAir.Memory.addressLimit]
    · have live : Memory.SliceValid allocator before.memory.heap (OwnedKeys.slice key ⟨owned.address, id⟩) := by
        simpa only [OwnedKeys.slice, aligned] using custody.live
      obtain ⟨⟨cell, found, typed, writable, _⟩, _⟩ := facts.valid.related allocator owned.address key.arguments empty (live.resolve_left empty)
      exact view_width before.memory.memory ⟨owned.address, 0, key.arguments.length⟩ facts.valid.memory
        ⟨key.arguments.length, cell, found, typed, writable, by simp⟩
  obtain ⟨bits, metadataRead⟩ := binding.metadata index inside
  have countBound := Table.count_bound bucketCapacity bucket before.memory.memory
  have countRoom := Table.count_room bucketCapacity bucket index before.memory.memory inside vacant
  have bounded : (BitVec.ofNat 32 (Table.count bucketCapacity bucket before.memory.memory)).toNat + 1 < 2 ^ 32 := by
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound]
    have := bucketCapacity.isLt
    omega
  obtain ⟨reached, ran, nativeFacts, post, effects⟩ := facts.publish_new_slot place receiver bucketCapacity bucket index embedded
    binding.layout fp available (BitVec.ofNat 32 (Table.count bucketCapacity bucket before.memory.memory)) bits inside
    availableRead binding.size metadataRead room bounded key ⟨owned.address, 0⟩ id length
  have registry : reached.memory.heap = before.memory.heap := by
    have projection : (publishNewSlot place safety receiver bucketCapacity bucket index fp key ⟨owned.address, 0⟩ id before).2.memory.heap =
        before.memory.heap := by
      unfold publishNewSlot
      split <;> rfl
    simpa only [ran] using projection
  have live : Memory.SliceValid allocator reached.memory.heap owned := by rw [registry]; exact custody.live
  have absentNow : reached.memory.effects.keys key = none := by rw [effects]; exact absent
  have fresh : OwnedKeys.Fresh reached.memory.effects.keys key ⟨owned.address, id⟩ := by
    intro query old found nonempty oldNonempty alias
    rw [effects] at found
    exact custody.apart query old found oldNonempty ⟨by simpa only [← aligned] using nonempty, alias.symm⟩
  have completed := nativeFacts.store_absent key owned id reached.memory.effects.allocator aligned absentNow live fresh custody.operands
  have incoming := Table.EntryView.of_live (allocator := allocator) (key := key) (entry := ⟨owned.address, id⟩) nativeFacts.valid
    (by simpa only [OwnedKeys.slice, aligned] using live) post.stored
  have boundAfter := binding.after_new_slot ⟨owned.address, id⟩ post inside vacant absent incoming
  refine ⟨Publication.freshWorld key owned id reached.memory.effects.allocator reached,
    by simp only [publishSelectedNew, ran], completed, ?_, ?_, ?_, post⟩
  · simpa only [Publication.freshWorld, effects] using boundAfter
  · simp only [Publication.freshWorld, effects]
  · simpa only [Publication.freshWorld] using congrArg Publication.Effects.allocator effects

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
