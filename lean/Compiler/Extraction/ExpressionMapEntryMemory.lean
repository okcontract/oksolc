/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapEntry
import Compiler.Extraction.ExpressionMapCapacityMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets

def assignEntry (bucketCapacity : BitVec 32) (bucket index : Nat) (key : Key)
    (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault Unit × World (Publication.Effects σ) :=
  let (result, memory) := Entry.assign bucketCapacity bucket index key arguments id before.memory.memory
  (result, { before with memory := { before.memory with memory } })

theorem assignEntry_prefix (bucketCapacity : BitVec 32) (bucket index : Nat) (key : Key)
    (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId) (before : World (Publication.Effects σ))
    (result : Except Compiler.ZigAir.Memory.Fault Unit) (memory : Compiler.ZigAir.Memory.State)
    (ran : Entry.assign bucketCapacity bucket index key arguments id before.memory.memory = (result, memory)) :
    assignEntry bucketCapacity bucket index key arguments id before =
      (result, { before with memory := { before.memory with memory } }) := by simp only [assignEntry, ran]

/-- The complete defined key/value assignment tail preserves the existing
native graph facts and actual metadata. This does not supply getOrPut, old-key
release, or the map's logical table transition. -/
theorem Facts.assign_entry {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (bucketCapacity : BitVec 32) (bucket index : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
    (inside : index < bucketCapacity.toNat)
    (found : before.memory.memory.heap.lookup bucket = some cell) (typed : cell.type = storageType bucketCapacity.toNat)
    (writable : cell.writable = true) (key : Key) (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId)
    (length : key.arguments.length < Compiler.ZigAir.Memory.addressLimit)
    (headers : ∀ slot : Header.Slot, Compiler.ZigAir.Memory.load before.memory.memory (slot.pointer bucketCapacity bucket) =
      .ok (slot.value bucketCapacity bucket)) :
    ∃ after, assignEntry bucketCapacity bucket index key arguments id before = (.ok (), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      Entry.Stored bucketCapacity bucket index key arguments id after.memory.memory ∧
      (∀ other, other < bucketCapacity.toNat → Metadata.observe after.memory.memory bucket other =
        Metadata.observe before.memory.memory bucket other) ∧
      after.memory.effects = before.memory.effects ∧
      after.memory.memory.nextId = before.memory.memory.nextId ∧
      after.memory.memory.nextAddress = before.memory.memory.nextAddress := by
  obtain ⟨keyed, memory, ran, post⟩ := Entry.assign_verified bucketCapacity bucket index key arguments id
    before.memory.memory cell inside facts.valid.memory found typed writable length headers
  have frame := post.native_frame
  let after : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
  exact ⟨after, assignEntry_prefix bucketCapacity bucket index key arguments id before (.ok ()) memory ran,
    facts.private_map_frame (.buckets bucketCapacity.toNat) bucket cell found typed memory frame.1 frame.2.1 frame.2.2.1,
    post.stored cell inside found typed headers, post.metadata_frame, rfl, frame.2.2.2.1, frame.2.2.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
