/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKeyWrites
import Compiler.Extraction.ExpressionMapCapacityMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets

def assignKey (bucketCapacity : BitVec 32) (bucket index : Nat) (key : Key)
    (arguments : Compiler.ZigAir.Memory.Address) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault Unit × World (Publication.Effects σ) :=
  let (result, memory) := KeyFields.assign bucketCapacity bucket index key arguments before.memory.memory
  (result, { before with memory := { before.memory with memory } })

theorem assignKey_prefix (bucketCapacity : BitVec 32) (bucket index : Nat) (key : Key)
    (arguments : Compiler.ZigAir.Memory.Address) (before : World (Publication.Effects σ))
    (result : Except Compiler.ZigAir.Memory.Fault Unit) (memory : Compiler.ZigAir.Memory.State)
    (ran : KeyFields.assign bucketCapacity bucket index key arguments before.memory.memory = (result, memory)) :
    assignKey bucketCapacity bucket index key arguments before =
      (result, { before with memory := { before.memory with memory } }) := by simp only [assignKey, ran]

/-- Actual key member stores preserve the existing graph and argument ownership
facts through the shared private-storage frame. Logical table replacement and
probing are separate consumers; this result does not invent either operation. -/
theorem Facts.assign_key {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (bucketCapacity : BitVec 32) (bucket index : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
    (inside : index < bucketCapacity.toNat)
    (found : before.memory.memory.heap.lookup bucket = some cell) (typed : cell.type = storageType bucketCapacity.toNat)
    (writable : cell.writable = true) (key : Key) (arguments : Compiler.ZigAir.Memory.Address)
    (length : key.arguments.length < Compiler.ZigAir.Memory.addressLimit)
    (header : Compiler.ZigAir.Memory.load before.memory.memory (Header.Slot.keys.pointer bucketCapacity bucket) =
      .ok (Header.Slot.keys.value bucketCapacity bucket)) :
    ∃ after, assignKey bucketCapacity bucket index key arguments before = (.ok (), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      KeyFields.Written bucketCapacity.toNat bucket index key arguments KeyFields.order before.memory.memory after.memory.memory ∧
      (∀ slot, KeyFields.read bucketCapacity bucket index slot after.memory.memory = .ok (KeyFields.value key arguments slot)) ∧
      after.memory.effects = before.memory.effects := by
  obtain ⟨memory, ran, post, _⟩ := KeyFields.assign_verified bucketCapacity bucket index key arguments
    before.memory.memory cell inside facts.valid.memory found typed writable length header
  let after : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
  exact ⟨after, assignKey_prefix bucketCapacity bucket index key arguments before (.ok ()) memory ran,
    facts.private_map_frame (.buckets bucketCapacity.toNat) bucket cell found typed memory post.valid post.shape post.frame,
    post, fun slot => post.read cell inside found typed header slot, rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
