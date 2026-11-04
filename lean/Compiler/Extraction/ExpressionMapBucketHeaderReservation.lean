/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketStorage

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ExpressionMap.Buckets

/-- Allocation and the three private header writes from native allocate. The
following receiver.metadata publication and grow's metadata clearing are still
separate obligations. A rejected write retains its actual reached memory. -/
def reserveHeader (capacity : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address) × World (Publication.Effects σ) :=
  let (result, reserved) := PrivateRegion.reserve (storageType capacity.toNat) allocate before
  match result with
  | .ok (some address) =>
    let (initialized, memory) := Header.run capacity address.allocation reserved.memory.memory
    (initialized.map (fun _ => some address), { reserved with memory := { reserved.memory with memory } })
  | result => (result, reserved)

theorem Facts.reserve_header_framed {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (bucketCapacity : BitVec 32)
    (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base) :
    ∃ after, reserveHeader bucketCapacity allocate before = (.ok (some ⟨before.memory.memory.nextId, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer bucketCapacity before.memory.memory.nextId) =
          .ok (slot.value bucketCapacity before.memory.memory.nextId)) ∧
      (∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
        cell.base = base ∧ cell.type = storageType bucketCapacity.toNat ∧ cell.writable = true ∧ cell.stack = false) ∧
      after.memory.heap before.memory.memory.nextId = none ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      after.memory.memory.nextAddress = max before.memory.memory.nextAddress (base + bytes bucketCapacity.toNat) ∧
      after.memory.effects.allocator = effects ∧
      (∀ other, other ≠ before.memory.memory.nextId →
        after.memory.memory.heap.lookup other = before.memory.memory.heap.lookup other) := by
  have checked := geometry bucketCapacity.toNat bucketCapacity.isLt
  obtain ⟨reserved, ran, reservedFacts, located, unregistered, nextId, nextAddress, reached⟩ :=
    facts.reserve_private_success (storageType bucketCapacity.toNat) ⟨bytes bucketCapacity.toNat, 16⟩ base allocate effects
      (storage_layout bucketCapacity.toNat positive) (Nat.ne_of_gt checked.2.2.2.2.2.2.1) checked.2.2.2.2.2.2.2
      (by simpa only [source_request] using response) fits
  obtain ⟨memory, initialized, valid, shape, reads, frame, keptId, keptAddress⟩ :=
    Header.run_verified reserved.memory.memory before.memory.memory.nextId _ bucketCapacity positive
      reservedFacts.valid.memory located rfl rfl
  let after : World (Publication.Effects σ) := { reserved with memory := { reserved.memory with memory } }
  have afterValid : Valid after.memory := reservedFacts.valid.private_memory_frame reserved.memory memory
    before.memory.memory.nextId unregistered valid shape frame
  have older (id : Nat) (guarded : Protected owner data capacity rows id) : id < before.memory.memory.nextId := by
    rcases guarded with rfl | ⟨nonempty, rfl⟩ | ⟨row, member, rfl⟩
    · obtain ⟨cell, found, _, _⟩ := facts.ownerLive
      exact (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
    · obtain ⟨⟨_, _, cell, found, _, _, _⟩, _, _⟩ := facts.storage nonempty
      exact (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
    · obtain ⟨cell, found, _, _⟩ := facts.items row member
      exact (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
  have afterFacts : Facts safety allocator owner data capacity after rows :=
    reservedFacts.frame afterValid reservedFacts.projected rfl rfl
      (fun id cell found guarded => (frame id (Nat.ne_of_lt (older id guarded))).trans found)
      (fun _ _ found => found)
  refine ⟨after, ?_, afterFacts, reads, ?_, unregistered, keptId.trans nextId, keptAddress.trans nextAddress, reached, ?_⟩
  · simp only [reserveHeader, ran, initialized, Except.map, after]
  · obtain ⟨cell, found, same⟩ := shape before.memory.memory.nextId _ located
    exact ⟨cell, found, same⟩
  · intro other apart
    have reservedFrame := Compiler.ZigAir.Memory.RegionAllocation.reserve_heap_other before.memory.memory
      (storageType bucketCapacity.toNat) allocate before.memory.effects.allocator other apart
    change (PrivateRegion.reserve (storageType bucketCapacity.toNat) allocate before).2.memory.memory.heap.lookup other =
      before.memory.memory.heap.lookup other at reservedFrame
    simp only [ran] at reservedFrame
    exact (frame other apart).trans reservedFrame

theorem Facts.reserve_header {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (bucketCapacity : BitVec 32)
    (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base) :
    ∃ after, reserveHeader bucketCapacity allocate before = (.ok (some ⟨before.memory.memory.nextId, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer bucketCapacity before.memory.memory.nextId) =
          .ok (slot.value bucketCapacity before.memory.memory.nextId)) ∧
      (∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
        cell.base = base ∧ cell.type = storageType bucketCapacity.toNat ∧ cell.writable = true ∧ cell.stack = false) ∧
      after.memory.heap before.memory.memory.nextId = none ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      after.memory.memory.nextAddress = max before.memory.memory.nextAddress (base + bytes bucketCapacity.toNat) ∧
      after.memory.effects.allocator = effects := by
  obtain ⟨after, ran, next, reads, live, unregistered, cursor, address, reached, _⟩ :=
    facts.reserve_header_framed bucketCapacity positive base allocate effects response fits
  exact ⟨after, ran, next, reads, live, unregistered, cursor, address, reached⟩

theorem reserveHeader_oom (before : World (Publication.Effects σ)) (bucketCapacity : BitVec 32)
    (positive : 0 < bucketCapacity.toNat) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (effects : σ) (valid : before.memory.memory.valid = true)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (none, effects)) :
    reserveHeader bucketCapacity allocate before = (.ok none, { before with memory := { before.memory with
      effects := { before.memory.effects with allocator := effects } } }) := by
  have checked := geometry bucketCapacity.toNat bucketCapacity.isLt
  have failed := PrivateRegion.oom before (storageType bucketCapacity.toNat) ⟨bytes bucketCapacity.toNat, 16⟩ allocate effects valid
    (storage_layout bucketCapacity.toNat positive) (Nat.ne_of_gt checked.2.2.2.2.2.2.1) checked.2.2.2.2.2.2.2
    (by simpa only [source_request] using response)
  simp only [reserveHeader, failed]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
