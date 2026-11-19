/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapReceiver

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ExpressionMap.Buckets

/-- The two private native map allocations share typed separation from every
compiler graph object and registered argument array. -/
inductive PrivateMapStorage where
  | receiver | buckets (capacity : Nat)

def PrivateMapStorage.type (kind : PrivateMapStorage) (safety : Bool) : Compiler.ZigAir.Memory.Ty := match kind with
  | .receiver => ExpressionMap.allocationType safety
  | .buckets capacity => storageType capacity

/-- A standalone map or private bucket allocation cannot alias the owner,
backing, items or registered word arrays. Typed separation frames their stores. -/
theorem Facts.private_map_frame {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (kind : PrivateMapStorage) (receiver : Nat) (localCell : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup receiver = some localCell)
    (typed : localCell.type = kind.type safety)
    (memory : Compiler.ZigAir.Memory.State) (valid : memory.valid = true)
    (shape : before.memory.memory.heap.RetainsShape memory.heap)
    (frame : ∀ other, other ≠ receiver → memory.heap.lookup other = before.memory.memory.heap.lookup other) :
    Facts safety allocator owner data capacity { before with memory := { before.memory with memory } } rows := by
  have afterValid : Valid ({ before.memory with memory } : Session (Publication.Effects σ)) := by
    refine ⟨valid, ?_, facts.valid.injected.retained shape⟩
    intro alloc id values nonempty registered
    obtain ⟨⟨cell, located, cellType, writable, persistent⟩, represented⟩ := facts.valid.related alloc id values nonempty registered
    have apart := before.memory.memory.heap.lookup_ne_of_type_ne id receiver cell localCell located found
      (by cases kind <;> simp [PrivateMapStorage.type, storageType, cellType, typed, ExpressionMap.allocationType])
    exact ⟨⟨cell, (frame id apart).trans located, cellType, writable, persistent⟩,
      represented_frame _ values represented (frame id apart)⟩
  apply facts.frame (after := { before with memory := { before.memory with memory } }) afterValid facts.projected rfl rfl _ (fun _ _ registered => registered)
  intro id cell located guarded
  have apart : id ≠ receiver := by
    rcases guarded with rfl | ⟨nonempty, rfl⟩ | ⟨row, member, rfl⟩
    · obtain ⟨native, nativeFound, nativeType, _⟩ := facts.ownerLive
      exact before.memory.memory.heap.lookup_ne_of_type_ne _ _ native localCell nativeFound found
        (by cases kind <;> simp [PrivateMapStorage.type, storageType, nativeType, typed, Owner.viewType, ExpressionMap.allocationType])
    · obtain ⟨⟨_, _, native, nativeFound, nativeType, _, _⟩, _, _⟩ := facts.storage nonempty
      exact before.memory.memory.heap.lookup_ne_of_type_ne _ _ native localCell nativeFound found
        (by cases kind <;> simp [PrivateMapStorage.type, storageType, nativeType, typed, Backing.type, ExpressionMap.allocationType])
    · obtain ⟨native, nativeFound, nativeType, _⟩ := facts.items row member
      exact before.memory.memory.heap.lookup_ne_of_type_ne _ _ native localCell nativeFound found
        (by cases kind <;> simp [PrivateMapStorage.type, storageType, nativeType, typed, AssemblyItem.viewType, ExpressionMap.allocationType])
  exact (frame id apart).trans located

/-- The existing local-map interface specializes the same private-storage frame. -/
theorem Facts.local_map_frame {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (receiver : Nat) (localCell : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup receiver = some localCell)
    (typed : localCell.type = ExpressionMap.allocationType safety)
    (memory : Compiler.ZigAir.Memory.State) (valid : memory.valid = true)
    (shape : before.memory.memory.heap.RetainsShape memory.heap)
    (frame : ∀ other, other ≠ receiver → memory.heap.lookup other = before.memory.memory.heap.lookup other) :
    Facts safety allocator owner data capacity { before with memory := { before.memory with memory } } rows := by
  exact facts.private_map_frame .receiver receiver localCell found typed memory valid shape frame

/-- Complete native allocate on an admitted standalone receiver: reservation,
header initialization, checked metadata cast and receiver publication. The
following grow operations (locking, clearing, rehash and swap) remain separate. -/
def allocateBuckets (safety : Bool) (capacity : BitVec 32) (receiver : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address) × World (Publication.Effects σ) :=
  let (result, headed) := reserveHeader capacity allocate before
  match result with
  | .ok (some bucket) =>
    match ExpressionMap.Receiver.publish safety capacity ⟨receiver, 0⟩ bucket.allocation headed.memory.memory with
    | .error fault => (.error fault, headed)
    | .ok memory => (.ok (some bucket), { headed with memory := { headed.memory with memory } })
  | result => (result, headed)

/-- A verification rejection during receiver publication retains the actual
completed allocation/header prefix and its allocator effects. -/
theorem allocateBuckets_rejected (safety : Bool) (capacity : BitVec 32) (receiver : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (before headed : World (Publication.Effects σ)) (bucket : Compiler.ZigAir.Memory.Address)
    (fault : Compiler.ZigAir.Memory.Fault)
    (reserved : reserveHeader capacity allocate before = (.ok (some bucket), headed))
    (rejected : ExpressionMap.Receiver.publish safety capacity ⟨receiver, 0⟩ bucket.allocation headed.memory.memory = .error fault) :
    allocateBuckets safety capacity receiver allocate before = (.error fault, headed) := by
  simp only [allocateBuckets, reserved, rejected]

theorem Facts.allocate_buckets_framed {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (receiver : Nat) (localCell : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup receiver = some localCell)
    (typed : localCell.type = ExpressionMap.allocationType safety) (writable : localCell.writable = true)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base) :
    ∃ after, allocateBuckets safety bucketCapacity receiver allocate before =
        (.ok (some ⟨before.memory.memory.nextId, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨receiver, 0⟩ =
        .ok (ExpressionMap.Receiver.value before.memory.memory.nextId) ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer bucketCapacity before.memory.memory.nextId) = .ok (slot.value bucketCapacity before.memory.memory.nextId)) ∧
      (∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
        cell.base = base ∧ cell.type = storageType bucketCapacity.toNat ∧ cell.writable = true ∧ cell.stack = false) ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      after.memory.memory.nextAddress = max before.memory.memory.nextAddress (base + bytes bucketCapacity.toNat) ∧
      after.memory.effects.allocator = effects ∧
      (∃ cell, after.memory.memory.heap.lookup receiver = some cell ∧
        cell.type = ExpressionMap.allocationType safety ∧ cell.writable = true) ∧
      (∀ slot : ExpressionMap.Initialization.Slot, slot ≠ .metadata →
        Compiler.ZigAir.Memory.load after.memory.memory
          (.pointer (.pointer true false slot.value.type) ⟨receiver, slot.offset safety⟩) =
        Compiler.ZigAir.Memory.load before.memory.memory
          (.pointer (.pointer true false slot.value.type) ⟨receiver, slot.offset safety⟩)) := by
  have apart : receiver ≠ before.memory.memory.nextId := Nat.ne_of_lt
    (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
  obtain ⟨headed, ran, headedFacts, reads, live, _, cursor, address, reached, retained⟩ :=
    facts.reserve_header_framed bucketCapacity positive base allocate effects response fits
  obtain ⟨bucketCell, bucketFound, bucketBase, bucketType, bucketWritable, persistent⟩ := live
  have localFound := (retained receiver apart).trans found
  obtain ⟨memory, published, stored, valid, shape, read, frame, nextId, nextAddress⟩ :=
    ExpressionMap.Receiver.publish_verified safety headed.memory.memory receiver before.memory.memory.nextId localCell bucketCell
      bucketCapacity positive headedFacts.valid.memory localFound typed writable bucketFound bucketType bucketWritable
  let after : World (Publication.Effects σ) := { headed with memory := { headed.memory with memory } }
  obtain ⟨finalCell, finalFound, finalShape⟩ := shape receiver localCell localFound
  refine ⟨after, ?_, headedFacts.local_map_frame receiver localCell localFound typed memory valid shape frame,
    read, ?_, ⟨bucketCell, (frame _ apart.symm).trans bucketFound, bucketBase, bucketType, bucketWritable, persistent⟩,
    nextId.trans cursor, nextAddress.trans address, reached,
    ⟨finalCell, finalFound, finalShape.2.1.trans typed, finalShape.2.2.1.trans writable⟩, ?_⟩
  · simp only [allocateBuckets, ran, published, after]
  · intro slot
    have same := Compiler.ZigAir.Memory.load_eq_of_lookup headed.memory.memory memory true false
      (slot.value bucketCapacity before.memory.memory.nextId).type
      ⟨before.memory.memory.nextId, slot.offset⟩ (frame _ apart.symm)
    exact same.trans (reads slot)
  · intro slot different
    have preserved := ExpressionMap.Initialization.load_frame_at .localMap safety headed.memory.memory memory receiver
      (ExpressionMap.Receiver.value before.memory.memory.nextId) .metadata slot rfl different true
      (by simpa only [ExpressionMap.Initialization.Placement.offset, ExpressionMap.Initialization.Slot.offset,
        ExpressionMap.metadataOffset, Nat.zero_add] using stored)
    have same := Compiler.ZigAir.Memory.load_eq_of_lookup before.memory.memory headed.memory.memory true false
      slot.value.type ⟨receiver, slot.offset safety⟩ (retained receiver apart)
    simp only [ExpressionMap.Initialization.Placement.offset, Nat.zero_add] at preserved
    exact preserved.trans same

theorem Facts.allocate_buckets {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (receiver : Nat) (localCell : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup receiver = some localCell)
    (typed : localCell.type = ExpressionMap.allocationType safety) (writable : localCell.writable = true)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base) :
    ∃ after, allocateBuckets safety bucketCapacity receiver allocate before =
        (.ok (some ⟨before.memory.memory.nextId, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨receiver, 0⟩ =
        .ok (ExpressionMap.Receiver.value before.memory.memory.nextId) ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer bucketCapacity before.memory.memory.nextId) = .ok (slot.value bucketCapacity before.memory.memory.nextId)) ∧
      (∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
        cell.base = base ∧ cell.type = storageType bucketCapacity.toNat ∧ cell.writable = true ∧ cell.stack = false) ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      after.memory.memory.nextAddress = max before.memory.memory.nextAddress (base + bytes bucketCapacity.toNat) ∧
      after.memory.effects.allocator = effects := by
  obtain ⟨after, ran, facts, read, headers, live, cursor, address, effects, _⟩ :=
    facts.allocate_buckets_framed receiver localCell found typed writable bucketCapacity positive base allocate effects response fits
  exact ⟨after, ran, facts, read, headers, live, cursor, address, effects⟩

theorem allocateBuckets_oom (safety : Bool) (before : World (Publication.Effects σ)) (receiver : Nat)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (valid : before.memory.memory.valid = true)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (none, effects)) :
    allocateBuckets safety bucketCapacity receiver allocate before = (.ok none,
      { before with memory := { before.memory with effects := { before.memory.effects with allocator := effects } } }) := by
  simp only [allocateBuckets, reserveHeader_oom before bucketCapacity positive allocate effects valid response]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
