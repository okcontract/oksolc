/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapAvailability

namespace Compiler.Extraction.ExpressionMap.Local
open Compiler.ZigAir.Memory Initialization Buckets

/-- The temporary native map immediately before grow's rehash loop. This is
its actual allocated storage and observations, not a second logical cache. -/
structure EmptyReady (safety : Bool) (receiver bucket : Nat) (capacity : BitVec 32) (base : Nat) (state : State) : Prop where
  valid : state.valid = true
  receiverLive : ∃ cell, state.heap.lookup receiver = some cell ∧ cell.type = ExpressionMap.allocationType safety ∧ cell.writable = true
  bucketLive : ∃ cell, state.heap.lookup bucket = some cell ∧ cell.base = base ∧ cell.type = storageType capacity.toNat ∧
    cell.writable = true ∧ cell.stack = false
  metadata : Receiver.read safety state ⟨receiver, 0⟩ = .ok (Receiver.value bucket)
  headers : ∀ slot : Header.Slot, load state (slot.pointer capacity bucket) = .ok (slot.value capacity bucket)
  size : load state (field safety receiver .size) = .ok (.scalar (.int false 32 0))
  available : load state (field safety receiver .available) = .ok (Availability.value capacity)
  locked : safety = true → load state (field safety receiver .lock) = .ok exclusive
  slots : ∀ index, index < capacity.toNat → Metadata.observe state bucket index = .ok (true, false)

def countSlot : Slot := .size

def readCount (safety : Bool) (state : State) (receiver : Nat) : Except Fault Value := do
  let selected ← fieldPointer state (.pointer (.pointer false false (ExpressionMap.allocationType safety)) ⟨receiver, 0⟩)
    (countSlot.offset safety)
  load state selected

/-- Local and embedded empty lookups use the same source size-zero branch.
Hashing, key/value reads and nonempty probing are not manufactured here. -/
def getEmpty (safety : Bool) (state : State) (receiver : Nat) (key : Compiler.Extraction.Cache.Key) :
    Except Fault (Option Compiler.Algebraic.NodeId) :=
  ExpressionMap.getEmptyFrom (readCount safety state receiver) key

theorem EmptyReady.count_read (ready : EmptyReady safety receiver bucket capacity base state) :
    readCount safety state receiver = .ok (.scalar (.int false 32 0)) := by
  have selectedField : countSlot = .size := rfl
  obtain ⟨cell, found, typed, _⟩ := ready.receiverLive
  have selected := root_fieldPointer state receiver cell (ExpressionMap.allocationType safety) (.scalar (.int false 32))
    (Placement.localMap.layout safety) (sizeOffset safety) false false ready.valid found typed
    (Placement.localMap.layout_checked safety) (by cases safety <;> decide) (by cases safety <;> rfl)
  simp only [readCount, selectedField, Slot.offset, selected, bind, Except.bind]
  simpa only [field, Slot.offset, Slot.value, load] using ready.size

/-- Lookup agrees with the existing owned-key empty table for every key, even
though the allocated key/value leaves are still uninitialized. -/
theorem EmptyReady.lookup (ready : EmptyReady safety receiver bucket capacity base state) (key : Compiler.Extraction.Cache.Key) :
    getEmpty safety state receiver key = .ok (OwnedKeys.view (fun _ => none) key) := by
  simp only [getEmpty, ExpressionMap.getEmptyFrom, ready.count_read, bind, Except.bind, ↓reduceIte,
    OwnedKeys.view, Option.map_none]

/-- The next insertion has both a positive countdown and free metadata at any
admitted probe index. This does not supply the hash/probing correspondence. -/
theorem EmptyReady.insertion_room (ready : EmptyReady safety receiver bucket capacity base state)
    (minimum : 8 ≤ capacity.toNat) (index : Nat) (inside : index < capacity.toNat) :
    ∃ available : BitVec 32,
      load state (field safety receiver .available) = .ok (.scalar (.int false 32 available.toNat)) ∧
      0 < available.toNat ∧ available.toNat < capacity.toNat ∧ Metadata.observe state bucket index = .ok (true, false) := by
  exact ⟨Availability.word capacity, ready.available, (Availability.positive capacity minimum).1,
    (Availability.positive capacity minimum).2, ready.slots index inside⟩

end Compiler.Extraction.ExpressionMap.Local

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets

/-- Complete initialization between grow's capacity guards and rehash loop. -/
def readyBuckets (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address) × World (Publication.Effects σ) :=
  let (result, cleared) := clearBuckets safety capacity allocate before
  match result with
  | .ok (some bucket) => match ExpressionMap.Local.Availability.assign safety before.memory.memory.nextId capacity cleared.memory.memory with
    | .error fault => (.error fault, cleared)
    | .ok memory => (.ok (some bucket), { cleared with memory := { cleared.memory with memory } })
  | result => (result, cleared)

theorem Facts.ready_buckets {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (room : ExpressionMap.Local.Room safety before.memory.memory)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base)
    (apart : base + bytes bucketCapacity.toNat ≤ ExpressionMap.Local.stackBase before.memory.memory ∨
      ExpressionMap.Local.stackEnd safety before.memory.memory ≤ base) :
    ∃ after, readyBuckets safety bucketCapacity allocate before =
        (.ok (some ⟨before.memory.memory.nextId + 1, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 2 ∧ after.memory.effects.allocator = effects ∧
      ExpressionMap.Local.EmptyReady safety before.memory.memory.nextId (before.memory.memory.nextId + 1)
        bucketCapacity base after.memory.memory := by
  obtain ⟨cleared, ran, clearedFacts, read, headers, cursor, reached, defaults, locked, slots, bucketLive,
    ⟨cell, found, typed, writable⟩⟩ := facts.clear_buckets room bucketCapacity positive base allocate effects response fits apart
  obtain ⟨memory, assigned, post⟩ := ExpressionMap.Local.Availability.initialize_verified safety
    before.memory.memory.nextId bucketCapacity cleared.memory.memory cell clearedFacts.valid.memory found typed writable
  let after : World (Publication.Effects σ) := { cleared with memory := { cleared.memory with memory } }
  obtain ⟨finalCell, finalFound, shape⟩ := post.shape _ cell found
  have bucketFrame := post.frame (before.memory.memory.nextId + 1) (by omega)
  obtain ⟨bucket, bucketFound, bucketBase, bucketTyped, bucketWritable, bucketPersistent⟩ := bucketLive
  have metadataBefore := ExpressionMap.Receiver.root_pointer safety cleared.memory.memory _ cell false clearedFacts.valid.memory found typed
  have metadataAfter := ExpressionMap.Receiver.root_pointer safety memory _ finalCell false post.valid finalFound (shape.2.1.trans typed)
  refine ⟨after, ?_, clearedFacts.local_map_frame _ cell found typed memory post.valid post.shape post.frame,
    post.nextId.trans cursor, reached, post.valid,
    ⟨finalCell, finalFound, shape.2.1.trans typed, shape.2.2.1.trans writable⟩,
    ⟨bucket, bucketFrame.trans bucketFound, bucketBase, bucketTyped, bucketWritable, bucketPersistent⟩,
    ?_, ?_, (post.others .size (by decide)).trans (defaults .size (by decide) (by decide)),
    post.read, fun enabled => (post.others .lock (by decide)).trans (locked enabled), ?_⟩
  · simp only [readyBuckets, ran, assigned, after]
  · simp only [ExpressionMap.Receiver.read, metadataBefore, bind, Except.bind] at read
    change ExpressionMap.Receiver.read safety memory ⟨before.memory.memory.nextId, 0⟩ = _
    simp only [ExpressionMap.Receiver.read, metadataAfter, bind, Except.bind]
    have same := post.others .metadata (by decide)
    simpa only [ExpressionMap.Local.field, ExpressionMap.Initialization.Slot.offset, ExpressionMap.metadataOffset,
      ExpressionMap.Initialization.Slot.value, Compiler.ZigAir.Memory.load] using same.trans read
  · intro slot
    exact (Compiler.ZigAir.Memory.load_eq_of_lookup cleared.memory.memory memory true false
      (slot.value bucketCapacity (before.memory.memory.nextId + 1)).type
      ⟨before.memory.memory.nextId + 1, slot.offset⟩ bucketFrame).trans (headers slot)
  · intro index inside
    change Metadata.observe memory (before.memory.memory.nextId + 1) index = _
    have same := Compiler.ZigAir.Memory.load_eq_of_lookup cleared.memory.memory memory true false Metadata.byte
      ⟨before.memory.memory.nextId + 1, 24 + index⟩ bucketFrame
    simpa only [Metadata.observe, Metadata.pointer, same] using slots index inside

theorem readyBuckets_oom (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before cleared : World (Publication.Effects σ))
    (oom : clearBuckets safety capacity allocate before = (.ok none, cleared)) :
    readyBuckets safety capacity allocate before = (.ok none, cleared) := by
  simp only [readyBuckets, oom]

theorem readyBuckets_rejected (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before cleared : World (Publication.Effects σ))
    (bucket : Compiler.ZigAir.Memory.Address) (fault : Compiler.ZigAir.Memory.Fault)
    (ran : clearBuckets safety capacity allocate before = (.ok (some bucket), cleared))
    (rejected : ExpressionMap.Local.Availability.assign safety before.memory.memory.nextId capacity cleared.memory.memory = .error fault) :
    readyBuckets safety capacity allocate before = (.error fault, cleared) := by
  simp only [readyBuckets, ran, rejected]

theorem readyBuckets_exhausted (safety : Bool) (before : World (Publication.Effects σ))
    (capacity : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (valid : before.memory.memory.valid = true) (room : ¬ExpressionMap.Local.Room safety before.memory.memory) :
    readyBuckets safety capacity allocate before = (.error .outOfMemory, before) := by
  simp only [readyBuckets, clearBuckets_exhausted safety before capacity allocate valid room]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
