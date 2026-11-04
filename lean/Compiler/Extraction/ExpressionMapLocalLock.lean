/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapLocalAllocation

namespace Compiler.Extraction.ExpressionMap.Local
open Compiler.ZigAir.Memory Initialization

/-- Zig SafetyLock.State.exclusive is maxInt(usize), not the shared count 1. -/
def exclusive : Value := .scalar (.int false 64 18446744073709551615)

/-- SafetyLock.lock's assertion is a verification rejection when its read is
not unlocked. ReleaseFast has no stored lock and performs no memory access. -/
def lock (safety : Bool) (receiver : Nat) (before : State) : Except Fault State := do
  if !safety then return before
  let current ← load before (field safety receiver .lock)
  if current ≠ .scalar (.int false 64 0) then .error .unsupported
  else store before (field safety receiver .lock) exclusive

structure Locked (safety : Bool) (receiver : Nat) (before after : State) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  frame : ∀ other, other ≠ receiver → after.heap.lookup other = before.heap.lookup other
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  read : safety = true → load after (field safety receiver .lock) = .ok exclusive
  others : ∀ slot, slot ≠ .lock → load after (field safety receiver slot) = load before (field safety receiver slot)

theorem lock_verified (safety : Bool) (before : State) (receiver : Nat) (cell : Allocation)
    (valid : before.valid = true) (found : before.heap.lookup receiver = some cell)
    (typed : cell.type = allocationType safety) (writable : cell.writable = true)
    (unlocked : safety = true → load before (field safety receiver .lock) = .ok (.scalar (.int false 64 0))) :
    ∃ after, lock safety receiver before = .ok after ∧ Locked safety receiver before after := by
  cases safety with
  | false => exact ⟨before, rfl, valid, Heap.RetainsShape.refl _, fun _ _ => rfl, rfl, rfl,
      (by intro impossible; cases impossible), fun _ _ => rfl⟩
  | true =>
    obtain ⟨after, stored, post⟩ := store_value_verified true before receiver cell .lock exclusive rfl (by decide)
      (fun _ => rfl) valid found typed writable
    refine ⟨after, ?_, post.valid, post.shape, post.frame, post.nextId, post.nextAddress, fun _ => post.read, post.others⟩
    simp only [lock, Bool.not_true, Bool.false_eq_true, ↓reduceIte, unlocked rfl, bind, Except.bind,
      ne_self_iff_false, stored, pure, Except.pure]

theorem lock_rejected (before : State) (receiver : Nat) (value : Value)
    (read : load before (field true receiver .lock) = .ok value)
    (held : value ≠ .scalar (.int false 64 0)) : lock true receiver before = .error .unsupported := by
  simp only [lock, Bool.not_true, Bool.false_eq_true, ↓reduceIte, read, bind, Except.bind, pure, Except.pure]
  exact if_pos held

theorem lock_without_safety (before : State) (receiver : Nat) : lock false receiver before = .ok before := rfl

end Compiler.Extraction.ExpressionMap.Local

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets

/-- The contiguous grow prefix through its temporary-map lock, after capacity
selection/guards. OOM does not reach the lock; rejection retains the prefix. -/
def lockBuckets (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address) × World (Publication.Effects σ) :=
  let (result, prepared) := prepareBuckets safety capacity allocate before
  match result with
  | .ok (some bucket) => match ExpressionMap.Local.lock safety before.memory.memory.nextId prepared.memory.memory with
    | .error fault => (.error fault, prepared)
    | .ok memory => (.ok (some bucket), { prepared with memory := { prepared.memory with memory } })
  | result => (result, prepared)

theorem Facts.lock_buckets {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (room : ExpressionMap.Local.Room safety before.memory.memory)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base)
    (apart : base + bytes bucketCapacity.toNat ≤ ExpressionMap.Local.stackBase before.memory.memory ∨
      ExpressionMap.Local.stackEnd safety before.memory.memory ≤ base) :
    ∃ after, lockBuckets safety bucketCapacity allocate before =
        (.ok (some ⟨before.memory.memory.nextId + 1, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨before.memory.memory.nextId, 0⟩ =
        .ok (ExpressionMap.Receiver.value (before.memory.memory.nextId + 1)) ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer bucketCapacity (before.memory.memory.nextId + 1)) =
        .ok (slot.value bucketCapacity (before.memory.memory.nextId + 1))) ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 2 ∧
      after.memory.effects.allocator = effects ∧
      (∀ slot : ExpressionMap.Initialization.Slot, slot ≠ .metadata → slot ≠ .lock →
        Compiler.ZigAir.Memory.load after.memory.memory (ExpressionMap.Local.field safety before.memory.memory.nextId slot) =
          .ok slot.value) ∧
      (safety = true → Compiler.ZigAir.Memory.load after.memory.memory
        (ExpressionMap.Local.field safety before.memory.memory.nextId .lock) = .ok ExpressionMap.Local.exclusive) ∧
      (∃ cell, after.memory.memory.heap.lookup (before.memory.memory.nextId + 1) = some cell ∧
        cell.base = base ∧ cell.type = storageType bucketCapacity.toNat ∧ cell.writable = true ∧ cell.stack = false) ∧
      (∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
        cell.type = ExpressionMap.allocationType safety ∧ cell.writable = true) := by
  obtain ⟨prepared, ran, preparedFacts, read, headers, cursor, reached, ⟨cell, found, typed, writable⟩, defaults, ⟨bucket, bucketFound, bucketBase, bucketType, bucketWritable, bucketPersistent⟩⟩ :=
    facts.prepare_buckets_framed room bucketCapacity positive base allocate effects response fits apart
  obtain ⟨memory, locked, post⟩ := ExpressionMap.Local.lock_verified safety prepared.memory.memory
    before.memory.memory.nextId cell preparedFacts.valid.memory found typed writable
    (by intro enabled; exact defaults .lock (fun _ => enabled) (by decide))
  let after : World (Publication.Effects σ) := { prepared with memory := { prepared.memory with memory } }
  obtain ⟨finalCell, finalFound, shape⟩ := post.shape _ cell found
  have readBefore := ExpressionMap.Receiver.root_pointer safety prepared.memory.memory _ cell false preparedFacts.valid.memory found typed
  have readAfter := ExpressionMap.Receiver.root_pointer safety memory _ finalCell false post.valid finalFound (shape.2.1.trans typed)
  refine ⟨after, by simp only [lockBuckets, ran, locked, after],
    preparedFacts.local_map_frame _ cell found typed memory post.valid post.shape post.frame,
    ?_, ?_, post.nextId.trans cursor, reached, ?_, post.read,
    ⟨bucket, (post.frame _ (by omega)).trans bucketFound, bucketBase, bucketType, bucketWritable, bucketPersistent⟩,
    ⟨finalCell, finalFound, shape.2.1.trans typed, shape.2.2.1.trans writable⟩⟩
  · simp only [ExpressionMap.Receiver.read, readBefore, bind, Except.bind] at read
    change ExpressionMap.Receiver.read safety memory ⟨before.memory.memory.nextId, 0⟩ = _
    simp only [ExpressionMap.Receiver.read, readAfter, bind, Except.bind]
    have same := post.others .metadata (by decide)
    simpa only [ExpressionMap.Local.field, ExpressionMap.Initialization.Slot.offset, ExpressionMap.metadataOffset,
      ExpressionMap.Initialization.Slot.value, Compiler.ZigAir.Memory.load] using same.trans read
  · intro slot
    exact (Compiler.ZigAir.Memory.load_eq_of_lookup prepared.memory.memory memory true false
      (slot.value bucketCapacity (before.memory.memory.nextId + 1)).type
      ⟨before.memory.memory.nextId + 1, slot.offset⟩
      (post.frame _ (by change before.memory.memory.nextId + 1 ≠ before.memory.memory.nextId; omega))).trans (headers slot)
  · intro slot notMetadata notLock
    exact (post.others slot notLock).trans (defaults slot (by intro impossible; exact False.elim (notLock impossible)) notMetadata)

theorem lockBuckets_oom (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before prepared : World (Publication.Effects σ))
    (oom : prepareBuckets safety capacity allocate before = (.ok none, prepared)) :
    lockBuckets safety capacity allocate before = (.ok none, prepared) := by
  simp only [lockBuckets, oom]

theorem lockBuckets_rejected (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before prepared : World (Publication.Effects σ))
    (bucket : Compiler.ZigAir.Memory.Address) (fault : Compiler.ZigAir.Memory.Fault)
    (ran : prepareBuckets safety capacity allocate before = (.ok (some bucket), prepared))
    (rejected : ExpressionMap.Local.lock safety before.memory.memory.nextId prepared.memory.memory = .error fault) :
    lockBuckets safety capacity allocate before = (.error fault, prepared) := by
  simp only [lockBuckets, ran, rejected]

theorem lockBuckets_exhausted (safety : Bool) (before : World (Publication.Effects σ))
    (capacity : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (valid : before.memory.memory.valid = true) (room : ¬ExpressionMap.Local.Room safety before.memory.memory) :
    lockBuckets safety capacity allocate before = (.error .outOfMemory, before) := by
  simp only [lockBuckets, prepareBuckets_exhausted safety before capacity allocate valid room]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
