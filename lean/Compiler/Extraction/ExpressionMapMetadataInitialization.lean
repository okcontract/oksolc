/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapLocalLock
import Compiler.Extraction.ExpressionMapMetadata

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets

/-- Grow's contiguous declaration/allocation/locking/metadata-clear prefix,
after capacity guards. Every fault retains its actual reached state. -/
def clearBuckets (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address) × World (Publication.Effects σ) :=
  let (result, locked) := lockBuckets safety capacity allocate before
  match result with
  | .ok (some bucket) =>
    let (cleared, memory) := Metadata.clear safety ⟨before.memory.memory.nextId, 0⟩ locked.memory.memory
    (cleared.map (fun _ => some bucket), { locked with memory := { locked.memory with memory } })
  | result => (result, locked)

theorem Facts.clear_buckets {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (room : ExpressionMap.Local.Room safety before.memory.memory)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base)
    (apart : base + bytes bucketCapacity.toNat ≤ ExpressionMap.Local.stackBase before.memory.memory ∨
      ExpressionMap.Local.stackEnd safety before.memory.memory ≤ base) :
    ∃ after, clearBuckets safety bucketCapacity allocate before =
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
      (∀ index, index < bucketCapacity.toNat →
        Metadata.observe after.memory.memory (before.memory.memory.nextId + 1) index = .ok (true, false)) ∧
      (∃ cell, after.memory.memory.heap.lookup (before.memory.memory.nextId + 1) = some cell ∧
        cell.base = base ∧ cell.type = storageType bucketCapacity.toNat ∧ cell.writable = true ∧ cell.stack = false) ∧
      (∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
        cell.type = ExpressionMap.allocationType safety ∧ cell.writable = true) := by
  obtain ⟨locked, ran, lockedFacts, read, headers, cursor, reached, defaults, lockRead,
    ⟨cell, found, cellBase, typed, writable, persistent⟩, ⟨localCell, localFound, localTyped, localWritable⟩⟩ :=
    facts.lock_buckets room bucketCapacity positive base allocate effects response fits apart
  obtain ⟨memory, cleared, post⟩ := Metadata.clear_verified safety ⟨before.memory.memory.nextId, 0⟩
    locked.memory.memory (before.memory.memory.nextId + 1) cell bucketCapacity positive lockedFacts.valid.memory found typed writable
    read (headers .capacity)
  let after : World (Publication.Effects σ) := { locked with memory := { locked.memory with memory } }
  have localFrame := post.frame before.memory.memory.nextId (by omega)
  have fieldFrame (slot : ExpressionMap.Initialization.Slot) := Compiler.ZigAir.Memory.load_eq_of_lookup
    locked.memory.memory memory true false slot.value.type ⟨before.memory.memory.nextId, slot.offset safety⟩ localFrame
  obtain ⟨finalCell, finalFound, shape⟩ := post.shape _ cell found
  refine ⟨after, ?_, lockedFacts.private_map_frame (.buckets bucketCapacity.toNat) _ cell found typed memory
    post.valid post.shape post.frame, (ExpressionMap.Receiver.read_eq_of_lookup safety _ _ _ localFrame).trans read,
    fun slot => (post.headers slot).trans (headers slot), post.nextId.trans cursor, reached,
    fun slot notMetadata notLock => (fieldFrame slot).trans (defaults slot notMetadata notLock),
    fun enabled => (fieldFrame .lock).trans (lockRead enabled), post.free_unused,
    ⟨finalCell, finalFound, shape.1.trans cellBase, shape.2.1.trans typed,
      shape.2.2.1.trans writable, shape.2.2.2.trans persistent⟩,
    ⟨localCell, localFrame.trans localFound, localTyped, localWritable⟩⟩
  simp only [clearBuckets, ran, cleared, Except.map, after]

theorem clearBuckets_oom (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before locked : World (Publication.Effects σ))
    (oom : lockBuckets safety capacity allocate before = (.ok none, locked)) :
    clearBuckets safety capacity allocate before = (.ok none, locked) := by
  simp only [clearBuckets, oom]

theorem clearBuckets_rejected (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before locked : World (Publication.Effects σ))
    (bucket : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State) (fault : Compiler.ZigAir.Memory.Fault)
    (ran : lockBuckets safety capacity allocate before = (.ok (some bucket), locked))
    (rejected : Metadata.clear safety ⟨before.memory.memory.nextId, 0⟩ locked.memory.memory = (.error fault, memory)) :
    clearBuckets safety capacity allocate before = (.error fault, { locked with memory := { locked.memory with memory } }) := by
  simp only [clearBuckets, ran, rejected, Except.map]

theorem clearBuckets_exhausted (safety : Bool) (before : World (Publication.Effects σ))
    (capacity : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (valid : before.memory.memory.valid = true) (room : ¬ExpressionMap.Local.Room safety before.memory.memory) :
    clearBuckets safety capacity allocate before = (.error .outOfMemory, before) := by
  simp only [clearBuckets, lockBuckets_exhausted safety before capacity allocate valid room]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
