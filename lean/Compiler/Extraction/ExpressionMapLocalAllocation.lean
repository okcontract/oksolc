/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapLocal

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets

def declareMap (safety : Bool) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault Compiler.ZigAir.Memory.Address × World (Publication.Effects σ) :=
  let (result, memory) := ExpressionMap.Local.declare safety before.memory.memory
  (result, { before with memory := { before.memory with memory } })

theorem Facts.declare_map {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (room : ExpressionMap.Local.Room safety before.memory.memory) :
    ∃ after cell, declareMap safety before = (.ok ⟨before.memory.memory.nextId, 0⟩, after) ∧
      Facts safety allocator owner data capacity after rows ∧
      after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
      cell.type = ExpressionMap.allocationType safety ∧ cell.writable = true ∧ cell.stack = true ∧
      (∀ slot, slot.Active safety → Compiler.ZigAir.Memory.load after.memory.memory
        (ExpressionMap.Local.field safety before.memory.memory.nextId slot) = .ok slot.value) ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 1 ∧
      after.memory.memory.nextAddress = ExpressionMap.Local.stackEnd safety before.memory.memory ∧
      after.memory.effects = before.memory.effects := by
  obtain ⟨memory, cell, ran, valid, shape, found, _, typed, writable, stack, reads, frame, nextId, nextAddress⟩ :=
    ExpressionMap.Local.declare_verified safety before.memory.memory facts.valid.memory room
  let after : World (Publication.Effects σ) := { before with memory := { before.memory with memory } }
  have afterValid := facts.valid.private_memory_frame before.memory memory before.memory.memory.nextId
    (facts.valid.injected.fresh facts.valid.memory) valid shape frame
  have afterFacts : Facts safety allocator owner data capacity after rows := by
    apply facts.frame (after := after) afterValid facts.projected rfl rfl _ (fun _ _ registered => registered)
    intro id old located _
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory located).1
    exact (frame id (by omega)).trans located
  exact ⟨after, cell, by simp only [declareMap, ran, after], afterFacts, found, typed, writable, stack, reads,
    nextId, nextAddress, rfl⟩

/-- The contiguous declaration/allocation prefix after grow's capacity guards.
It retains the declared local on ordinary allocator OOM; scope cleanup and the
remaining grow statements are not silently folded into this prefix. -/
def prepareBuckets (safety : Bool) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault (Option Compiler.ZigAir.Memory.Address) × World (Publication.Effects σ) :=
  let (result, declared) := declareMap safety before
  match result with
  | .error fault => (.error fault, declared)
  | .ok receiver => allocateBuckets safety capacity receiver.allocation allocate declared

/-- Original native validity, stack room and allocator-region admission derive
the receiver and its initialization. Neither the receiver cell nor successful
declaration, stores, publication or final graph facts are supplied premises. -/
theorem Facts.prepare_buckets_framed {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (room : ExpressionMap.Local.Room safety before.memory.memory)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base)
    (apart : base + bytes bucketCapacity.toNat ≤ ExpressionMap.Local.stackBase before.memory.memory ∨
      ExpressionMap.Local.stackEnd safety before.memory.memory ≤ base) :
    ∃ after, prepareBuckets safety bucketCapacity allocate before =
        (.ok (some ⟨before.memory.memory.nextId + 1, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨before.memory.memory.nextId, 0⟩ =
        .ok (ExpressionMap.Receiver.value (before.memory.memory.nextId + 1)) ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer bucketCapacity (before.memory.memory.nextId + 1)) =
        .ok (slot.value bucketCapacity (before.memory.memory.nextId + 1))) ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 2 ∧
      after.memory.effects.allocator = effects ∧
      (∃ cell, after.memory.memory.heap.lookup before.memory.memory.nextId = some cell ∧
        cell.type = ExpressionMap.allocationType safety ∧ cell.writable = true) ∧
      (∀ slot, slot.Active safety → slot ≠ .metadata → Compiler.ZigAir.Memory.load after.memory.memory
        (ExpressionMap.Local.field safety before.memory.memory.nextId slot) = .ok slot.value) ∧
      (∃ cell, after.memory.memory.heap.lookup (before.memory.memory.nextId + 1) = some cell ∧
        cell.base = base ∧ cell.type = storageType bucketCapacity.toNat ∧ cell.writable = true ∧ cell.stack = false) := by
  obtain ⟨declared, cell, declaration, declaredFacts, found, typed, writable, _, defaults, cursor, _, unchanged⟩ := facts.declare_map room
  have region := ExpressionMap.Local.declare_region safety before.memory.memory facts.valid.memory room
    ⟨bytes bucketCapacity.toNat, 16⟩ base fits apart
  have memoryEq : declared.memory.memory = (ExpressionMap.Local.declare safety before.memory.memory).2 :=
    (congrArg (fun result => result.2.memory.memory) declaration).symm
  obtain ⟨after, allocation, afterFacts, read, headers, bucketLive, nextId, _, reached, live, retained⟩ :=
    declaredFacts.allocate_buckets_framed before.memory.memory.nextId cell found typed writable bucketCapacity positive base allocate effects
      (by rw [unchanged]; exact response)
      (memoryEq.symm ▸ region)
  rw [cursor] at allocation read headers nextId bucketLive
  refine ⟨after, by simp only [prepareBuckets, declaration]; exact allocation, afterFacts, read, headers,
    by omega, reached, live, ?_, bucketLive⟩
  intro slot active different
  exact (retained slot different).trans (defaults slot active)

theorem Facts.prepare_buckets {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (room : ExpressionMap.Local.Room safety before.memory.memory)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory.memory ⟨bytes bucketCapacity.toNat, 16⟩ base)
    (apart : base + bytes bucketCapacity.toNat ≤ ExpressionMap.Local.stackBase before.memory.memory ∨
      ExpressionMap.Local.stackEnd safety before.memory.memory ≤ base) :
    ∃ after, prepareBuckets safety bucketCapacity allocate before =
        (.ok (some ⟨before.memory.memory.nextId + 1, 0⟩), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨before.memory.memory.nextId, 0⟩ =
        .ok (ExpressionMap.Receiver.value (before.memory.memory.nextId + 1)) ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer bucketCapacity (before.memory.memory.nextId + 1)) =
        .ok (slot.value bucketCapacity (before.memory.memory.nextId + 1))) ∧
      after.memory.memory.nextId = before.memory.memory.nextId + 2 ∧
      after.memory.effects.allocator = effects := by
  obtain ⟨after, ran, facts, read, headers, cursor, effects, _⟩ :=
    facts.prepare_buckets_framed room bucketCapacity positive base allocate effects response fits apart
  exact ⟨after, ran, facts, read, headers, cursor, effects⟩

theorem Facts.prepare_buckets_oom {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (room : ExpressionMap.Local.Room safety before.memory.memory)
    (bucketCapacity : BitVec 32) (positive : 0 < bucketCapacity.toNat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ) (effects : σ)
    (response : allocate (sourceRequest bucketCapacity).toNat 16 before.memory.effects.allocator = (none, effects)) :
    ∃ declared, declareMap safety before = (.ok ⟨before.memory.memory.nextId, 0⟩, declared) ∧
      prepareBuckets safety bucketCapacity allocate before = (.ok none,
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := effects } } }) ∧
      Facts safety allocator owner data capacity
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := effects } } } rows ∧
      (∀ slot, slot.Active safety → Compiler.ZigAir.Memory.load declared.memory.memory
        (ExpressionMap.Local.field safety before.memory.memory.nextId slot) = .ok slot.value) := by
  obtain ⟨declared, _, declaration, declaredFacts, _, _, _, _, reads, _, _, unchanged⟩ := facts.declare_map room
  refine ⟨declared, declaration, ?_, ?_, reads⟩
  · simp only [prepareBuckets, declaration]
    exact allocateBuckets_oom safety declared _ bucketCapacity positive allocate effects declaredFacts.valid.memory
      (by rw [unchanged]; exact response)
  · exact declaredFacts.frame ⟨declaredFacts.valid.memory, declaredFacts.valid.related, declaredFacts.valid.injected⟩ declaredFacts.projected rfl rfl
      (fun _ _ found _ => found) (fun _ _ registered => registered)

theorem prepareBuckets_exhausted (safety : Bool) (before : World (Publication.Effects σ))
    (capacity : BitVec 32) (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator σ)
    (valid : before.memory.memory.valid = true) (room : ¬ExpressionMap.Local.Room safety before.memory.memory) :
    prepareBuckets safety capacity allocate before = (.error .outOfMemory, before) := by
  simp only [prepareBuckets, declareMap, ExpressionMap.Local.declare_exhausted safety _ valid room]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
