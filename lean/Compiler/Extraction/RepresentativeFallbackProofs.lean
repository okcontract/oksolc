/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeFallback

namespace Compiler.Extraction.RepresentativeArray.Backing.Fallback
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Ordinary OOM derives an unchanged memory/registry and reached allocator
effects before any header read, without an allocation-result premise. -/
theorem oom_verified (allocate : Registry.Allocate σ) (release : Release.External σ) (allocator : Nat)
    (header oldData : Address) (oldCapacity capacity : Nat) (before : Session σ) (effects : σ)
    (valid : before.memory.valid = true) (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (response : allocate allocator (capacity * 32) 8 before.effects = (none, effects)) :
    run allocate release allocator header oldData oldCapacity capacity before = (.ok none, {before with effects}) :=
  oom allocate release allocator header oldData oldCapacity capacity before _
    (Registry.failed allocate allocator capacity before effects valid nonempty size response)

/-- Allocation derives the fresh destination, its ownership and separation.
The existing suffix then derives copy, full old release and publication from
initial reads. The old view is an evaluated branch input: remap preservation
is not inferred from this allocation-branch theorem. -/
theorem verified (runtimeSafety : Bool) (allocate : Registry.Allocate σ) (release : Release.External σ)
    (allocator lifetime source oldCapacity capacity length base : Nat) (before : Session σ) (effects : σ) (owner : Allocation)
    (valid : Valid before) (ownerFound : before.memory.heap.lookup lifetime = some owner)
    (ownerType : owner.type = Owner.viewType runtimeSafety) (ownerWritable : owner.writable = true)
    (sourceOwned : Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (oldNonempty : oldCapacity ≠ 0) (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (extent : length ≤ capacity) (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base)
    (loaded : readItems before.memory (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ length))
    (ready : ∀ index, index < length → ∀ slot ∈ expressionSlots,
      ∃ value, Expression.readField before.memory false ⟨source, index * 32⟩ slot.1 = .ok value) :
    ∃ oldCell after, before.memory.heap.lookup source = some oldCell ∧
      run allocate release allocator (Owner.headerAddress ⟨lifetime, 0⟩) ⟨source, 0⟩ oldCapacity capacity before = (.ok (some ()), after) ∧
      Valid after ∧ Release.Owned allocator ⟨before.memory.nextId, 0⟩ capacity after ∧
      after.heap = Compiler.Extraction.Memory.write
        (Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩)) source none ∧
      after.effects = release allocator oldCell.base (oldCapacity * 32) 8 effects ∧
      after.memory.nextId = before.memory.nextId + 1 ∧
      after.memory.nextAddress = max before.memory.nextAddress (base + capacity * 32) ∧
      after.memory.heap.lookup source = none ∧
      readHeader after.memory (Owner.headerAddress ⟨lifetime, 0⟩) =
        .ok (.slice itemsType ⟨before.memory.nextId, 0⟩ length, .scalar (.int false 64 capacity)) ∧
      (∀ index, index < length → Expression.readFields after.memory false ⟨before.memory.nextId, index * 32⟩ =
        Expression.readFields before.memory false ⟨source, index * 32⟩) ∧
      (∀ query, query ≠ source → query ≠ before.memory.nextId → query ≠ lifetime →
        after.memory.heap.lookup query = before.memory.heap.lookup query) := by
  obtain ⟨reserved, allocated, reservedValid, targetOwned, memory, heap, reached⟩ :=
    Registry.verified allocate allocator capacity base before effects valid nonempty size response fits
  obtain ⟨root, ⟨cells, vector⟩, oldCell, sourceFound, sourceType, sourceWritable, sourcePersistent⟩ := sourceOwned
  have sourceOlder := (valid_lookup before.memory source oldCell valid.memory sourceFound).1
  have ownerOlder := (valid_lookup before.memory lifetime owner valid.memory ownerFound).1
  have frame (query : Nat) (apart : query ≠ before.memory.nextId) :
      reserved.memory.heap.lookup query = before.memory.heap.lookup query := by
    rw [memory, RegionAllocation.extend_lookup, if_neg (Ne.symm apart)]
  have sourceReserved : Release.Owned allocator ⟨source, 0⟩ oldCapacity reserved := by
    refine ⟨root, ⟨cells, ?_⟩, oldCell, (frame source (by omega)).trans sourceFound, sourceType, sourceWritable, sourcePersistent⟩
    simpa only [Compiler.Extraction.Memory.Vector, heap, Compiler.Extraction.Memory.write, if_neg (show source ≠ before.memory.nextId by omega)] using vector
  have reads (index offset : Nat) := RegisteredCopy.read_field_frame before.memory reserved.memory ⟨source, index * 32⟩ offset
    (frame source (by omega))
  obtain ⟨releasedCell, after, releasedFound, relocated, finalValid, finalOwned, finalHeap, finalEffects,
      finalId, finalAddress, dead, header, fields, kept⟩ :=
    Relocation.verified runtimeSafety release allocator lifetime source before.memory.nextId oldCapacity capacity length reserved owner
      reservedValid ((frame lifetime (by omega)).trans ownerFound) ownerType ownerWritable sourceReserved targetOwned oldNonempty
      (by omega) extent ((readField_eq_of_lookup before.memory reserved.memory _ itemsOffset (frame lifetime (by omega))).trans loaded)
      (fun index inside slot member => by
        obtain ⟨value, read⟩ := ready index inside slot member
        exact ⟨value, (reads index slot.1).trans read⟩)
  have same : releasedCell = oldCell := Option.some.inj (releasedFound.symm.trans ((frame source (by omega)).trans sourceFound))
  subst releasedCell
  refine ⟨oldCell, after, sourceFound, of_steps allocate release allocator _ _ _ oldCapacity capacity _ _ _ allocated relocated,
    finalValid, finalOwned, ?_, ?_, ?_, ?_, dead, header, ?_, ?_⟩
  · rw [finalHeap, heap]
  · rw [finalEffects, reached]
  · rw [finalId, memory]; rfl
  · rw [finalAddress, memory]; rfl
  · intro index inside
    exact (fields index inside).trans (RepresentativeArray.Copy.readFields_eq_of_slots _ _ _ _ (fun slot _ => reads index slot.1))
  · intro query oldApart newApart ownerApart
    exact (kept query oldApart newApart ownerApart).trans (frame query newApart)

end Compiler.Extraction.RepresentativeArray.Backing.Fallback
