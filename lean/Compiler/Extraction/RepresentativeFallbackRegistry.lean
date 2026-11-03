/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorPreservation
import Compiler.Extraction.MemoryProofs

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Pair the actual allocation fallback with the existing logical vector move.
The native adapter returns provisional registry storage; publishing its copied
cells is a refinement witness with identical memory and effects. Initial vector
contents must match the descriptor relation. No successful final read, final
allocation or logical move is a premise. The saved old view remains evaluated;
this does not supply preservation across a preceding remap. -/
theorem fallback_registered (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (release : Backing.Release.External σ)
    (allocator owner source oldCapacity capacity base : Nat) (before : Session σ) (effects : σ) (ownerCell : Allocation)
    (cells : List Storage.Cell) (valid : Valid before) (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerType : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (sourceOwned : Backing.Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (vector : Compiler.Extraction.Memory.Vector allocator before.heap source cells)
    (oldNonempty : oldCapacity ≠ 0) (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (extent : cells.length ≤ capacity)
    (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base)
    (loaded : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ cells.length))
    (represented : Prefix before.memory source cells) :
    ∃ oldCell raw after,
      before.memory.heap.lookup source = some oldCell ∧
      Backing.Fallback.run allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) ⟨source, 0⟩ oldCapacity capacity before =
        (.ok (some ()), raw) ∧
      after.memory = raw.memory ∧ after.effects = raw.effects ∧
      raw.heap = Compiler.Extraction.Memory.write
        (Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩)) source none ∧
      Compiler.Extraction.Memory.moveVector before.heap allocator source before.memory.nextId true = .ok after.heap ∧
      after.effects = release allocator oldCell.base (oldCapacity * 32) 8 effects ∧
      Valid after ∧ Compiler.Extraction.Memory.Vector allocator after.heap before.memory.nextId cells ∧
      Backing.Release.Owned allocator ⟨before.memory.nextId, 0⟩ capacity after ∧
      after.heap source = none ∧ after.memory.heap.lookup source = none ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨before.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      Prefix after.memory before.memory.nextId cells ∧
      after.memory.nextId = before.memory.nextId + 1 ∧ after.memory.nextAddress = max before.memory.nextAddress (base + capacity * 32) ∧
      (∀ id, representativeFields after.memory (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run cells id).map (values id.toNat))) ∧
      (∀ previous, Compiler.Extraction.Memory.Resident allocator before.heap previous →
        Compiler.Extraction.Memory.Resident allocator after.heap previous) := by
  obtain ⟨oldCell, raw, oldFound, executed, rawValid, rawOwned, heap, reached, nextId, nextAddress, dead, header, fields, _⟩ :=
    Backing.Fallback.verified runtimeSafety allocate release allocator owner source oldCapacity capacity cells.length base before effects ownerCell
      valid ownerFound ownerType ownerWritable sourceOwned oldNonempty nonempty size extent response fits loaded
      (source_ready _ _ _ represented)
  have fresh := valid.injected.fresh valid.memory
  have apart : source ≠ before.memory.nextId := by
    intro same
    have registered := vector
    dsimp only [Compiler.Extraction.Memory.Vector] at registered
    rw [same, fresh] at registered
    contradiction
  let after : Session σ := { raw with
    heap := Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩) }
  have published : after.heap = Compiler.Extraction.Memory.write
      (Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives cells⟩)) source none := by
    funext query
    simp only [after, heap, Compiler.Extraction.Memory.write]
    by_cases old : query = source
    · subst query; simp [apart]
    · by_cases new : query = before.memory.nextId <;> simp [old, new, Ne.symm apart]
  obtain ⟨_, _, backing, backingFound, backingType, backingWritable, backingPersistent⟩ := rawOwned
  have finalVector : Compiler.Extraction.Memory.Vector allocator after.heap before.memory.nextId cells :=
    Compiler.Extraction.Memory.write_same _ _ _
  have finalPrefix := copied _ _ _ _ _ represented fields
  refine ⟨oldCell, raw, after, oldFound, executed, rfl, rfl, heap, ?_, reached,
    Backing.Registry.vector_write_valid raw allocator before.memory.nextId backing cells rawValid backingFound backingPersistent,
    finalVector, ⟨rfl, ⟨cells, finalVector⟩, backing, backingFound, backingType, backingWritable, backingPersistent⟩,
    ?_, dead, header, finalPrefix, nextId, nextAddress, ?_, ?_⟩
  · rw [published]
    exact Compiler.Extraction.Memory.move_vector_eq allocator before.heap source before.memory.nextId cells vector fresh
  · rw [published]; exact Compiler.Extraction.Memory.write_same _ _ _
  · intro id
    exact query after.memory _ before.memory.nextId capacity backing cells id rawValid.memory
      (readHeader_items _ _ _ _ header) backingFound backingType backingWritable extent finalPrefix
  · intro previous resident
    rw [published]
    have allocated := Compiler.Extraction.Memory.resident_fresh_write allocator before.heap previous resident before.memory.nextId fresh
      (some ⟨allocator, .representatives cells⟩)
    exact Compiler.Extraction.Memory.resident_vector_write allocator _ previous allocated source cells
      (by simpa only [Compiler.Extraction.Memory.Vector, Compiler.Extraction.Memory.write, if_neg apart] using vector) none

/-- Actual allocator OOM agrees with logical move failure and preserves the old
registered vector. Allocation-private effects are reached; no release or
logical publication follows. A malformed header is still not evaluated. -/
theorem fallback_registry_oom (allocate : Backing.Registry.Allocate σ) (release : Backing.Release.External σ)
    (allocator source oldCapacity capacity : Nat) (header oldData : Address) (before : Session σ) (effects : σ)
    (cells : List Storage.Cell) (valid : Valid before)
    (vector : Compiler.Extraction.Memory.Vector allocator before.heap source cells)
    (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (response : allocate allocator (capacity * 32) 8 before.effects = (none, effects)) :
    Backing.Fallback.run allocate release allocator header oldData oldCapacity capacity before = (.ok none, {before with effects}) ∧
      Compiler.Extraction.Memory.moveVector before.heap allocator source before.memory.nextId false = .error .outOfMemory ∧
      Valid ({before with effects} : Session σ) ∧
      Compiler.Extraction.Memory.Vector allocator ({before with effects} : Session σ).heap source cells ∧
      before.heap before.memory.nextId = none :=
  ⟨Backing.Fallback.oom_verified allocate release allocator header oldData oldCapacity capacity before effects valid.memory nonempty size response,
    Compiler.Extraction.Memory.move_vector_oom allocator before.heap source before.memory.nextId cells vector,
    ⟨valid.memory, valid.related, valid.injected⟩, vector, valid.injected.fresh valid.memory⟩

end Compiler.Extraction.RepresentativeArray.DescriptorRelation
