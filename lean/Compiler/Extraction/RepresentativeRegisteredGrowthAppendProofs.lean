/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredGrowthAppend

namespace Compiler.Extraction.RepresentativeArray.Append.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The common append continuation is recovered from the existing spare
executor after capacity selection. Its descriptor stores are not reimplemented. -/
theorem spare_continuation (runtimeSafety : Bool) (before after : Session σ)
    (allocator owner lifetime capacity : Nat) (ownerCell : Allocation) (cells : List Storage.Cell) (cell : Storage.Cell)
    (allocate : Backing.Registry.Allocate σ) (valid : Valid before)
    (found : before.memory.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : cells.length < capacity) (width : Append.nextLength cells.length < addressLimit)
    (executed : Execution.ownerRun runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (allocate allocator) before.effects =
        ((.ok (some ()), after.memory), after.effects)) :
    Execution.assumeCapacity before.memory (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
      cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat = (.ok (), after.memory) := by
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory found typed
  have length := Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell ⟨lifetime, 0⟩ cells.length valid.memory found typed items
  have capacity := Capacity.ensure_unchanged before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity (Append.nextLength cells.length)
    (allocate allocator) before.effects width count (by simp only [Append.nextLength]; omega)
  simp only [Execution.ownerRun, Execution.ownerWithCapacity, selected, Execution.runWithCapacity, length,
    Int.toNat_natCast, if_neg (Nat.not_le.mpr width), capacity] at executed
  generalize assigned : Execution.assumeCapacity before.memory (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat = result at executed ⊢
  rcases result with ⟨outcome, memory⟩
  cases outcome with
  | error fault => cases executed
  | ok value =>
    cases value
    have same := congrArg (fun result => result.1.2) executed
    exact congrArg (fun state => (Except.ok (), state)) same

/-- Spare capacity bypasses both allocation adapters and preserves the exact
shared descriptor execution, including rejection and private effects. -/
theorem spare_same (runtimeSafety : Bool) (before : Session σ)
    (allocator owner lifetime capacity : Nat) (ownerCell : Allocation) (cells : List Storage.Cell) (cell : Storage.Cell)
    (allocate : Backing.Registry.Allocate σ) (calls : Growth.Registered.Callbacks σ) (valid : Valid before)
    (found : before.memory.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : cells.length < capacity) (width : Append.nextLength cells.length < addressLimit) :
    runWithGrowth calls runtimeSafety allocate allocator owner cells cell before =
      run runtimeSafety allocate allocator owner cells cell before := by
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory found typed
  have length := Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell ⟨lifetime, 0⟩ cells.length valid.memory found typed items
  have capacity := Capacity.ensure_unchanged before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity (Append.nextLength cells.length)
    (allocate allocator) before.effects width count (by simp only [Append.nextLength]; omega)
  have growing := Capacity.Registered.unchanged calls allocate allocator _ _ (Owner.headerAddress ⟨owner, 0⟩) before
    width count (by simp only [Append.nextLength]; omega)
  simp only [run, runWithGrowth, Execution.ownerRun, Execution.ownerWithCapacity, selected,
    Execution.runWithCapacity, length, Int.toNat_natCast, if_neg (Nat.not_le.mpr width),
    capacity, growingCapacity, growing, Except.mapError]
  generalize Execution.assumeCapacity before.memory (Owner.headerAddress ⟨owner, 0⟩)
    ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat = result
  rcases result with ⟨result, memory⟩
  cases result with
  | error fault => rfl
  | ok value => cases value; rfl

/-- Source-selected nonempty growth followed by the actual append derives its
new vector, every native row/query, new backing ownership and old backing death.
Only initial correspondence and the actual allocator response are premises. -/
theorem growing_verified (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (release : Backing.Release.External σ)
    (allocator owner source oldCapacity capacity base context returnAddress : Nat) (before : Session σ) (effects : σ)
    (ownerCell : Allocation) (cells : List Storage.Cell) (cell : Storage.Cell) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell) (ownerType : ownerCell.type = Owner.viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true) (sourceOwned : Backing.Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (vector : Compiler.Extraction.Memory.Vector allocator before.heap source cells)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selectedCapacity : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < addressLimit) (room : cells.length < 2 ^ 32 - 1) (argumentsValid : cell.arguments.length < addressLimit)
    (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base)
    (loaded : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ cells.length))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (represented : DescriptorRelation.Prefix before.memory source cells)
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ oldCell after,
      before.memory.heap.lookup source = some oldCell ∧
      runWithGrowth ⟨.noRemap context returnAddress, release⟩ runtimeSafety allocate allocator owner cells cell before = (.ok true, after) ∧
      Valid after ∧ Compiler.Extraction.Memory.Vector allocator after.heap before.memory.nextId (cells ++ [cell]) ∧
      Backing.Release.Owned allocator ⟨before.memory.nextId, 0⟩ capacity after ∧
      after.heap source = none ∧ after.memory.heap.lookup source = none ∧
      after.effects = release allocator oldCell.base (oldCapacity * 32) 8 effects ∧
      after.memory.nextId = before.memory.nextId + 1 ∧
      after.memory.nextAddress = max before.memory.nextAddress (base + capacity * 32) ∧
      (∀ query, query ≠ source → query ≠ before.memory.nextId → after.heap query = before.heap query) ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨before.memory.nextId, 0⟩ (cells ++ [cell]).length, .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix after.memory before.memory.nextId (cells ++ [cell]) ∧
      (∀ id, representativeFields after.memory (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run (cells ++ [cell]) id).map (DescriptorRelation.values id.toNat))) ∧
      (∀ previous ∈ cells, Compiler.Extraction.Memory.Resident allocator before.heap previous →
        Compiler.Extraction.Memory.Resident allocator after.heap previous) ∧
      (∃ finalOwner, after.memory.heap.lookup owner = some finalOwner ∧ ownerCell.SameShape finalOwner) ∧
      (∀ query, query ≠ source → query ≠ before.memory.nextId → query ≠ owner →
        after.memory.heap.lookup query = before.memory.heap.lookup query) := by
  have width : Append.nextLength cells.length < addressLimit := by
    simp only [Append.nextLength, addressLimit]; omega
  have enough : Append.nextLength cells.length ≤ capacity := selectedCapacity ▸ Capacity.grow_sufficient _ width
  have spare : cells.length < capacity := by simp only [Append.nextLength] at enough; omega
  have positive : capacity ≠ 0 := by omega
  have growth := Growth.Registered.fallback_execution runtimeSafety allocate release allocator owner source oldCapacity capacity cells.length
    context returnAddress before ownerCell valid ownerFound ownerType sourceOwned oldNonempty (by omega) (by omega) loaded count unlocked
  obtain ⟨oldCell, raw, ready, oldFound, grown, memory, reached, rawHeap, moved, effectsReached, readyValid, readyVector,
      readyOwned, oldDead, nativeDead, readyHeader, readyPrefix, nextId, nextAddress, _, residents⟩ :=
    DescriptorRelation.fallback_registered runtimeSafety allocate release allocator owner source oldCapacity capacity base before effects ownerCell
      cells valid ownerFound ownerType ownerWritable sourceOwned vector oldNonempty positive size (by omega) response fits loaded represented
  have ownerShape := Backing.Fallback.owner_shape runtimeSafety allocate release allocator owner oldCapacity capacity ⟨source, 0⟩ before ownerCell
    valid positive ownerFound ownerType
  rw [grown] at ownerShape
  obtain ⟨readyOwner, readyFound, shape⟩ := ownerShape
  rw [← memory] at readyFound
  obtain ⟨_, _, backing, backingFound, backingType, backingWritable, backingPersistent⟩ := readyOwned
  obtain ⟨after, appended, finalHeap, finalEffects, finalValid, finalVector, finalHeader, finalPrefix, queries, finalResidents⟩ :=
    DescriptorRelation.spare_registered runtimeSafety ready allocator owner before.memory.nextId capacity readyOwner backing cells cell (allocate allocator)
      readyValid readyFound (shape.2.1.trans ownerType) (shape.2.2.1.trans ownerWritable) backingFound backingType backingWritable
      (readHeader_items _ _ _ _ readyHeader) (Append.readHeader_parts _ _ _ _ readyHeader).2 readyVector readyPrefix spare room argumentsValid
  have continuation := spare_continuation runtimeSafety ready after allocator owner before.memory.nextId capacity readyOwner cells cell allocate
    readyValid readyFound (shape.2.1.trans ownerType) (readHeader_items _ _ _ _ readyHeader) (Append.readHeader_parts _ _ _ _ readyHeader).2 spare width appended
  obtain ⟨native, nativeRun, _, _, _, _, _, _, nativeFrame, _⟩ :=
    Execution.spare_verified runtimeSafety ready.memory owner before.memory.nextId capacity cells.length readyOwner backing
      ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat
      (allocate allocator) ready.effects readyValid.memory readyFound (shape.2.1.trans ownerType) (shape.2.2.1.trans ownerWritable)
      backingFound backingType backingWritable (readHeader_items _ _ _ _ readyHeader) (Append.readHeader_parts _ _ _ _ readyHeader).2
      spare argumentsValid (WordArray.number_valid (Storage.idFor cells)) (WordArray.number_valid cell.sequence)
  have sameNative : native = after.memory := congrArg (fun result => result.1.2) (nativeRun.symm.trans appended)
  subst native
  have growthFrame := (Backing.Fallback.storage runtimeSafety allocate release allocator owner oldCapacity capacity ⟨source, 0⟩ before
    ownerCell valid positive ownerFound ownerType).2.2
  rw [grown] at growthFrame
  have fresh := valid.injected.fresh valid.memory
  have apart : source ≠ before.memory.nextId := by
    intro same; have v := vector; rw [Compiler.Extraction.Memory.Vector, same, fresh] at v; contradiction
  have readyHeap := Except.ok.inj ((Compiler.Extraction.Memory.move_vector_eq allocator before.heap source before.memory.nextId cells vector fresh).symm.trans moved)
  have finalRaw : after.heap = Compiler.Extraction.Memory.write raw.heap before.memory.nextId (some ⟨allocator, .representatives (cells ++ [cell])⟩) := by
    rw [finalHeap, ← readyHeap, rawHeap]
    funext query
    simp only [Compiler.Extraction.Memory.write]
    split <;> rfl
  have admitted : admit allocator before.memory.nextId cells {before with heap := raw.heap} = .ok () := by
    simp only [admit, rawHeap, Compiler.Extraction.Memory.write, if_neg (Ne.symm apart), ↓reduceIte]
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory ownerFound ownerType
  have length := Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell ⟨source, 0⟩ cells.length valid.memory ownerFound ownerType loaded
  have ensured := Capacity.Registered.growing (⟨.noRemap context returnAddress, release⟩ : Growth.Registered.Callbacks σ)
    allocate allocator oldCapacity (Append.nextLength cells.length) (Owner.headerAddress ⟨owner, 0⟩) before width count full
  rw [← selectedCapacity, growth, grown] at ensured
  have executed : runWithGrowth ⟨.noRemap context returnAddress, release⟩ runtimeSafety allocate allocator owner cells cell before = (.ok true, after) := by
    simp only [runWithGrowth, Execution.ownerWithCapacity, selected, Execution.runWithCapacity, length, Int.toNat_natCast,
      if_neg (Nat.not_le.mpr width), growingCapacity, ensured, Except.mapError, ← memory, ← reached, continuation,
      finish, readHeader_items _ _ _ _ finalHeader, List.length_append, List.length_singleton, and_self, ↓reduceIte, admitted]
    cases after
    dsimp only at finalRaw finalEffects
    simp only [← finalRaw, ← finalEffects]
  have nativeShape := Execution.assumeCapacity_storage ready.memory (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩
    ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat readyValid.memory
  rw [continuation] at nativeShape
  obtain ⟨finalBacking, finalFound, backingShape⟩ := nativeShape.2.1 before.memory.nextId backing backingFound
  refine ⟨oldCell, after, oldFound, executed, finalValid, finalVector,
    ⟨rfl, ⟨cells ++ [cell], finalVector⟩, finalBacking, finalFound, backingShape.2.1.trans backingType,
      backingShape.2.2.1.trans backingWritable, backingShape.2.2.2.trans backingPersistent⟩,
    ?_, ?_, finalEffects.trans effectsReached, nativeShape.2.2.1.trans nextId,
    nativeShape.2.2.2.trans nextAddress, ?_, finalHeader, finalPrefix, queries, ?_, ?_, ?_⟩
  · rw [finalHeap]; simpa only [Compiler.Extraction.Memory.write, if_neg apart] using oldDead
  · have missing := Execution.assumeCapacity_missing ready.memory (Owner.headerAddress ⟨owner, 0⟩) ⟨cell.itemAddress, 0⟩
      ⟨cell.argumentsAddress, 0⟩ cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat source readyValid.memory nativeDead
    simpa only [continuation] using missing
  · intro query oldApart newApart
    simp only [finalRaw, rawHeap, Compiler.Extraction.Memory.write, if_neg oldApart, if_neg newApart]
  · intro previous member resident
    exact finalResidents previous member (residents previous resident)
  · obtain ⟨finalOwner, found, finalShape⟩ := nativeShape.2.1 owner readyOwner readyFound
    exact ⟨finalOwner, found, shape.trans finalShape⟩
  · intro query oldApart newApart ownerApart
    exact (nativeFrame query ownerApart newApart).trans
      ((congrArg (fun state => state.heap.lookup query) memory).trans (growthFrame query oldApart newApart ownerApart))

/-- Nonempty growth OOM is derived from the actual capacity selection, refused
remap and allocator response. Neither heap changes; allocator-private effects
are retained. No descriptor store, backing release or registry finish runs. -/
theorem growing_oom (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ)
    (allocator owner source oldCapacity capacity context returnAddress : Nat)
    (before : Session σ) (effects : σ) (ownerCell : Allocation)
    (cells : List Storage.Cell) (cell : Storage.Cell) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerType : ownerCell.type = Owner.viewType runtimeSafety)
    (sourceOwned : Backing.Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selectedCapacity : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (response : allocate allocator (capacity * 32) 8 before.effects = (none, effects))
    (loaded : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ cells.length))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    runWithGrowth ⟨.noRemap context returnAddress, release⟩ runtimeSafety allocate allocator owner cells cell before =
      (.ok false, {before with effects}) := by
  have width : Append.nextLength cells.length < addressLimit := by
    simp only [Append.nextLength, addressLimit]; omega
  have enough : Append.nextLength cells.length ≤ capacity := selectedCapacity ▸ Capacity.grow_sufficient _ width
  have fallback := Growth.Registered.fallback_execution runtimeSafety allocate release allocator owner source oldCapacity capacity cells.length
    context returnAddress before ownerCell valid ownerFound ownerType sourceOwned oldNonempty (by omega) (by omega) loaded count unlocked
  have failed := Backing.Fallback.oom_verified allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) ⟨source, 0⟩
    oldCapacity capacity before effects valid.memory (by simp only [Append.nextLength] at enough; omega) size response
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory ownerFound ownerType
  have length := Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell ⟨source, 0⟩ cells.length valid.memory ownerFound ownerType loaded
  have ensured := Capacity.Registered.growing (⟨.noRemap context returnAddress, release⟩ : Growth.Registered.Callbacks σ)
    allocate allocator oldCapacity (Append.nextLength cells.length) (Owner.headerAddress ⟨owner, 0⟩) before width count full
  rw [← selectedCapacity, fallback, failed] at ensured
  simp only [runWithGrowth, Execution.ownerWithCapacity, selected, Execution.runWithCapacity, length,
    Int.toNat_natCast, if_neg (Nat.not_le.mpr width), growingCapacity, ensured, Except.mapError]

/-- Spare capacity bypasses allocation and preserves the exact descriptor
execution for either configured allocator, including rejected outcomes. -/
theorem spare_allocators (runtimeSafety : Bool) (before : Session σ)
    (allocator owner lifetime capacity : Nat) (ownerCell : Allocation) (cells : List Storage.Cell) (cell : Storage.Cell)
    (allocate other : Backing.Registry.Allocate σ) (valid : Valid before)
    (found : before.memory.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (items : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : cells.length < capacity) (width : Append.nextLength cells.length < addressLimit) :
    run runtimeSafety allocate allocator owner cells cell before =
      run runtimeSafety other allocator owner cells cell before := by
  have selected := Owner.root_header_pointer runtimeSafety before.memory owner ownerCell true valid.memory found typed
  have length := Execution.owner_length_from_items runtimeSafety before.memory owner ownerCell ⟨lifetime, 0⟩ cells.length valid.memory found typed items
  have capacity1 := Capacity.ensure_unchanged before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity (Append.nextLength cells.length)
    (allocate allocator) before.effects width count (by simp only [Append.nextLength]; omega)
  have capacity2 := Capacity.ensure_unchanged before.memory (Owner.headerAddress ⟨owner, 0⟩) capacity (Append.nextLength cells.length)
    (other allocator) before.effects width count (by simp only [Append.nextLength]; omega)
  simp only [run, Execution.ownerRun, Execution.ownerWithCapacity, selected,
    Execution.runWithCapacity, length, Int.toNat_natCast, if_neg (Nat.not_le.mpr width), capacity1, capacity2]


end Compiler.Extraction.RepresentativeArray.Append.Registered
