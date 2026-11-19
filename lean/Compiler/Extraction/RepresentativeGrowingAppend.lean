/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeAppendExecution

namespace Compiler.Extraction.RepresentativeArray.Append.Execution
open Compiler.ZigAir.Memory

/-- Recover the length leaf from a previously checked complete items read.
The executable length reader itself neither reads the pointer leaf nor
requires live backing. The captured owner's geometry derives its selector. -/
theorem owner_length_from_items (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (data : Address) (length : Nat) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (loaded : readItems state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType data length)) :
    readField state (Owner.headerAddress ⟨lifetime, 0⟩) lengthOffset = .ok (.scalar (.int false 64 length)) := by
  have header : Owner.headerAddress ⟨lifetime, 0⟩ = ⟨lifetime, Owner.representativesOffset⟩ := rfl
  rw [header] at loaded ⊢
  have fields := Owner.root_header_fields runtimeSafety state lifetime cell false initial found typed
  rw [header] at fields
  have parent := root_access state lifetime cell (Owner.layout runtimeSafety) false initial found
    (typed ▸ Owner.view_layout_checked runtimeSafety) (by cases runtimeSafety <;> decide) (by simp)
  have headerAccess := Owner.header_region_access runtimeSafety state ⟨lifetime, 0⟩ cell false parent
  have declared : acceptsView cell.type (Owner.headerAddress ⟨lifetime, 0⟩).offset allocationType = true := by
    simpa only [typed, Owner.headerAddress, Nat.zero_add] using Owner.header_view_checked runtimeSafety
  have selector := fieldPointer_of_access state (Owner.headerAddress ⟨lifetime, 0⟩) cell allocationType usize
    Owner.representativesLayout lengthOffset false false Owner.header_layout_checked headerAccess declared length_type_checked
  rw [header] at selector
  have raw : load state (.pointer (.pointer false false itemsType) ⟨lifetime, Owner.representativesOffset + itemsOffset⟩) =
      .ok (.slice itemsType data length) := by
    simpa only [readItems, readField, fields.1, bind, Except.bind] using loaded
  cases accessed : access state ⟨lifetime, Owner.representativesOffset + itemsOffset⟩ ⟨16, 8⟩ false with
  | error fault => simp [load, itemsType, Ty.layout, accessed, bind, Except.bind] at raw
  | ok owner =>
    have same := Option.some.inj (((access_success_region state _ _ false owner accessed).1).symm.trans found)
    subst owner
    have read : cell.cells.read cell.type (Owner.representativesOffset + itemsOffset) itemsType =
        .ok (.slice itemsType data length) := by
      simpa only [load, itemsType, Ty.layout, Ty.leafLayout, accessed, bind, Except.bind, readCell] using raw
    have parts := cell.cells.read_slice_parts cell.type (Owner.representativesOffset + itemsOffset) true elementType data length read
    have lengthAccess := access_subregion state ⟨lifetime, Owner.representativesOffset + itemsOffset⟩ ⟨16, 8⟩ ⟨8, 8⟩ 8 false cell
      accessed (by decide) (by decide) (by decide) (by decide)
    have view : acceptsView cell.type (Owner.representativesOffset + lengthOffset) usize = true := by
      rw [typed]
      cases runtimeSafety <;> decide
    simp only [lengthOffset, usize] at view
    simp only [Nat.add_assoc] at lengthAccess
    have lengthRead : load state (.pointer (.pointer false false usize) ⟨lifetime, Owner.representativesOffset + lengthOffset⟩) =
        .ok (.scalar (.int false 64 length)) := by
      simpa only [load, usize, Ty.layout, Ty.leafLayout, lengthOffset, Nat.add_assoc, lengthAccess, bind, Except.bind,
        readCell, Cells.read, view, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using parts.2.2
    simp only [readField, selector, bind, Except.bind, lengthRead]

/-- First source-selected growth and append are the same reached execution.
Initial empty owner storage, evaluated values and the actual allocator response
derive capacity five, the first initialized descriptor and complete readback.
Neither the grown state nor any successful store is a premise. -/
theorem first_verified (runtimeSafety : Bool) (state : State) (owner : Nat) (cell : Allocation)
    (sentinel itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int) (base : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (initial : state.valid = true) (found : state.heap.lookup owner = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true)
    (items : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true)
    (response : allocate 160 8 effects = (some base, reached)) (fits : RegionAllocation.Fits state ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader state (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ after, ownerRun runtimeSafety state ⟨owner, 0⟩ itemAddress argumentsAddress argumentsLength id sequence allocate effects =
        ((.ok (some ()), after), reached) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨state.nextId, 0⟩ 1, .scalar (.int false 64 5)) ∧
      Expression.readFields after false ⟨state.nextId, 0⟩ = .ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] ∧
      after.nextId = state.nextId + 1 ∧ after.nextAddress = max state.nextAddress (base + 160) ∧
      (∀ other, other ≠ owner → other ≠ state.nextId → after.heap.lookup other = state.heap.lookup other) := by
  have lengthRead := owner_length_from_items runtimeSafety state owner cell sentinel 0 initial found typed items
  obtain ⟨ready, ensured, readyValid, readyShape, readyHeader, backing, nextId, nextAddress, growthFrame⟩ :=
    Capacity.first_verified runtimeSafety state owner cell sentinel 1 base allocate effects reached initial found typed writable items capacity
      (by decide) (by decide) (by decide) response fits unlocked
  obtain ⟨readyOwner, readyFound, ownerShape⟩ := readyShape owner cell found
  have readyTyped := ownerShape.2.1.trans typed
  have readyWritable := ownerShape.2.2.1.trans writable
  have readyParts := readHeader_parts ready (Owner.headerAddress ⟨owner, 0⟩) _ _ readyHeader
  obtain ⟨after, appended, valid, shape, finalHeader, fields, finalId, finalAddress, appendFrame, _⟩ :=
    Owner.appendWithoutGrowth_framed runtimeSafety ready owner state.nextId 5 0 readyOwner
      ⟨base, Backing.type 5, [], true, false⟩ itemAddress argumentsAddress argumentsLength id sequence readyValid readyFound readyTyped readyWritable
      backing rfl rfl readyParts.1 readyParts.2 (by decide) argumentsValid idValid sequenceValid
  have selectedReady := Owner.root_header_pointer runtimeSafety ready owner readyOwner true readyValid readyFound readyTyped
  have pureAppend : appendWithoutGrowth ready (Owner.headerAddress ⟨owner, 0⟩) itemAddress argumentsAddress argumentsLength id sequence = .ok after := by
    simpa only [Owner.appendWithoutGrowth, selectedReady, bind, Except.bind] using appended
  have readyLength := owner_length_from_items runtimeSafety ready owner readyOwner ⟨state.nextId, 0⟩ 0 readyValid readyFound readyTyped readyParts.1
  have reachedAppend := assumeCapacity_of_spare ready after (Owner.headerAddress ⟨owner, 0⟩) ⟨state.nextId, 0⟩ 0 5
    itemAddress argumentsAddress argumentsLength id sequence readyHeader readyLength pureAppend
  have selected := Owner.root_header_pointer runtimeSafety state owner cell true initial found typed
  refine ⟨after, ?_, valid, readyShape.trans shape, finalHeader, fields, finalId.trans nextId, finalAddress.trans nextAddress, ?_⟩
  · simp only [ownerRun, ownerWithCapacity, selected, runWithCapacity, lengthRead, Int.toNat_natCast, nextLength, Nat.zero_add,
      if_neg (by decide : ¬1 ≥ addressLimit), ensured, reachedAppend]
  · intro other outsideOwner outsideBacking
    exact (appendFrame other outsideOwner outsideBacking).trans (growthFrame other outsideOwner outsideBacking)

/-- First-append OOM skips both the length mutation and every descriptor store.
The allocator's private effects are retained, including for a readonly owner. -/
theorem first_oom (runtimeSafety : Bool) (state : State) (owner : Nat) (cell : Allocation)
    (sentinel itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (initial : state.valid = true) (found : state.heap.lookup owner = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety)
    (items : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (response : allocate 160 8 effects = (none, reached))
    (unlocked : Owner.NativeLock.checkHeader state (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ownerRun runtimeSafety state ⟨owner, 0⟩ itemAddress argumentsAddress argumentsLength id sequence allocate effects =
      ((.ok none, state), reached) := by
  have selected := Owner.root_header_pointer runtimeSafety state owner cell true initial found typed
  have lengthRead := owner_length_from_items runtimeSafety state owner cell sentinel 0 initial found typed items
  have pointerRead := readItemsData_from_loaded runtimeSafety state owner cell sentinel 0 initial found typed items
  have ensured := Capacity.first_oom state (Owner.headerAddress ⟨owner, 0⟩) sentinel 1 allocate effects reached
    initial pointerRead capacity (by decide) (by decide) (by decide) response unlocked
  simp only [ownerRun, ownerWithCapacity, selected, runWithCapacity, lengthRead, Int.toNat_natCast, nextLength, Nat.zero_add,
    if_neg (by decide : ¬1 ≥ addressLimit), ensured]

/-- Ready backing uses the same complete execution, with the capacity call
returning before any allocator effect. The old append proof derives its stores;
the reached endpoint adds no successful-final-state premise. -/
theorem spare_verified (runtimeSafety : Bool) (state : State) (owner lifetime capacity length : Nat)
    (ownerCell backing : Allocation) (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (allocate : RegionAllocation.Allocator σ) (effects : σ)
    (initial : state.valid = true)
    (ownerFound : state.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (capacityRead : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : length < capacity) (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true) :
    ∃ after, ownerRun runtimeSafety state ⟨owner, 0⟩ itemAddress argumentsAddress argumentsLength id sequence allocate effects =
        ((.ok (some ()), after), effects) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (nextLength length), .scalar (.int false 64 capacity)) ∧
      Expression.readFields after false ⟨lifetime, length * 32⟩ = .ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ owner → other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) ∧
      Owner.NativeLock.checkHeader after (Owner.headerAddress ⟨owner, 0⟩) =
        Owner.NativeLock.checkHeader state (Owner.headerAddress ⟨owner, 0⟩) := by
  obtain ⟨after, appended, valid, shape, header, fields, nextId, nextAddress, frame, lock⟩ :=
    Owner.appendWithoutGrowth_framed runtimeSafety state owner lifetime capacity length ownerCell backing
      itemAddress argumentsAddress argumentsLength id sequence initial ownerFound ownerTyped ownerWritable backingFound backingTyped
      backingWritable itemsRead capacityRead spare argumentsValid idValid sequenceValid
  have selected := Owner.root_header_pointer runtimeSafety state owner ownerCell true initial ownerFound ownerTyped
  have pureAppend : appendWithoutGrowth state (Owner.headerAddress ⟨owner, 0⟩) itemAddress argumentsAddress argumentsLength id sequence = .ok after := by
    simpa only [Owner.appendWithoutGrowth, selected, bind, Except.bind] using appended
  have lengthRead := owner_length_from_items runtimeSafety state owner ownerCell ⟨lifetime, 0⟩ length initial ownerFound ownerTyped itemsRead
  have reachedAppend := assumeCapacity_of_spare state after (Owner.headerAddress ⟨owner, 0⟩) ⟨lifetime, 0⟩ length capacity
    itemAddress argumentsAddress argumentsLength id sequence (readHeader_from_parts state _ _ _ itemsRead capacityRead) lengthRead pureAppend
  have bounded := nextLength_bounded state lifetime capacity length backing initial backingFound backingTyped spare
  have ensured := Capacity.ensure_unchanged state (Owner.headerAddress ⟨owner, 0⟩) capacity (nextLength length) allocate effects
    bounded capacityRead (by simp only [nextLength]; omega)
  refine ⟨after, ?_, valid, shape, header, fields, nextId, nextAddress, frame, lock⟩
  simp only [ownerRun, ownerWithCapacity, selected, runWithCapacity, lengthRead, Int.toNat_natCast,
    if_neg (Nat.not_le.mpr bounded), ensured, reachedAppend]

end Compiler.Extraction.RepresentativeArray.Append.Execution
