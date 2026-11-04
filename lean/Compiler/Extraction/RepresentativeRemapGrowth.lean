/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRemap
import Compiler.Extraction.RepresentativeArrayGrowth
import Compiler.Extraction.RepresentativeFallbackRegistry
import Compiler.Extraction.RepresentativeFallbackFrame

namespace Compiler.Extraction.RepresentativeArray.Growth.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Continue the same saved-view prefix through admitted remap dispatch. A
refusal enters the existing allocation/copy/full-free/publication executor;
ordinary OOM and semantic rejection retain their actual reached states.
Successful remap callbacks remain unsupported by the captured callback family. -/
def run (callback : Remap.Callback) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ) (allocator : Nat) (header : Address) (capacity : Nat) (before : Session σ) :
    Except Backing.Release.Fault (Option Unit) × Session σ :=
  match prepare before.memory header capacity with
  | .error reason => (.error (.memory reason), before)
  | .ok none => (.ok (some ()), before)
  | .ok (some (data, oldCapacity)) =>
    let (result, reached) := Remap.run callback release allocator data oldCapacity capacity before
    match result with
    | .error reason => (.error reason, reached)
    | .ok none => Backing.Fallback.run allocate release allocator header data oldCapacity capacity reached
    | .ok (some data) =>
      let (result, after) := Publication.Registered.run header data capacity reached
      (result.mapError Compiler.Extraction.Memory.Arguments.ReleaseFault.memory |>.map some, after)

/-- The admitted positive-size execution either stops before changing storage
or reaches the existing fallback from that same initial state. This statement
is derived from callback execution, not an assumed remap frame. -/
theorem reached_cases (callback : Remap.Callback) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ) (allocator : Nat) (header : Address) (capacity : Nat)
    (before : Session σ) (positive : 0 < capacity) :
    (run callback allocate release allocator header capacity before).2 = before ∨
      ∃ data oldCapacity, run callback allocate release allocator header capacity before =
        Backing.Fallback.run allocate release allocator header data oldCapacity capacity before := by
  unfold run
  cases prepared : prepare before.memory header capacity with
  | error reason => exact Or.inl rfl
  | ok value => cases value with
    | none => exact Or.inl rfl
    | some pair =>
      rcases pair with ⟨data, oldCapacity⟩
      dsimp only
      have reached := Remap.positive_reached callback release allocator oldCapacity capacity data before positive
      have refused := Remap.positive_no_success callback release allocator oldCapacity capacity data before positive
      generalize called : Remap.run callback release allocator data oldCapacity capacity before = result at reached refused ⊢
      rcases result with ⟨outcome, after⟩
      dsimp only at reached
      subst after
      cases outcome with
      | error reason => exact Or.inl rfl
      | ok result => cases result with
        | none => exact Or.inr ⟨data, oldCapacity, rfl⟩
        | some target => exact False.elim (refused target rfl)

/-- Offset parent borrows and their complete backing allocations survive every
admitted outcome, including partial copy and publication rejection. -/
theorem parent_borrow (runtimeSafety : Bool) (callback : Remap.Callback) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ) (allocator owner capacity : Nat) (before : Session σ) (ownerCell : Allocation)
    (valid : Valid before) (positive : 0 < capacity)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell) (ownerType : ownerCell.type = Owner.viewType runtimeSafety)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some cell) (typed : cell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    let after := (run callback allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) capacity before).2
    Valid after ∧ after.memory.heap.lookup parent.allocation = some cell ∧ WordArray.Represents after.memory parent values := by
  rcases reached_cases callback allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) capacity before positive with same | ⟨data, oldCapacity, fallback⟩
  · dsimp only; rw [same]; exact ⟨valid, found, represented⟩
  · dsimp only; rw [fallback]
    exact ⟨(Backing.Fallback.storage runtimeSafety allocate release allocator owner oldCapacity capacity data before ownerCell valid
      (by omega) ownerFound ownerType).1,
      Backing.Fallback.parent_borrow runtimeSafety allocate release allocator owner oldCapacity capacity data before ownerCell valid
        (by omega) ownerFound ownerType parent values extent cell found typed represented⟩

/-- Initial native owner/header and backing facts derive the saved full view;
the actual captured callback derives its preservation. No remap result or
post-remap ownership/frame is an input to the fallback connection. -/
theorem fallback_execution (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ) (allocator owner source oldCapacity capacity length context returnAddress : Nat)
    (before : Session σ) (ownerCell : Allocation) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerType : ownerCell.type = Owner.viewType runtimeSafety)
    (sourceOwned : Backing.Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (oldNonempty : oldCapacity ≠ 0) (width : capacity < addressLimit) (short : oldCapacity < capacity)
    (loaded : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ length))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    run (.noRemap context returnAddress) allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) capacity before =
      Backing.Fallback.run allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) ⟨source, 0⟩ oldCapacity capacity before := by
  obtain ⟨backing, found, typed, _, _⟩ := sourceOwned.2.2
  have saved := allocatedSlice_nonempty before.memory _ source oldCapacity backing valid.memory found typed oldNonempty
    (readItemsData_from_loaded runtimeSafety before.memory owner ownerCell _ length valid.memory ownerFound ownerType loaded) count
  have prepared := prepare_growing before.memory _ _ oldCapacity capacity oldCapacity width short count saved unlocked
  have refused := Remap.refuses release allocator context returnAddress oldCapacity capacity ⟨source, 0⟩ before valid sourceOwned (by omega) width
  simp only [run, prepared, refused]

/-- Complete nonempty growth for the admitted refusing callback, including
logical vector relocation and every representative query. The logical update
refines the same native result; no final read, final heap or move is assumed. -/
theorem verified (runtimeSafety : Bool) (allocate : Backing.Registry.Allocate σ) (release : Backing.Release.External σ)
    (allocator owner source oldCapacity capacity base context returnAddress : Nat) (before : Session σ) (effects : σ)
    (ownerCell : Allocation) (cells : List Storage.Cell) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerType : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (sourceOwned : Backing.Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (vector : Compiler.Extraction.Memory.Vector allocator before.heap source cells)
    (oldNonempty : oldCapacity ≠ 0) (short : oldCapacity < capacity) (size : capacity * 32 < addressLimit)
    (extent : cells.length ≤ capacity)
    (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base)
    (loaded : readItems before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ cells.length))
    (count : readField before.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (represented : DescriptorRelation.Prefix before.memory source cells)
    (unlocked : Owner.NativeLock.checkHeader before.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    ∃ oldCell raw after,
      before.memory.heap.lookup source = some oldCell ∧
      run (.noRemap context returnAddress) allocate release allocator (Owner.headerAddress ⟨owner, 0⟩) capacity before = (.ok (some ()), raw) ∧
      after.memory = raw.memory ∧ after.effects = raw.effects ∧
      Compiler.Extraction.Memory.moveVector before.heap allocator source before.memory.nextId true = .ok after.heap ∧
      after.effects = release allocator oldCell.base (oldCapacity * 32) 8 effects ∧
      Valid after ∧ Compiler.Extraction.Memory.Vector allocator after.heap before.memory.nextId cells ∧
      Backing.Release.Owned allocator ⟨before.memory.nextId, 0⟩ capacity after ∧
      after.heap source = none ∧ after.memory.heap.lookup source = none ∧
      readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨before.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix after.memory before.memory.nextId cells ∧
      after.memory.nextId = before.memory.nextId + 1 ∧ after.memory.nextAddress = max before.memory.nextAddress (base + capacity * 32) ∧
      (∀ id, representativeFields after.memory (Owner.headerAddress ⟨owner, 0⟩) id =
        .ok ((Storage.representativeProgram.run cells id).map (DescriptorRelation.values id.toNat))) ∧
      (∀ previous, Compiler.Extraction.Memory.Resident allocator before.heap previous →
        Compiler.Extraction.Memory.Resident allocator after.heap previous) := by
  rw [fallback_execution runtimeSafety allocate release allocator owner source oldCapacity capacity cells.length context returnAddress
    before ownerCell valid ownerFound ownerType sourceOwned oldNonempty (by omega) short loaded count unlocked]
  obtain ⟨oldCell, raw, after, oldFound, executed, memory, reached, _, moved, effects, rest⟩ :=
    DescriptorRelation.fallback_registered runtimeSafety allocate release allocator owner source oldCapacity capacity base before effects ownerCell
      cells valid ownerFound ownerType ownerWritable sourceOwned vector oldNonempty (by omega) size extent response fits loaded represented
  exact ⟨oldCell, raw, after, oldFound, executed, memory, reached, moved, effects, rest⟩

end Compiler.Extraction.RepresentativeArray.Growth.Registered
