/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorPreservation
import Compiler.Extraction.RepresentativeAppendFrame
import Compiler.ZigAir.MemorySliceElements

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation
open Compiler.ZigAir.Memory

/-- Successful selection retains the loaded allocation and source-selected
index. No successful access is inferred from a logical cell or numeric address. -/
theorem selected_address (state : State) (header address : Address) (lifetime length : Nat)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ (Append.nextLength length)))
    (selected : Append.selectNewElement state header (Append.nextLength length) = .ok address) :
    address = ⟨lifetime, length * 32⟩ := by
  simp only [Append.selectNewElement, loaded, bind, Except.bind] at selected
  cases pointed : sliceElementPointer state (.slice itemsType ⟨lifetime, 0⟩ (Append.nextLength length))
      (Append.selectedIndex (Append.nextLength length)) with
  | error fault => simp [pointed] at selected
  | ok element =>
    obtain ⟨_, _, layout, shaped, _, same⟩ := sliceElementPointer_address state true elementType ⟨lifetime, 0⟩
      (Append.nextLength length) (Append.selectedIndex (Append.nextLength length)) element pointed
    have layoutEq : layout = ⟨32, 8⟩ := Option.some.inj (shaped.symm.trans rfl)
    subst layout
    simp only [Append.selectedIndex, Append.nextLength, Nat.add_sub_cancel, Nat.zero_add] at same
    subst element
    simp only [pointed] at selected
    cases resolved : recordView state Expression.allocationType
        (.pointer (.pointer true false elementType) ⟨lifetime, length * 32⟩) with
    | error fault => simp [resolved] at selected
    | ok complete =>
      have same := recordView_address state Expression.allocationType true false _ _ ⟨lifetime, length * 32⟩ complete resolved
      subst complete
      simpa only [resolved, bind, Except.bind, ne_self_iff_false, Nat.mul_mod_left, or_self, ↓reduceIte,
        Except.ok.injEq] using selected.symm

/-- Every reached descriptor-assignment outcome preserves the old prefix.
Failure may leave a partial new row, which is not added to the relation. -/
theorem finish_frame (state : State) (header : Address) (lifetime : Nat) (cells : List Storage.Cell)
    (item arguments : Address) (length : Nat) (id sequence : Int)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ (Append.nextLength cells.length)))
    (represented : Prefix state lifetime cells) :
    Prefix (Append.Execution.finish state header (Append.nextLength cells.length) item arguments length id sequence).2 lifetime cells := by
  unfold Append.Execution.finish
  cases selected : Append.selectNewElement state header (Append.nextLength cells.length) with
  | error fault => exact represented
  | ok address =>
    have same := selected_address state header address lifetime cells.length loaded selected
    subst address
    simp only [Nat.mul_div_cancel _ (by decide : 0 < 32)]
    intro index cell found
    have inside : index < cells.length := by
      by_cases inside : index < cells.length
      · exact inside
      · rw [List.getElem?_eq_none (by omega)] at found
        contradiction
    exact (initialization_frame state lifetime cells.length index item arguments length id sequence (by omega)).trans
      (represented index cell found)

/-- Header length mutation and even later rejection preserve all previously
represented rows. The separate header allocation is derived by callers. -/
theorem assumeCapacity_frame (state : State) (header : Address) (lifetime capacity : Nat) (cells : List Storage.Cell)
    (item arguments : Address) (length : Nat) (id sequence : Int)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (lengthRead : readField state header Append.lengthOffset = .ok (.scalar (.int false 64 cells.length)))
    (capacityRead : readField state header capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (selector : fieldPointer state (.pointer (.pointer false false allocationType) header) itemsOffset =
      .ok (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩))
    (separate : lifetime ≠ header.allocation) (represented : Prefix state lifetime cells) :
    Prefix (Append.Execution.assumeCapacity state header item arguments length id sequence).2 lifetime cells := by
  simp only [Append.Execution.assumeCapacity, lengthRead, capacityRead, Int.toNat_natCast]
  split
  · exact represented
  · cases written : Append.writeLength state header (Append.nextLength cells.length) with
    | error fault => exact represented
    | ok ready =>
      have stored := Append.Execution.length_write_is_store state ready header _ written
      have kept := heap_after_store_other _ _ _ _ _ _ _ stored lifetime separate
      exact finish_frame ready header lifetime cells item arguments length id sequence
        (Append.readItems_after_length_store_at state ready header ⟨lifetime, 0⟩ cells.length _ selector loaded stored)
        (frame state ready lifetime cells represented kept)

/-- Complete spare-capacity append preserves every old row, including on a
later checked rejection. The actual capacity call returns before allocation. -/
theorem owner_spare_frame (runtimeSafety : Bool) (state : State) (owner lifetime capacity : Nat) (ownerCell : Allocation)
    (cells : List Storage.Cell) (item arguments : Address) (length : Nat) (id sequence : Int)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (initial : state.valid = true)
    (found : state.heap.lookup owner = some ownerCell) (typed : ownerCell.type = Owner.viewType runtimeSafety)
    (loaded : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : cells.length < capacity) (bounded : Append.nextLength cells.length < addressLimit)
    (separate : lifetime ≠ owner) (represented : Prefix state lifetime cells) :
    Prefix (Append.Execution.ownerRun runtimeSafety state ⟨owner, 0⟩ item arguments length id sequence allocate effects).1.2 lifetime cells := by
  have selected := Owner.root_header_pointer runtimeSafety state owner ownerCell true initial found typed
  have lengthRead := Append.Execution.owner_length_from_items runtimeSafety state owner ownerCell ⟨lifetime, 0⟩ cells.length initial found typed loaded
  have selector := (Owner.root_header_fields runtimeSafety state owner ownerCell false initial found typed).1
  have ensured := Capacity.ensure_unchanged state (Owner.headerAddress ⟨owner, 0⟩) capacity (Append.nextLength cells.length) allocate effects
    bounded capacityRead (by simp only [Append.nextLength]; omega)
  have kept := assumeCapacity_frame state (Owner.headerAddress ⟨owner, 0⟩) lifetime capacity cells item arguments length id sequence
    loaded lengthRead capacityRead selector separate represented
  simp only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected, Append.Execution.runWithCapacity, lengthRead, Int.toNat_natCast,
    if_neg (Nat.not_le.mpr bounded), ensured]
  generalize assigned : Append.Execution.assumeCapacity state (Owner.headerAddress ⟨owner, 0⟩) item arguments length id sequence = result at *
  rcases result with ⟨result, after⟩
  cases result <;> exact kept

/-- After an actual successful capacity call, every append continuation retains
the reached allocation geometry, even if it later rejects. This exposes the
fresh first-growth backing without assuming a final allocation or field. -/
theorem after_capacity_shape (state ready : State) (header : Address) (length : Nat)
    (item arguments : Address) (argumentsLength : Nat) (id sequence : Int)
    (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (lengthRead : readField state header Append.lengthOffset = .ok (.scalar (.int false 64 length)))
    (bounded : Append.nextLength length < addressLimit)
    (ensured : Capacity.ensure state header (Append.nextLength length) allocate effects = ((.ok (some ()), ready), reached))
    (readyValid : ready.valid = true) :
    ready.heap.RetainsShape (Append.Execution.run state header item arguments argumentsLength id sequence allocate effects).1.2.heap := by
  have shape := (Append.Execution.assumeCapacity_storage ready header item arguments argumentsLength id sequence readyValid).2.1
  simp only [Append.Execution.run, Append.Execution.runWithCapacity, lengthRead, Int.toNat_natCast, if_neg (Nat.not_le.mpr bounded), ensured]
  generalize assigned : Append.Execution.assumeCapacity ready header item arguments argumentsLength id sequence = result at *
  rcases result with ⟨result, after⟩
  cases result <;> exact shape

/-- The first admitted allocation survives every later append outcome with its
exact base, extent, mutability and persistent lifetime. This derives the fresh
backing from the actual capacity response, even if descriptor assignment fails. -/
theorem first_continuation_backing (runtimeSafety : Bool) (state : State) (owner : Nat) (ownerCell : Allocation)
    (sentinel item arguments : Address) (length : Nat) (id sequence : Int) (base : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (initial : state.valid = true) (found : state.heap.lookup owner = some ownerCell)
    (typed : ownerCell.type = Owner.viewType runtimeSafety) (writable : ownerCell.writable = true)
    (items : readItems state (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacity : readField state (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (response : allocate 160 8 effects = (some base, reached)) (fits : RegionAllocation.Fits state ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader state (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    let after := (Append.Execution.ownerRun runtimeSafety state ⟨owner, 0⟩ item arguments length id sequence allocate effects).1.2
    state.heap.RetainsShape after.heap ∧
      ∃ backing, after.heap.lookup state.nextId = some backing ∧
        Allocation.SameShape ⟨base, Backing.type 5, [], true, false⟩ backing := by
  obtain ⟨ready, ensured, readyValid, readyShape, _, backing, _, _, _⟩ :=
    Capacity.first_verified runtimeSafety state owner ownerCell sentinel 1 base allocate effects reached initial found typed writable
      items capacity (by decide) (by decide) (by decide) response fits unlocked
  have lengthRead := Append.Execution.owner_length_from_items runtimeSafety state owner ownerCell sentinel 0 initial found typed items
  have selected := Owner.root_header_pointer runtimeSafety state owner ownerCell true initial found typed
  have retained := after_capacity_shape state ready (Owner.headerAddress ⟨owner, 0⟩) 0 item arguments
    length id sequence allocate effects reached lengthRead (by decide) ensured readyValid
  simpa only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected] using
    And.intro (readyShape.trans retained) (retained state.nextId _ backing)

end Compiler.Extraction.RepresentativeArray.DescriptorRelation
