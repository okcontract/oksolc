/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayGrowth

namespace Compiler.Extraction.RepresentativeArray.Growth
open Compiler.ZigAir.Memory

/-- First precise growth derives reservation, empty copy/release and ordered
publication from the initial header and the actual external allocation response.
The fresh backing remains uninitialized; no descriptor list or final header is
supplied as a premise. This does not cover remapping an existing allocation. -/
theorem run_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (sentinel : Address) (capacity base : Nat) (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true)
    (items : readItems state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType sentinel 0))
    (oldCapacity : readField state (Owner.headerAddress ⟨lifetime, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (positive : 0 < capacity) (size : capacity * 32 < addressLimit)
    (response : allocate (capacity * 32) 8 effects = (some base, reached))
    (fits : RegionAllocation.Fits state ⟨capacity * 32, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok ()) :
    ∃ after, run state (Owner.headerAddress ⟨lifetime, 0⟩) capacity allocate effects = ((.ok (some ()), after), reached) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨lifetime, 0⟩) =
        .ok (.slice itemsType ⟨state.nextId, 0⟩ 0, .scalar (.int false 64 capacity)) ∧
      after.heap.lookup state.nextId = some ⟨base, Backing.type capacity, [], true, false⟩ ∧
      after.nextId = state.nextId + 1 ∧ after.nextAddress = max state.nextAddress (base + capacity * 32) ∧
      (∀ id, id ≠ lifetime → id ≠ state.nextId → after.heap.lookup id = state.heap.lookup id) := by
  have pointer := readItemsData_from_loaded runtimeSafety state lifetime cell sentinel 0 initial found typed items
  have header : Owner.headerAddress ⟨lifetime, 0⟩ = ⟨lifetime, Owner.representativesOffset⟩ := rfl
  rw [header] at pointer items oldCapacity ⊢
  have oldMemory := allocatedSlice_empty state ⟨lifetime, Owner.representativesOffset⟩ sentinel pointer oldCapacity
  have width : capacity < addressLimit := by omega
  have older := (valid_lookup state lifetime cell initial found).1
  obtain ⟨ready, reserved, validReady, shapeReady, backing, idsReady, addressesReady, oldFrame⟩ :=
    Backing.reserve_verified state capacity base allocate effects reached initial (by omega) size response fits
  have ownerFrame := oldFrame lifetime (by omega)
  have readyFound := ownerFrame.trans found
  have readyItems : readItems ready ⟨lifetime, Owner.representativesOffset⟩ = .ok (.slice itemsType sentinel 0) :=
    (readField_eq_of_lookup state ready ⟨lifetime, Owner.representativesOffset⟩ itemsOffset ownerFrame).trans items
  obtain ⟨after, published, validAfter, shapeAfter, readback, idsAfter, addressesAfter, publicationFrame⟩ :=
    Publication.run_verified runtimeSafety ready lifetime cell sentinel ⟨state.nextId, 0⟩ 0 capacity
      validReady readyFound typed writable (by simpa only [header] using readyItems) width
  rw [header] at published readback
  have executed : run state ⟨lifetime, Owner.representativesOffset⟩ capacity allocate effects =
      ((.ok (some ()), after), reached) := by
    rw [run_first state _ sentinel capacity allocate effects width positive oldCapacity oldMemory unlocked]
    exact first_of_reservation_and_publication state ready after _ sentinel ⟨state.nextId, 0⟩ capacity allocate effects reached
      reserved readyItems published
  exact ⟨after, executed, validAfter, shapeReady.trans shapeAfter, readback,
    (publicationFrame state.nextId (by omega)).trans backing,
    idsAfter.trans idsReady, addressesAfter.trans addressesReady,
    fun id ownerApart freshApart => (publicationFrame id ownerApart).trans (oldFrame id freshApart)⟩

/-- OOM occurs before reading the copy length. Even an uninitialized length
cannot mask the allocator's ordinary failure or discard its private effects. -/
theorem run_oom (state : State) (header sentinel : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects reached : σ) (initial : state.valid = true)
    (pointer : readItemsData state header = .ok (.pointer Publication.pointerType sentinel))
    (oldCapacity : readField state header capacityOffset = .ok (.scalar (.int false 64 0)))
    (positive : 0 < capacity) (size : capacity * 32 < addressLimit)
    (response : allocate (capacity * 32) 8 effects = (none, reached))
    (unlocked : Owner.NativeLock.checkHeader state header = .ok ()) :
    run state header capacity allocate effects = ((.ok none, state), reached) := by
  have width : capacity < addressLimit := by omega
  have oldMemory := allocatedSlice_empty state header sentinel pointer oldCapacity
  rw [run_first state header sentinel capacity allocate effects width positive oldCapacity oldMemory unlocked]
  apply first_oom
  simpa only [Backing.reserve, if_neg (Nat.not_le.mpr width)] using
    RegionAllocation.reserve_failed state (Backing.type capacity) ⟨capacity * 32, 8⟩ allocate effects reached
      initial (Backing.layout_checked capacity) (by dsimp; omega) size response

theorem run_unchanged (state : State) (header : Address) (oldCapacity capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (width : capacity < addressLimit)
    (loaded : readField state header capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (enough : capacity ≤ oldCapacity)
    (unlocked : Owner.NativeLock.checkHeader state header = .ok ()) :
    run state header capacity allocate effects = ((.ok (some ()), state), effects) := by
  simp only [run, prepare, unlocked, bind, Except.bind, choose, if_neg (Nat.not_le.mpr width), loaded, Int.toNat_natCast, if_pos enough]

end Compiler.Extraction.RepresentativeArray.Growth
