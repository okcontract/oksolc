/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeAllocationCoverage
import Compiler.Extraction.RepresentativeRegisteredCapacity

namespace Compiler.Extraction.RepresentativeArray.Growth
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The actual growth prefix checks the lock before selecting any allocation. -/
theorem ordinary_unlocked (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (selected : Option Unit)
    (completed : (run state header capacity allocate effects).1.1 = .ok selected) :
    Owner.NativeLock.checkHeader state header = .ok () := by
  cases checked : Owner.NativeLock.checkHeader state header with
  | error fault => simp only [run, prepare, checked, bind, Except.bind, reduceCtorEq] at completed
  | ok value => cases value; rfl

theorem Registered.ordinary_unlocked (callback : Remap.Callback) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ) (allocator : Nat) (header : Address) (capacity : Nat)
    (before : Session σ) (selected : Option Unit)
    (completed : (Registered.run callback allocate release allocator header capacity before).1 = .ok selected) :
    Owner.NativeLock.checkHeader before.memory header = .ok () := by
  cases checked : Owner.NativeLock.checkHeader before.memory header with
  | error fault => simp only [Registered.run, prepare, checked, bind, Except.bind, reduceCtorEq] at completed
  | ok value => cases value; rfl

/-- First growth derives its allocation observation from the original native
prefix, including the checked lock and the saved empty allocation view. -/
theorem first_observation (state : State) (header data : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (selected : Option Unit)
    (positive : 0 < capacity) (size : capacity * 32 < addressLimit)
    (loaded : readField state header capacityOffset = .ok (.scalar (.int false 64 0)))
    (saved : allocatedSlice state header = .ok (.slice itemsType data 0))
    (completed : (run state header capacity allocate effects).1.1 = .ok selected) :
    Owner.NativeLock.checkHeader state header = .ok () ∧
      Backing.AllocationObservation allocate capacity state effects selected.isSome := by
  have unlocked := ordinary_unlocked state header capacity allocate effects selected completed
  have first := run_first state header data capacity allocate effects (by omega) positive loaded saved unlocked
  exact ⟨unlocked, first_allocation_observation state header capacity allocate effects selected positive size (first ▸ completed)⟩

/-- An empty old allocation skips raw remap for every captured callback. Both
append adapters therefore expose the same source allocation outcome. -/
theorem Registered.first_observation (callback : Remap.Callback) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ) (allocator : Nat) (header data : Address) (capacity : Nat)
    (before : Session σ) (selected : Option Unit)
    (positive : 0 < capacity) (size : capacity * 32 < addressLimit)
    (loaded : readField before.memory header capacityOffset = .ok (.scalar (.int false 64 0)))
    (saved : allocatedSlice before.memory header = .ok (.slice itemsType data 0))
    (completed : (Registered.run callback allocate release allocator header capacity before).1 = .ok selected) :
    Owner.NativeLock.checkHeader before.memory header = .ok () ∧
      Backing.AllocationObservation (allocate allocator) capacity before.memory before.effects selected.isSome := by
  have unlocked := Registered.ordinary_unlocked callback allocate release allocator header capacity before selected completed
  have prepared := prepare_growing before.memory header data 0 capacity 0 (by omega) positive loaded saved unlocked
  have remapped := Remap.empty_old callback release allocator capacity data before positive (by omega)
  refine ⟨unlocked, Backing.Fallback.allocation_observation allocate release allocator header data 0 capacity before
    selected positive size ?_⟩
  simpa only [Registered.run, prepared, remapped] using completed

/-- Ordinary nonempty growth identifies the actual admitted remap body and
its fallback allocation. Unsupported callbacks stay rejected; they cannot be
reclassified as ordinary allocation failures. -/
theorem Registered.growing_observation (callback : Remap.Callback) (allocate : Backing.Registry.Allocate σ)
    (release : Backing.Release.External σ) (allocator : Nat) (header data : Address) (oldCapacity capacity : Nat)
    (before : Session σ) (selected : Option Unit)
    (valid : Valid before) (owned : Backing.Release.Owned allocator data oldCapacity before)
    (nonempty : oldCapacity ≠ 0) (short : oldCapacity < capacity) (size : capacity * 32 < addressLimit)
    (loaded : readField before.memory header capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (saved : allocatedSlice before.memory header = .ok (.slice itemsType data oldCapacity))
    (completed : (Registered.run callback allocate release allocator header capacity before).1 = .ok selected) :
    Owner.NativeLock.checkHeader before.memory header = .ok () ∧
      ∃ context returnAddress, callback = .noRemap context returnAddress ∧
        Backing.AllocationObservation (allocate allocator) capacity before.memory before.effects selected.isSome := by
  have unlocked := Registered.ordinary_unlocked callback allocate release allocator header capacity before selected completed
  have width : capacity < addressLimit := by omega
  have positive : 0 < capacity := by omega
  have prepared := prepare_growing before.memory header data oldCapacity capacity oldCapacity width short loaded saved unlocked
  cases callback with
  | noRemap context returnAddress =>
    have refused := Remap.refuses release allocator context returnAddress oldCapacity capacity data before valid owned positive width
    refine ⟨unlocked, context, returnAddress, rfl,
      Backing.Fallback.allocation_observation allocate release allocator header data oldCapacity capacity before selected positive size ?_⟩
    simpa only [Registered.run, prepared, refused] using completed
  | unsupported =>
    simp only [Registered.run, prepared, Remap.run, if_neg (Nat.not_le.mpr width),
      if_neg (by omega : capacity ≠ 0), if_neg nonempty, if_neg (Nat.not_le.mpr size)] at completed
    cases checked : Backing.Release.check allocator data oldCapacity before with
    | error fault => simp only [checked, reduceCtorEq] at completed
    | ok value => simp only [checked, reduceCtorEq] at completed

end Compiler.Extraction.RepresentativeArray.Growth
