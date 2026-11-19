/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeGrowthProgram
import Compiler.Extraction.RepresentativeArrayAllocationView
import Compiler.Extraction.RepresentativeArrayAllocation
import Compiler.Extraction.RepresentativeArrayCopy
import Compiler.Extraction.RepresentativeOwnerLock

namespace Compiler.Extraction.RepresentativeArray.Growth
open Compiler.ZigAir.Memory

/-- Continue after the empty old allocation's remap returned null. Ordinary
allocation failure is `ok none`, distinct from a checked-memory rejection.
The copy's source length is read only after successful allocation. Empty copy
and release do not inspect the sentinel or invoke an external free callback. -/
def firstAllocation (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) :
    (Except Fault (Option Unit) × State) × σ :=
  let ((reserved, ready), reached) := Backing.reserve state capacity allocate effects
  match reserved with
  | .error fault => ((.error fault, ready), reached)
  | .ok none => ((.ok none, ready), reached)
  | .ok (some data) =>
    match readItems ready header with
    | .error fault => ((.error fault, ready), reached)
    | .ok (.slice _ source length) =>
      if length ≠ 0 then ((.error .unsupported, ready), reached) else
      let (copied, afterCopy) := Copy.run ready source.allocation data.allocation length
      match copied with
      | .error fault => ((.error fault, afterCopy), reached)
      | .ok () =>
        -- The old capacity is zero; host.release is the specified empty no-op.
        let (published, afterPublication) := Publication.run afterCopy header data capacity
        match published with
        | .error fault => ((.error fault, afterPublication), reached)
        | .ok () => ((.ok (some ()), afterPublication), reached)
    | .ok _ => ((.error .malformed, ready), reached)

/-- Shared precise-growth prefix: check the native lock, read capacity, then save the complete old
allocation view only when growth is needed. No items length is evaluated. -/
def prepare (state : State) (header : Address) (capacity : Nat) : Except Fault (Option (Address × Nat)) := do
  Owner.NativeLock.checkHeader state header
  if capacity ≥ addressLimit then .error .malformed else
  match readField state header capacityOffset with
  | .error fault => .error fault
  | .ok (.scalar (.int false 64 oldCapacity)) =>
    match choose oldCapacity.toNat capacity with
    | .unchanged => .ok none
    | .firstAllocation | .existingGrowth =>
      match allocatedSlice state header with
      | .error fault => .error fault
      | .ok (.slice declared data extent) =>
        if declared = itemsType then .ok (some (data, extent)) else .error .malformed
      | .ok _ => .error .malformed
  | .ok _ => .error .malformed

/-- The first-allocation facade retains the shared source prefix. A nonempty
old view requires a separately admitted remap callback; this facade rejects it. -/
def run (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) :
    (Except Fault (Option Unit) × State) × σ :=
  match prepare state header capacity with
  | .error fault => ((.error fault, state), effects)
  | .ok none => ((.ok (some ()), state), effects)
  | .ok (some (_, oldCapacity)) =>
    if oldCapacity = 0 then firstAllocation state header capacity allocate effects
    else ((.error .unsupported, state), effects)

/-- The native assertion precedes capacity selection and every allocator call.
A failed check is a validation rejection with the original state and effects. -/
theorem lock_rejected (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (reason : Fault)
    (rejected : Owner.NativeLock.checkHeader state header = .error reason) :
    run state header capacity allocate effects = ((.error reason, state), effects) := by
  simp only [run, prepare, rejected, bind, Except.bind]

theorem prepare_growing (state : State) (header data : Address) (oldCapacity capacity extent : Nat)
    (width : capacity < addressLimit) (short : oldCapacity < capacity)
    (loaded : readField state header capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (saved : allocatedSlice state header = .ok (.slice itemsType data extent))
    (unlocked : Owner.NativeLock.checkHeader state header = .ok ()) :
    prepare state header capacity = .ok (some (data, extent)) := by
  simp only [prepare, unlocked, bind, Except.bind, if_neg (Nat.not_le.mpr width), loaded, choose, Int.toNat_natCast,
    if_neg (by omega : ¬oldCapacity ≥ capacity)]
  by_cases empty : oldCapacity = 0 <;> simp [empty, saved]

theorem run_first (state : State) (header data : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ)
    (width : capacity < addressLimit) (positive : 0 < capacity)
    (oldCapacity : readField state header capacityOffset = .ok (.scalar (.int false 64 0)))
    (oldMemory : allocatedSlice state header = .ok (.slice itemsType data 0))
    (unlocked : Owner.NativeLock.checkHeader state header = .ok ()) :
    run state header capacity allocate effects = firstAllocation state header capacity allocate effects := by
  simp only [run, prepare, unlocked, bind, Except.bind, choose, if_neg (Nat.not_le.mpr width), oldCapacity, Int.toNat_zero,
    if_neg (by omega : ¬0 ≥ capacity), oldMemory, ↓reduceIte]

theorem first_of_reservation_and_publication (state ready after : State) (header source data : Address)
    (capacity : Nat) (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (reserved : Backing.reserve state capacity allocate effects = ((.ok (some data), ready), reached))
    (empty : readItems ready header = .ok (.slice itemsType source 0))
    (published : Publication.run ready header data capacity = (.ok (), after)) :
    firstAllocation state header capacity allocate effects = ((.ok (some ()), after), reached) := by
  simp only [firstAllocation, reserved, empty, ne_self_iff_false, ↓reduceIte, Copy.run, published]

theorem first_oom (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (reserved : Backing.reserve state capacity allocate effects = ((.ok none, state), reached)) :
    firstAllocation state header capacity allocate effects = ((.ok none, state), reached) := by
  simp only [firstAllocation, reserved]

end Compiler.Extraction.RepresentativeArray.Growth
