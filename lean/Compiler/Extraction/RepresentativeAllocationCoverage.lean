/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingRegistry
import Compiler.Extraction.RepresentativeFallback
import Compiler.Extraction.RepresentativeArrayGrowth

namespace Compiler.Extraction.RepresentativeArray.Backing
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The actual backing request and checked response. This records source
observations only; it assumes no resulting storage or ownership invariant. -/
def AllocationObservation (allocate : RegionAllocation.Allocator σ) (capacity : Nat)
    (before : State) (effects : σ) (accepted : Bool) : Prop :=
  if accepted then ∃ base reached, allocate (capacity * 32) 8 effects = (some base, reached) ∧
    RegionAllocation.Fits before ⟨capacity * 32, 8⟩ base
  else ∃ reached, allocate (capacity * 32) 8 effects = (none, reached)

/-- Invert the existing reservation. Nonempty, nonoverflowing requests can
report ordinary OOM only from the actual allocator refusal; accepted regions
supply their full validity contract from the native checker. -/
theorem reserve_observation (state : State) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (selected : Option Address)
    (positive : 0 < capacity) (size : capacity * 32 < addressLimit)
    (completed : (reserve state capacity allocate effects).1.1 = .ok selected) :
    AllocationObservation allocate capacity state effects selected.isSome := by
  have width : capacity < addressLimit := by omega
  have nonzero : capacity * 32 ≠ 0 := by omega
  simp only [reserve, if_neg (Nat.not_le.mpr width)] at completed
  cases selected with
  | none =>
    simp only [RegionAllocation.reserve, layout_checked, if_neg nonzero] at completed
    split at completed
    · cases completed
    · rw [if_neg (Nat.not_le.mpr size)] at completed
      cases response : allocate (capacity * 32) 8 effects with
      | mk value reached =>
        rw [response] at completed
        dsimp only at completed
        cases value with
        | none => exact ⟨reached, response⟩
        | some base =>
          dsimp only at completed
          split at completed <;> cases completed
  | some address =>
    let ran := RegionAllocation.reserve state (type capacity) allocate effects
    have executed : RegionAllocation.reserve state (type capacity) allocate effects =
        ((.ok (some address), ran.1.2), ran.2) :=
      Prod.ext (Prod.ext completed rfl) rfl
    obtain ⟨base, _, memory, called, valid⟩ :=
      RegionAllocation.reserve_nonempty_success state ran.1.2 (type capacity) ⟨capacity * 32, 8⟩
        allocate effects ran.2 address (layout_checked capacity) nonzero executed
    exact ⟨base, ran.2, called,
      RegionAllocation.fits_of_extend_valid state (type capacity) ⟨capacity * 32, 8⟩ base
        (layout_checked capacity) (memory ▸ valid)⟩

/-- Registry rejection cannot manufacture an ordinary allocation observation. -/
theorem Registry.ordinary_reservation (allocate : Registry.Allocate σ) (allocator capacity : Nat)
    (before : Session σ) (selected : Option Address)
    (completed : (Registry.run allocate allocator capacity before).1 = .ok selected) :
    (reserve before.memory capacity (allocate allocator) before.effects).1.1 = .ok selected := by
  unfold Registry.run at completed
  cases reserved : reserve before.memory capacity (allocate allocator) before.effects with
  | mk native effects =>
    obtain ⟨result, memory⟩ := native
    rw [reserved] at completed
    dsimp only at completed
    cases result with
    | error fault => cases completed
    | ok value =>
      cases value with
      | none => exact congrArg Except.ok (Except.ok.inj completed)
      | some data =>
        dsimp only at completed
        split at completed
        · exact congrArg Except.ok (Except.ok.inj completed)
        · split at completed
          · cases completed
          · exact congrArg Except.ok (Except.ok.inj completed)

/-- Fallback's ordinary result preserves the actual allocation decision even
when copying, release or publication subsequently change the reached session. -/
theorem Fallback.allocation_observation (allocate : Registry.Allocate σ) (release : Release.External σ)
    (allocator : Nat) (header oldData : Address) (oldCapacity capacity : Nat) (before : Session σ)
    (selected : Option Unit) (positive : 0 < capacity) (size : capacity * 32 < addressLimit)
    (completed : (Fallback.run allocate release allocator header oldData oldCapacity capacity before).1 = .ok selected) :
    AllocationObservation (allocate allocator) capacity before.memory before.effects selected.isSome := by
  cases allocated : Registry.run allocate allocator capacity before with
  | mk result reached =>
    simp only [Fallback.run, allocated] at completed
    cases result with
    | error fault => cases fault <;> cases completed
    | ok data =>
      have native := Registry.ordinary_reservation allocate allocator capacity before data (by rw [allocated])
      have observed := reserve_observation before.memory capacity (allocate allocator) before.effects data positive size native
      cases data with
      | none =>
        have same : selected = none := (Except.ok.inj completed).symm
        simpa only [same] using observed
      | some data =>
        dsimp only at completed
        cases moved : Relocation.run release allocator header oldData data oldCapacity capacity reached with
        | mk result after =>
          rw [moved] at completed
          cases result with
          | error fault => cases completed
          | ok value =>
            cases value
            have same : selected = some () := (Except.ok.inj completed).symm
            simpa only [same] using observed

end Compiler.Extraction.RepresentativeArray.Backing

namespace Compiler.Extraction.RepresentativeArray.Growth
open Compiler.ZigAir.Memory

/-- First allocation and relocation expose the same primitive response
contract. The later copy/publication stages cannot manufacture an OOM. -/
theorem first_allocation_observation (state : State) (header : Address) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (selected : Option Unit)
    (positive : 0 < capacity) (size : capacity * 32 < addressLimit)
    (completed : (firstAllocation state header capacity allocate effects).1.1 = .ok selected) :
    Backing.AllocationObservation allocate capacity state effects selected.isSome := by
  cases reserved : Backing.reserve state capacity allocate effects with
  | mk native reached =>
    obtain ⟨result, memory⟩ := native
    simp only [firstAllocation, reserved] at completed
    cases result with
    | error fault => cases completed
    | ok data =>
      have observed := Backing.reserve_observation state capacity allocate effects data positive size (by rw [reserved])
      cases data with
      | none =>
        have same : selected = none := (Except.ok.inj completed).symm
        simpa only [same] using observed
      | some data =>
        dsimp only at completed
        have same : selected = some () := by
          repeat first
            | dsimp only at completed
            | exact (Except.ok.inj completed).symm
            | contradiction
            | split at completed
        simpa only [same] using observed

end Compiler.Extraction.RepresentativeArray.Growth
