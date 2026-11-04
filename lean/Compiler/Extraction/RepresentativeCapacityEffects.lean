/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingEffects

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory

variable {project : σ → τ} {left : Backing.Registry.Allocate σ} {right : Backing.Registry.Allocate τ}
  (allocated : Backing.Registry.Allocate.Transport project left right)
include allocated

/-- The first-allocation facade shares the same reservation proof as registered
growth. Its later reads, copies and stores retain every reached state. -/
theorem Growth.firstAllocation_transport (allocator capacity : Nat) (state : State) (header : Address) (effects : σ) :
    Growth.firstAllocation state header capacity (right allocator) (project effects) =
      ((Growth.firstAllocation state header capacity (left allocator) effects).1,
       project (Growth.firstAllocation state header capacity (left allocator) effects).2) := by
  unfold Growth.firstAllocation
  rw [Backing.reserve_transport allocated]
  cases Backing.reserve state capacity (left allocator) effects with
  | mk outcome reached =>
    rcases outcome with ⟨result, ready⟩
    cases result with
    | error reason => rfl
    | ok value => cases value with
      | none => rfl
      | some data =>
        dsimp only
        split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · split <;> rfl
        · rfl

theorem Growth.run_transport (allocator capacity : Nat) (state : State) (header : Address) (effects : σ) :
    Growth.run state header capacity (right allocator) (project effects) =
      ((Growth.run state header capacity (left allocator) effects).1,
       project (Growth.run state header capacity (left allocator) effects).2) := by
  unfold Growth.run
  split
  · rfl
  · rfl
  · split
    · exact Growth.firstAllocation_transport allocated allocator capacity state header effects
    · rfl

theorem Capacity.ensure_transport (allocator minimum : Nat) (state : State) (header : Address) (effects : σ) :
    Capacity.ensure state header minimum (right allocator) (project effects) =
      ((Capacity.ensure state header minimum (left allocator) effects).1,
       project (Capacity.ensure state header minimum (left allocator) effects).2) := by
  unfold Capacity.ensure
  split
  · rfl
  · rfl
  · exact Growth.run_transport allocated allocator _ state header effects

end Compiler.Extraction.RepresentativeArray
