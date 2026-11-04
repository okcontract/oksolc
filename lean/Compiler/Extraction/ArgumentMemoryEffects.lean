/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryDuplication
import Compiler.ZigAir.MemoryAllocationEffects

namespace Compiler.Extraction.Memory.Arguments
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory

theorem Allocation.reserve_transport (heap : Heap) (memory : Compiler.ZigAir.Memory.State)
    (allocator : Nat) (items : List NodeId)
    (physical : WordAllocation.Allocator σ) (original : WordAllocation.Allocator τ)
    (project : σ → τ)
    (mapped : ∀ bytes effects, original bytes (project effects) =
      ((physical bytes effects).1, project (physical bytes effects).2))
    (effects : σ) :
    Allocation.reserve heap memory allocator items original (project effects) =
      ((Allocation.reserve heap memory allocator items physical effects).1,
       project (Allocation.reserve heap memory allocator items physical effects).2) := by
  unfold Allocation.reserve
  rw [WordAllocation.reserve_transport memory items.length physical original project mapped]
  cases WordAllocation.reserve memory items.length physical effects with
  | mk allocation reached =>
    rcases allocation with ⟨result, after⟩
    cases result with
    | error fault => rfl
    | ok result =>
      cases result with
      | none => rfl
      | some target =>
        cases items.isEmpty <;> simp only [Bool.false_eq_true, ↓reduceIte]
        cases Memory.allocate heap allocator target.allocation (.arguments items) true <;> rfl

theorem Duplication.run_transport (heap : Heap) (memory : Compiler.ZigAir.Memory.State)
    (allocator : Nat) (source : WordArray.View) (items : List NodeId)
    (physical : WordAllocation.Allocator σ) (original : WordAllocation.Allocator τ)
    (project : σ → τ)
    (mapped : ∀ bytes effects, original bytes (project effects) =
      ((physical bytes effects).1, project (physical bytes effects).2))
    (effects : σ) :
    Duplication.run heap memory allocator source items original (project effects) =
      ((Duplication.run heap memory allocator source items physical effects).1,
       project (Duplication.run heap memory allocator source items physical effects).2) := by
  unfold Duplication.run
  by_cases different : source.length ≠ items.length
  · simp only [if_pos different]
  · simp only [if_neg different]
    rw [Allocation.reserve_transport heap memory allocator items physical original project mapped]
    cases Allocation.reserve heap memory allocator items physical effects with
    | mk allocation reached =>
      rcases allocation with ⟨result, registered, after⟩
      cases result with
      | error fault => rfl
      | ok result =>
        cases result with
        | none => rfl
        | some destination =>
          dsimp only
          cases copied : WordCopy.copy after source (view destination) with
          | mk result after => cases result <;> rfl

end Compiler.Extraction.Memory.Arguments
