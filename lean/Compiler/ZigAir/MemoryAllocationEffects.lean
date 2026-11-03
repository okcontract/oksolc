/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordAllocation

namespace Compiler.ZigAir.Memory

/-- Reobserve private allocator effects without changing its actual response,
typed allocation, rejection or reached memory. The callback equation applies
at every reached effect state, including ordinary OOM and invalid regions. -/
theorem RegionAllocation.reserve_transport (state : State) (type : Ty)
    (physical : RegionAllocation.Allocator σ) (original : RegionAllocation.Allocator τ)
    (project : σ → τ)
    (mapped : ∀ bytes alignment effects, original bytes alignment (project effects) =
      ((physical bytes alignment effects).1, project (physical bytes alignment effects).2))
    (effects : σ) :
    RegionAllocation.reserve state type original (project effects) =
      ((RegionAllocation.reserve state type physical effects).1,
       project (RegionAllocation.reserve state type physical effects).2) := by
  unfold RegionAllocation.reserve
  cases shaped : type.layout with
  | none => rfl
  | some layout =>
    by_cases empty : layout.bytes = 0
    · simp only [empty, ↓reduceIte]
    · simp only [empty, ↓reduceIte]
      cases state.valid with
      | false => simp only [Bool.not_false, ↓reduceIte]
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases large : layout.bytes ≥ addressLimit
        · simp only [large, ↓reduceIte]
        · simp only [large, ↓reduceIte, mapped]
          cases physical layout.bytes layout.alignment effects with
          | mk result reached =>
            cases result with
            | none => rfl
            | some base =>
              dsimp only
              split <;> rfl

theorem WordAllocation.reserve_transport (state : State) (length : Nat)
    (physical : WordAllocation.Allocator σ) (original : WordAllocation.Allocator τ)
    (project : σ → τ)
    (mapped : ∀ bytes effects, original bytes (project effects) =
      ((physical bytes effects).1, project (physical bytes effects).2))
    (effects : σ) :
    WordAllocation.reserve state length original (project effects) =
      ((WordAllocation.reserve state length physical effects).1,
       project (WordAllocation.reserve state length physical effects).2) := by
  unfold WordAllocation.reserve
  by_cases empty : length = 0
  · simp only [empty, ↓reduceIte]
  · simp only [empty, ↓reduceIte]
    by_cases large : length ≥ addressLimit
    · simp only [large, ↓reduceIte]
    · simp only [large, ↓reduceIte]
      rw [RegionAllocation.reserve_transport state (.array length WordArray.word)
        (fun bytes _ => physical bytes) (fun bytes _ => original bytes) project
        (fun bytes _ effects => mapped bytes effects)]

end Compiler.ZigAir.Memory
