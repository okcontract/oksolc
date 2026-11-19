/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredPop
import Compiler.Extraction.NormalizationMemoryEffects
import Compiler.Extraction.GraphEffects

namespace Compiler.Extraction.RepresentativeArray.Pop.Registered
open Compiler.Algebraic Compiler.Extraction.Memory.Arguments.Normalization

theorem finish_transport (project : σ → τ) (allocator owner : Nat) :
    Effect.Transport (Session.mapEffects project) (finish allocator owner) (finish allocator owner) := by
  intro before
  unfold finish
  simp only [Session.mapEffects_memory, Session.mapEffects_heap]
  split
  · rfl
  · split
    · split
      · rfl
      · split
        · rfl
        · split <;> rfl
      · rfl
    · rfl
  · rfl

/-- The registry check observes the completed native decrement. Its rejection
retains that store on both sides of the projection. -/
theorem run_transport (project : σ → τ) (allocator owner : Nat) :
    Effect.Transport (Session.mapEffects project) (run allocator owner) (run allocator owner) := by
  intro before
  unfold run
  simp only [Session.mapEffects_memory]
  cases Pop.run before.memory (Owner.headerAddress ⟨owner, 0⟩) with
  | error reason => rfl
  | ok memory => exact finish_transport project allocator owner { before with memory }

end Compiler.Extraction.RepresentativeArray.Pop.Registered
