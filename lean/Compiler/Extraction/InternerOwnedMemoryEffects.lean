/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryEffects
import Compiler.Extraction.InternerOwnedMemory
import Compiler.Extraction.GraphEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache

def World.mapEffects (project : σ → τ) (before : World σ) : World τ :=
  ⟨before.graph, before.memory.mapEffects project⟩

def State.mapEffects (project : σ → τ) (before : State σ) : State τ :=
  ⟨before.world.mapEffects project, before.scope⟩

namespace EffectTransport
variable {physical : External σ} {original : External τ} {project : σ → τ}
  (mapped : External.Transport physical original project)

/-- Recursive callbacks return the actual reached world; local handles remain
owned by the caller. This is the proper-child instrumentation obligation. -/
theorem graph (left : ArgumentSlice → GraphAction σ α) (right : ArgumentSlice → GraphAction τ α)
    (callbacks : ∀ slice, Effect.Transport (World.mapEffects project) (left slice) (right slice)) :
    Effect.Transport (State.mapEffects project) (OwnedCall.graph left) (OwnedCall.graph right) := by
  intro before
  unfold OwnedCall.graph
  simp only [State.mapEffects]
  cases before.scope.slice with
  | none => rfl
  | some slice => dsimp only; rw [callbacks slice before.world]

include mapped

theorem take (allocator : Nat) :
    Effect.Transport (State.mapEffects project) (OwnedCall.take physical allocator) (OwnedCall.take original allocator) := by
  intro before
  unfold OwnedCall.take
  simp only [State.mapEffects, World.mapEffects]
  cases before.scope.lookup with
  | none => rfl
  | some handle =>
    dsimp only
    rw [mapped.takeOwned]
    dsimp only [Step.mapEffects]
    cases Normalization.takeOwned normalizationOwnershipCode physical allocator handle before.world.memory with
    | mk result reached => cases result <;> rfl

theorem deinit (allocator : Nat) :
    Effect.Transport (State.mapEffects project) (OwnedCall.deinit physical allocator) (OwnedCall.deinit original allocator) := by
  intro before
  unfold OwnedCall.deinit
  simp only [State.mapEffects, World.mapEffects]
  cases before.scope.lookup with
  | none => rfl
  | some handle =>
    dsimp only
    rw [mapped.deinitialize]
    dsimp only [Step.mapEffects]
    cases Normalization.deinitialize normalizationOwnershipCode physical allocator handle before.world.memory with
    | mk result reached => cases result <;> rfl

theorem cleanup (allocator : Nat) :
    Effect.Transport (State.mapEffects project) (OwnedCall.cleanup physical allocator) (OwnedCall.cleanup original allocator) := by
  intro before
  unfold OwnedCall.cleanup
  simp only [show (before.mapEffects project).scope = before.scope from rfl]
  cases before.scope.handedOff with
  | true => exact deinit mapped allocator before
  | false =>
    cases before.scope.slice with
    | none => exact deinit mapped allocator before
    | some slice =>
      dsimp only
      simp only [show (before.mapEffects project).world.memory = before.world.memory.mapEffects project from rfl]
      rw [mapped.free]
      dsimp only [Step.mapEffects]
      cases Normalization.free physical allocator slice before.world.memory with
      | mk result reached =>
        cases result with
        | error fault => rfl
        | ok value =>
          cases value
          exact deinit mapped allocator ⟨⟨before.world.graph, reached⟩, { lookup := before.scope.lookup }⟩

theorem finish (allocator : Nat) (result : Except Fault α) (before : State σ) :
    OwnedCall.finish original allocator result (before.mapEffects project) =
      ((OwnedCall.finish physical allocator result before).1,
       (OwnedCall.finish physical allocator result before).2.mapEffects project) := by
  unfold OwnedCall.finish
  cases ordinary result with
  | false => rfl
  | true =>
    dsimp only
    rw [cleanup mapped allocator]
    cases OwnedCall.cleanup physical allocator before with
    | mk result reached => cases result <;> rfl

end EffectTransport
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
