/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerPublicationInput
import Compiler.Extraction.InternerInsertionCleanupEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache

/-- Normalizer deinitialization has allocator-private effects only. Reuse the
native free adapter's effect frame for both accepted and rejected releases. -/
theorem deinitialize_keys (host : External σ) (allocator : Nat) (handle : Handle) (before : Session (Effects σ)) :
    (deinitialize normalizationOwnershipCode (external host) allocator handle before).2.effects.keys = before.effects.keys := by
  unfold deinitialize
  cases handle.owned with
  | none => rfl
  | some slice => exact Insertion.Native.free_keys host allocator slice before

theorem caller_deinit_keys (host : External σ) (allocator : Nat) (before : State (Effects σ)) :
    (deinit (external host) allocator before).2.world.memory.effects.keys = before.world.memory.effects.keys := by
  unfold deinit
  cases before.scope.lookup with
  | none => rfl
  | some handle =>
    dsimp only
    have kept := deinitialize_keys host allocator handle before.world.memory
    cases ran : deinitialize normalizationOwnershipCode (external host) allocator handle before.world.memory with
    | mk result reached =>
      rw [ran] at kept
      cases result <;> exact kept

theorem caller_cleanup_keys (host : External σ) (allocator : Nat) (before : State (Effects σ)) :
    (cleanup (external host) allocator before).2.world.memory.effects.keys = before.world.memory.effects.keys := by
  unfold cleanup
  split
  · exact caller_deinit_keys host allocator before
  · cases before.scope.slice with
    | none => exact caller_deinit_keys host allocator before
    | some slice =>
      dsimp only
      have kept := Insertion.Native.free_keys host allocator slice before.world.memory
      cases ran : free (external host) allocator slice before.world.memory with
      | mk result reached =>
        rw [ran] at kept
        cases result with
        | error fault => exact kept
        | ok value =>
          exact (caller_deinit_keys host allocator
            { before with world := { before.world with memory := reached }, scope := { before.scope with slice := none } }).trans kept

theorem caller_finish_keys (host : External σ) (allocator : Nat) (result : Except Fault α) (before : State (Effects σ)) :
    (finish (external host) allocator result before).2.world.memory.effects.keys = before.world.memory.effects.keys := by
  unfold finish
  split
  · have kept := caller_cleanup_keys host allocator before
    cases ran : cleanup (external host) allocator before with
    | mk result reached =>
      rw [ran] at kept
      cases result <;> exact kept
  · rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
