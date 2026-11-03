/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResources

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

def token (origin : NormalizationOwnership.Origin) (handle : Handle) : NormalizationOwnership.State :=
  { origin := origin, owned := handle.owned.isSome, owner := if handle.owned.isSome then .lookup else .absent }

def continued (external : External σ) (budget allocator : Nat) (source buffer : View) (values : List NodeId)
    (origin : NormalizationOwnership.Origin) (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ) :=
  let (result, after) := normalizationOwnershipCode.continueWith
    (primitives external budget allocator source buffer values).toPrimitives exit (token origin handle) ⟨before, handle, none, none⟩
  (observe (.ok result) after, after.session)

/-- The resource interpreter's transfer and cleanup execute the same memory
operations, with the same outcomes and reached effects. No validity or
normalization-correctness premise is needed for this exact correspondence. -/
theorem continued_eq (external : External σ) (budget allocator : Nat) (source buffer : View) (values : List NodeId)
    (origin : NormalizationOwnership.Origin) (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ) :
    continued external budget allocator source buffer values origin exit handle before =
      let (result, after) := Normalization.continueWith normalizationOwnershipCode external allocator exit handle before
      (some result, after) := by
  rcases handle with ⟨items, contents, owned⟩
  cases owned with
  | some slice =>
    cases exit with
    | transfer => rfl
    | lookup | cleanup =>
      cases freed : Normalization.free external allocator slice before with
      | mk result after =>
        cases result with
        | error failure =>
          all_goals simp [continued, token, primitives, NormalizationOwnership.Code.continueWith,
            NormalizationOwnership.Code.finishWith, NormalizationOwnership.Code.takeWith,
            NormalizationOwnership.Code.deinitWith, NormalizationOwnership.State.move,
            release, outputSlice, observe, Normalization.continueWith, Normalization.close,
            Normalization.deinitialize, Normalization.takeOwned, normalizationOwnershipCode, freed]
        | ok returned =>
          cases returned
          all_goals simp [continued, token, primitives, NormalizationOwnership.Code.continueWith,
            NormalizationOwnership.Code.finishWith, NormalizationOwnership.Code.takeWith,
            NormalizationOwnership.Code.deinitWith, NormalizationOwnership.State.move,
            release, outputSlice, observe, Normalization.continueWith, Normalization.close,
            Normalization.deinitialize, Normalization.takeOwned, normalizationOwnershipCode, freed]
  | none =>
    cases exit with
    | lookup => rfl
    | transfer | cleanup =>
      cases copied : Duplication.run before.heap before.memory allocator items contents
          (external.allocate .duplicate before) before.effects with
      | mk result effects =>
        rcases result with ⟨outcome, heap, memory⟩
        cases outcome with
        | error failure =>
          all_goals simp [continued, token, primitives, NormalizationOwnership.Code.continueWith,
            NormalizationOwnership.Code.finishWith, NormalizationOwnership.Code.takeWith,
            NormalizationOwnership.Code.deinitWith,
            allocate, failed, observe, Normalization.continueWith,
            Normalization.takeOwned, normalizationOwnershipCode, copied]
        | ok result =>
          cases result with
          | none =>
            all_goals simp [continued, token, primitives, NormalizationOwnership.Code.continueWith,
              NormalizationOwnership.Code.finishWith, NormalizationOwnership.Code.takeWith,
              NormalizationOwnership.Code.deinitWith,
              allocate, failed, observe, Normalization.continueWith, Normalization.close,
              Normalization.deinitialize, Normalization.takeOwned, normalizationOwnershipCode, copied]
          | some slice =>
            all_goals simp [continued, token, primitives, NormalizationOwnership.Code.continueWith,
              NormalizationOwnership.Code.finishWith, NormalizationOwnership.Code.takeWith,
              NormalizationOwnership.Code.deinitWith, NormalizationOwnership.State.move,
              allocate, outputSlice, observe, Normalization.continueWith, Normalization.close,
              Normalization.deinitialize, Normalization.takeOwned, normalizationOwnershipCode, copied]
            all_goals
              cases freed : Normalization.free external allocator slice (⟨heap, memory, effects⟩ : Session σ) with
              | mk result after =>
                cases result with
                | error failure => simp [release, outputSlice, freed]
                | ok returned => cases returned; simp [release, outputSlice, freed]

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
