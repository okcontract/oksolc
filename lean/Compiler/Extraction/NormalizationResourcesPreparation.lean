/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesLifetime

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

def preparedToken (origin : NormalizationOwnership.Origin) (source buffer : View) : NormalizationOwnership.State :=
  let owned := normalizationOwnershipCode.ownTemporary.test source.length buffer.length
  { origin := origin, owned := owned, owner := if owned then .lookup else .absent }

theorem prepared_token (budget allocator : Nat) (source target buffer : View) (values : List NodeId)
    (allocated : Bool) (origin : NormalizationOwnership.Origin) (before after : Session σ) (handle : Handle)
    (executed : Normalization.prepare normalizationOwnershipCode budget allocator buffer.length source target values allocated before =
      (.ok handle, after)) : token origin handle = preparedToken origin source buffer := by
  have result := congrArg Prod.fst executed
  cases copied : Compiler.Extraction.InsertionSort.Copied.run budget before.memory source target with
  | mk outcome memory =>
    cases outcome with
    | error failure => simp [Normalization.prepare, copied] at result
    | ok returned =>
      cases returned
      simp only [Normalization.prepare, copied, Except.ok.injEq] at result
      subst handle
      cases owned : normalizationOwnershipCode.ownTemporary.test source.length buffer.length <;>
        simp [token, preparedToken, owned]

def preparedContinuation (external : External σ) (budget allocator : Nat) (source buffer : View) (values : List NodeId)
    (origin : NormalizationOwnership.Origin) (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ) :=
  let lookup := preparedToken origin source buffer
  let p := primitives external budget allocator source buffer values
  let (prepared, reached) := p.prepare lookup ⟨before, handle, none, none⟩
  let (result, after) : NormalizationOwnership.PreparedResult Failure × State σ := match prepared with
    | .error failure => (.error (failure, lookup), reached)
    | .ok () =>
      let (result, after) := normalizationOwnershipCode.continueWith p.toPrimitives exit lookup reached
      (.ok result, after)
  (observe result after, after.session)

/-- Successful preparation supplies the actual native handle to the transfer
adapter. A semantic fault returns immediately with partial writes; no release
callback or later allocation is evaluated. -/
theorem prepared_continuation_eq (external : External σ) (budget allocator : Nat) (source buffer : View) (values : List NodeId)
    (origin : NormalizationOwnership.Origin) (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ) :
    preparedContinuation external budget allocator source buffer values origin exit handle before =
      let target := if origin = .scratch then bufferPrefix buffer source.length else handle.items
      let (result, reached) := Normalization.prepare normalizationOwnershipCode budget allocator buffer.length source target values
        (origin == .allocation) before
      match result with
      | .error failure => (some (Except.error failure : Except Failure Outcome), reached)
      | .ok handle =>
        let (result, after) := Normalization.continueWith normalizationOwnershipCode external allocator exit handle reached
        (some result, after) := by
  let target := if origin = .scratch then bufferPrefix buffer source.length else handle.items
  cases prepared : Normalization.prepare normalizationOwnershipCode budget allocator buffer.length source target values
      (origin == .allocation) before with
  | mk result reached =>
    have prepared' := prepared
    dsimp only [target] at prepared'
    cases result with
    | error failure =>
      simp [preparedContinuation, primitives, prepare, preparedToken, prepared', observe]
    | ok nativeHandle =>
      have aligned := prepared_token budget allocator source target buffer values (origin == .allocation) origin before reached nativeHandle prepared
      have continuation := continued_eq external budget allocator source buffer values origin exit nativeHandle reached
      unfold continued at continuation
      rw [aligned] at continuation
      simpa only [preparedContinuation, primitives, prepare, preparedToken, prepared'] using continuation

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
