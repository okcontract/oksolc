/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesLifetime

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache

/-- Observe a live transfer, before handoff or deferred cleanup. A temporary
stays in the adapter's original descriptor; duplication records its returned
slice and remaining handle. Neither descriptor is a second allocation. -/
def observeTake (result : Bool × NormalizationOwnership.State) (after : State σ) :
    Option (Except Failure (ArgumentSlice × Handle)) :=
  match after.rejected with
  | some (.memory failure) => some (.error failure)
  | some .missingSlice => none
  | none =>
    if result.1 then
      match after.transferred with
      | some slice => some (.ok (slice, after.handle))
      | none => after.handle.owned.map (fun slice => .ok (slice, { after.handle with owned := none }))
    else some (.error .outOfMemory)

/-- Exact live correspondence for every native outcome, including partial
duplication faults. Allocation failure is not assumed to leave memory unchanged. -/
theorem take_spec (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session σ) :
    let execution := normalizationOwnershipCode.takeWith (allocate external allocator handle.values .duplicate)
      (token origin handle) ⟨before, handle, none, none⟩
    let native := Normalization.takeOwned normalizationOwnershipCode external allocator handle before
    (observeTake execution.1 execution.2, execution.2.session) = (some native.1, native.2) := by
  cases owned : handle.owned with
  | some slice => simp [NormalizationOwnership.Code.takeWith, token, owned, normalizationOwnershipCode,
      observeTake, Normalization.takeOwned]
  | none =>
    cases taken : Normalization.takeOwned normalizationOwnershipCode external allocator handle before with
    | mk result reached =>
      cases result with
      | error failure =>
        cases failure <;> simp [NormalizationOwnership.Code.takeWith, token, owned, allocate, failed,
          taken, observeTake]
      | ok pair =>
        rcases pair with ⟨slice, remaining⟩
        simp [NormalizationOwnership.Code.takeWith, token, owned, allocate, taken, observeTake]

theorem observe_take_result (result : Bool × NormalizationOwnership.State) (after : State σ)
    (native : Except Failure (ArgumentSlice × Handle)) (clean : after.rejected = none)
    (observed : observeTake result after = some native) :
    native.map (fun _ => ()) = if result.1 then .ok () else .error .outOfMemory := by
  cases success : result.1
  · simpa [observeTake, clean, success, Except.map] using congrArg (fun value => value.map (Except.map (fun _ => ()))) observed.symm
  · cases transferred : after.transferred with
    | some slice => simp [observeTake, clean, success, transferred] at observed; subst native; rfl
    | none =>
      cases owned : after.handle.owned with
      | none => simp [observeTake, clean, success, transferred, owned] at observed
      | some slice => simp [observeTake, clean, success, transferred, owned] at observed; subst native; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
