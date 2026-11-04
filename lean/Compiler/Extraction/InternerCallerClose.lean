/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceClose
import Compiler.Extraction.InternerCallerTakeInitialization
import Compiler.Extraction.InternerCallerCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open ResourceAdapter NormalizationOwnership.Trace

/-- Bind descriptors to the current native caller, after any graph work. -/
def capture (external : External σ) (allocator : Nat) (lookup : NormalizationOwnership.State)
    (phase : NormalizationOwnership.Exit) (handle : Handle) (before : OwnedCall.State σ) :=
  normalizationOwnershipCode.closeWith
    (record (primitives external 0 allocator handle.items handle.items handle.values)).release phase lookup
    ⟨⟨before.world.memory, handle, before.scope.slice, none⟩, []⟩

/-- Legal caller shapes have at most one native free. A rejected free retains
the original descriptors; successful deinit clears the lookup. -/
def observe (before : OwnedCall.State σ) (after : ResourceAdapter.State σ) :
    Option (Except Fault Unit × OwnedCall.State σ) :=
  let reached := { before with world := { before.world with memory := after.session } }
  match after.rejected with
  | some .missingSlice => none
  | some (.memory failure) => some (.error (memoryFault failure), reached)
  | none => some (.ok (), { reached with scope :=
      ⟨none, if before.scope.handedOff then before.scope.slice else none, before.scope.handedOff⟩ })

theorem lookup_spec (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : World σ) :
    let native : OwnedCall.State σ := ⟨before, { lookup := some handle }⟩
    observe native (capture external allocator (token origin handle) .lookup handle native).2.effects =
      some (cleanup external allocator native) := by
  cases owned : handle.owned with
  | none => simp [capture, observe, NormalizationOwnership.Code.closeWith, NormalizationOwnership.Code.deinitWith,
      normalizationOwnershipCode, token, owned, cleanup, deinit, deinitialize]
  | some slice =>
    cases freed : free external allocator slice before.memory with
    | mk result reached =>
      cases result <;> simp [capture, observe, NormalizationOwnership.Code.closeWith, NormalizationOwnership.Code.deinitWith,
        normalizationOwnershipCode, token, owned, cleanup, deinit, deinitialize, record, primitives,
        ResourceAdapter.release, freed]

theorem taken_spec (external : External σ) (allocator : Nat) (lookup : NormalizationOwnership.State)
    (handle : Handle) (slice : ArgumentSlice) (handedOff : Bool) (before : World σ)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (owner : lookup.owner = .caller) :
    let native : OwnedCall.State σ := ⟨before, ⟨some handle, some slice, handedOff⟩⟩
    observe native (capture external allocator lookup (if handedOff then .transfer else .cleanup) handle native).2.effects =
      some (cleanup external allocator native) := by
  cases handedOff with
  | true => simp [capture, observe, NormalizationOwnership.Code.closeWith, NormalizationOwnership.Code.deinitWith,
      normalizationOwnershipCode, unowned, cleanup, deinit, deinitialize, detached]
  | false =>
    cases freed : free external allocator slice before.memory with
    | mk result reached =>
      cases result <;> simp [capture, observe, NormalizationOwnership.Code.closeWith, NormalizationOwnership.Code.deinitWith,
        normalizationOwnershipCode, unowned, move_owned, owner, cleanup, deinit, deinitialize, detached,
        record, primitives, ResourceAdapter.release, outputSlice, freed]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
