/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTake

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

/-- A ready native handle and permitted host responses exclude semantic take
faults. Ordinary refusal remains a clean, reached-state allocation outcome. -/
theorem capture_clean (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : Session σ)
    (ready : Ready allocator source original handle before) (admitted : Admitted external) :
    (capture external allocator origin handle before).2.effects.rejected = none := by
  cases owned : handle.owned with
  | some slice => simp [capture, NormalizationOwnership.Code.takeWith, token, owned]
  | none =>
    obtain ⟨result, reached, taken, post⟩ := take_refines external allocator source original handle before ready admitted
    cases result with
    | error failure =>
      cases failure with
      | outOfMemory => simp [capture, NormalizationOwnership.Code.takeWith, token, owned, record, primitives,
          ResourceAdapter.allocate, failed, taken]
      | allocation | preparation | release => exact False.elim post
    | ok pair =>
      rcases pair with ⟨slice, remaining⟩
      simp [capture, NormalizationOwnership.Code.takeWith, token, owned, record, primitives, ResourceAdapter.allocate, taken]

/-- The actual recorded segment always passes its check for ready inputs.
Replay supplies the exact cursor bound; the host may succeed or refuse. -/
theorem checked_ready (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : Session σ)
    (leading suffix : List (Event Failure)) (graph : Interner.Heap)
    (ready : Ready allocator source original handle before) (admitted : Admitted external)
    (start : graph.allocationCursor = leading.length) :
    let execution := capture external allocator origin handle before
    checked execution leading suffix (token origin handle) handle.values graph =
      .ok (Interner.Scoped.take (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete))
        ⟨⟨some (token origin handle), handle.values, .lookup⟩, graph⟩) := by
  have clean := capture_clean external allocator origin source original handle before ready admitted
  have replayed := capture_replays_at external allocator origin handle before leading suffix
  have within : ¬ (leading ++ ((capture external allocator origin handle before).2.events ++ suffix)).length <
      leading.length + (capture external allocator origin handle before).2.events.length := by
    simp only [List.length_append]
    omega
  simp only [checked, TraceBridge.checkPhysical, clean, start, replayed, Scope.admit, if_neg within, Except.mapError]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
