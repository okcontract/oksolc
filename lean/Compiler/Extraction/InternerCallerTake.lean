/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesTake
import Compiler.Extraction.NormalizationTraceTake
import Compiler.Extraction.NormalizationTraceMemory
import Compiler.Extraction.NormalizationHostTrace
import Compiler.Extraction.InternerOwnedMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open ResourceAdapter NormalizationOwnership.Trace

/-- Only the existing duplicate primitive is used. The preparation budget and
views are immaterial here: take performs neither preparation nor sorting. -/
def capture (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session σ) :=
  normalizationOwnershipCode.takeWith
    ((record (primitives external 0 allocator handle.items handle.items handle.values)).allocate .duplicate)
    (token origin handle) ⟨⟨before, handle, none, none⟩, []⟩

theorem capture_spec (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session σ) :
    let execution := capture external allocator origin handle before
    let native := Normalization.takeOwned normalizationOwnershipCode external allocator handle before
    (observeTake execution.1 execution.2.effects, execution.2.effects.session) = (some native.1, native.2) := by
  have erased := NormalizationOwnership.take_transport normalizationOwnershipCode
    ((record (primitives external 0 allocator handle.items handle.items handle.values)).allocate .duplicate)
    ((primitives external 0 allocator handle.items handle.items handle.values).allocate .duplicate) Recorded.effects
    (fun before => (record_transport _).allocate .duplicate before) (token origin handle) ⟨⟨before, handle, none, none⟩, []⟩
  have spec := take_spec external allocator origin handle before
  dsimp only [primitives] at erased
  have observed := congrArg (fun result : (Bool × NormalizationOwnership.State) × ResourceAdapter.State σ =>
    (observeTake result.1 result.2, result.2.session)) erased
  exact observed.symm.trans spec

theorem recorded_erases (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session (HostTrace.Recorded σ)) :
    let execution := capture (HostTrace.record external) allocator origin handle before
    let native := Normalization.takeOwned normalizationOwnershipCode external allocator handle
      (before.mapEffects HostTrace.Recorded.effects)
    (some native.1, native.2) =
      (observeTake execution.1 execution.2.effects, execution.2.effects.session.mapEffects HostTrace.Recorded.effects) := by
  have spec := capture_spec (HostTrace.record external) allocator origin handle before
  have mapped := congrArg (fun pair : Option (Except Failure (ArgumentSlice × Handle)) × Session (HostTrace.Recorded σ) =>
    (pair.1, pair.2.mapEffects HostTrace.Recorded.effects)) spec
  have native := (HostTrace.transport external).takeOwned normalizationOwnershipCode allocator handle before
  rw [native]
  exact mapped.symm

theorem caller (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : OwnedCall.State σ) (present : before.scope.lookup = some handle) :
    let execution := capture external allocator origin handle before.world.memory
    (observeTake execution.1 execution.2.effects).map (fun result =>
      let world := { before.world with memory := execution.2.effects.session }
      match result with
      | .error failure => (.error (memoryFault failure), { before with world })
      | .ok (slice, remaining) => (.ok (), ⟨world, ⟨some remaining, some slice, false⟩⟩)) =
      some (OwnedCall.take external allocator before) := by
  have spec := capture_spec external allocator origin handle before.world.memory
  have mapped := congrArg (fun pair : Option (Except Failure (ArgumentSlice × Handle)) × Session σ =>
    (pair.1.map (fun result =>
      let world := { before.world with memory := pair.2 }
      match result with
      | .error failure => (.error (memoryFault failure), { before with world })
      | .ok (slice, remaining) => (.ok (), ⟨world, ⟨some remaining, some slice, false⟩⟩)) : Option (Except Fault Unit × OwnedCall.State σ))) spec
  simpa only [OwnedCall.take, present, Option.map] using mapped

theorem capture_replays_at (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session σ) (leading suffix : List (Event Failure)) :
    let execution := capture external allocator origin handle before
    normalizationOwnershipCode.takeWith
      ((replay (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)).allocate .duplicate)
      (token origin handle) leading.length = (execution.1, leading.length + execution.2.events.length) :=
  take_replay_at (primitives external 0 allocator handle.items handle.items handle.values) (.preparation .incomplete)
    (token origin handle) ⟨before, handle, none, none⟩ leading suffix

def checked (execution : (Bool × NormalizationOwnership.State) × Recorded (ResourceAdapter.State σ) Failure)
    (leading suffix : List (Event Failure)) (lookup : NormalizationOwnership.State) (items : List NodeId) (graph : Interner.Heap) :
    Except TraceBridge.Rejection (Except Interner.Error Unit × Interner.Scoped.Session) :=
  let events := leading ++ (execution.2.events ++ suffix)
  let replayed := normalizationOwnershipCode.takeWith ((replay events (.preparation .incomplete)).allocate .duplicate)
    lookup graph.allocationCursor
  TraceBridge.checkPhysical execution.2.effects (Scope.admit events (.ok replayed.1, replayed.2)
    (Interner.Scoped.take (Scope.resources events (.preparation .incomplete)) ⟨⟨some lookup, items, .lookup⟩, graph⟩))

theorem checked_scope (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session σ) (leading suffix : List (Event Failure)) (graph : Interner.Heap)
    (scope : Except Interner.Error Unit × Interner.Scoped.Session) (start : graph.allocationCursor = leading.length)
    (accepted : checked (capture external allocator origin handle before) leading suffix (token origin handle) handle.values graph = .ok scope) :
    let execution := capture external allocator origin handle before
    execution.2.effects.rejected = none ∧
    scope = (if execution.1.1 then .ok () else .error .outOfMemory,
      ⟨⟨some execution.1.2, handle.values, if execution.1.1 then .cleanup else .lookup⟩,
        { graph with allocationCursor := leading.length + execution.2.events.length }⟩) := by
  obtain ⟨clean, admitted⟩ := TraceBridge.check_physical_sound _ _ _ accepted
  obtain ⟨_, _, _, projected⟩ := Scope.admit_sound _ _ _ _ admitted
  have replayed := capture_replays_at external allocator origin handle before leading suffix
  dsimp only [replay] at replayed
  refine ⟨clean, ?_⟩
  rw [projected]
  simp only [Interner.Scoped.take, Scope.resources, start, replayed]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
