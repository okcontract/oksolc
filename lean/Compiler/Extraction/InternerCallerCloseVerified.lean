/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerClose

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

theorem observe_success (before after : OwnedCall.State σ) (physical : ResourceAdapter.State σ)
    (observed : observe before physical = some (.ok (), after)) :
    physical.rejected = none ∧ after.world.memory = physical.session := by
  cases rejection : physical.rejected with
  | none =>
    refine ⟨rfl, ?_⟩
    simp only [observe, rejection] at observed
    exact (congrArg (fun pair : Except Fault Unit × OwnedCall.State σ => pair.2.world.memory)
      (Option.some.inj observed)).symm
  | some error => cases error <;> simp [observe, rejection] at observed

theorem capture_replays_at (external : External σ) (allocator : Nat) (lookup : NormalizationOwnership.State)
    (phase : NormalizationOwnership.Exit) (handle : Handle) (before : OwnedCall.State σ)
    (leading suffix : List (Event Failure)) :
    let execution := capture external allocator lookup phase handle before
    normalizationOwnershipCode.closeWith (replay (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)).release
      phase lookup leading.length = (execution.1, leading.length + execution.2.events.length) :=
  close_replay_at (primitives external 0 allocator handle.items handle.items handle.values) (.preparation .incomplete)
    phase lookup ⟨before.world.memory, handle, before.scope.slice, none⟩ leading suffix

def checked (execution : NormalizationOwnership.State × Recorded (ResourceAdapter.State σ) Failure)
    (leading suffix : List (Event Failure)) (lookup : NormalizationOwnership.State) (phase : NormalizationOwnership.Exit)
    (items : List NodeId) (graph : Interner.Heap) : Except TraceBridge.Rejection Interner.Scoped.Session :=
  let events := leading ++ (execution.2.events ++ suffix)
  let replayed := normalizationOwnershipCode.closeWith (replay events (.preparation .incomplete)).release
    phase lookup graph.allocationCursor
  TraceBridge.checkPhysical execution.2.effects (Scope.admit events (.ok replayed.1, replayed.2)
    (Interner.Scoped.close (Scope.resources events (.preparation .incomplete)) ⟨⟨some lookup, items, phase⟩, graph⟩))

/-- Exact native correspondence plus successful reached-state cleanup supplies
physical admission. Replay derives the cursor and the complete scoped result. -/
theorem checked_of_cleanup (external : External σ) (allocator : Nat) (lookup : NormalizationOwnership.State)
    (phase : NormalizationOwnership.Exit) (handle : Handle) (before after : OwnedCall.State σ)
    (leading suffix : List (Event Failure)) (items : List NodeId) (graph : Interner.Heap)
    (start : graph.allocationCursor = leading.length)
    (corresponds : observe before (capture external allocator lookup phase handle before).2.effects =
      some (cleanup external allocator before))
    (closed : cleanup external allocator before = (.ok (), after)) :
    let execution := capture external allocator lookup phase handle before
    let scope := Interner.Scoped.close (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete))
      ⟨⟨some lookup, items, phase⟩, graph⟩
    after.world.memory = execution.2.effects.session ∧
    checked execution leading suffix lookup phase items graph = .ok scope ∧
    scope = ⟨⟨some execution.1, items, phase⟩, { graph with allocationCursor := leading.length + execution.2.events.length }⟩ := by
  rw [closed] at corresponds
  obtain ⟨clean, memory⟩ := observe_success before after _ corresponds
  have replayed := capture_replays_at external allocator lookup phase handle before leading suffix
  have within : ¬ (leading ++ ((capture external allocator lookup phase handle before).2.events ++ suffix)).length <
      leading.length + (capture external allocator lookup phase handle before).2.events.length := by
    simp only [List.length_append]; omega
  refine ⟨memory, ?_, ?_⟩
  · simp only [checked, TraceBridge.checkPhysical, clean, start, replayed, Scope.admit, if_neg within, Except.mapError]
  · rw [Scope.close_projection, start, replayed]

theorem lookup_verified (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (ready : Ready allocator source original handle before.memory) (leading suffix : List (Event Failure)) :
    let native : OwnedCall.State σ := ⟨before, { lookup := some handle }⟩
    let execution := capture external allocator (token origin handle) .lookup handle native
    ∃ after, cleanup external allocator native = (.ok (), after) ∧
      Good source original after.world ∧ Closed after.scope ∧ after.world.graph = before.graph ∧
      after.world.memory = execution.2.effects.session ∧
      checked execution leading suffix (token origin handle) .lookup handle.values
        { before.graph with allocationCursor := leading.length } =
        .ok ⟨⟨some execution.1, handle.values, .lookup⟩,
          { before.graph with allocationCursor := leading.length + execution.2.events.length }⟩ := by
  obtain ⟨after, closed, good, locals, graph, _⟩ := cleanup_lookup external allocator source original handle before ready
  have linked := checked_of_cleanup external allocator (token origin handle) .lookup handle
    ⟨before, { lookup := some handle }⟩ after leading suffix handle.values
    { before.graph with allocationCursor := leading.length } rfl (lookup_spec external allocator origin handle before) closed
  exact ⟨after, closed, good, locals, graph, linked.1, by simpa only [linked.2.2] using linked.2.1⟩

theorem taken_verified (external : External σ) (allocator : Nat) (lookup : NormalizationOwnership.State)
    (source : View) (original : List NodeId) (handle : Handle) (slice : ArgumentSlice) (handedOff : Bool) (before : World σ)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (owner : lookup.owner = .caller)
    (good : Good source original before) (live : handedOff = false → SliceValid allocator before.memory.heap slice)
    (separate : original ≠ [] → source.allocation ≠ slice.address) (leading suffix : List (Event Failure)) :
    let native : OwnedCall.State σ := ⟨before, ⟨some handle, some slice, handedOff⟩⟩
    let phase : NormalizationOwnership.Exit := if handedOff then .transfer else .cleanup
    let execution := capture external allocator lookup phase handle native
    ∃ after, cleanup external allocator native = (.ok (), after) ∧
      CleanupPost external allocator source original slice native after ∧
      after.world.memory = execution.2.effects.session ∧
      checked execution leading suffix lookup phase handle.values { before.graph with allocationCursor := leading.length } =
        .ok ⟨⟨some execution.1, handle.values, phase⟩,
          { before.graph with allocationCursor := leading.length + execution.2.events.length }⟩ := by
  obtain ⟨after, closed, post⟩ := cleanup_taken external allocator source original slice handle
    ⟨before, ⟨some handle, some slice, handedOff⟩⟩ rfl detached rfl good live separate
  have linked := checked_of_cleanup external allocator lookup (if handedOff then .transfer else .cleanup) handle
    ⟨before, ⟨some handle, some slice, handedOff⟩⟩ after leading suffix handle.values
    { before.graph with allocationCursor := leading.length } rfl
    (taken_spec external allocator lookup handle slice handedOff before detached unowned owner) closed
  exact ⟨after, closed, post, linked.1, by simpa only [linked.2.2] using linked.2.1⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
