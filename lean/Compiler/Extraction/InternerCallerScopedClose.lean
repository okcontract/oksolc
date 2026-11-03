/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerScopeProjection

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ScopeProjection
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace Recursive

/-- Identify checked cleanup with closing the actually projected scoped state.
The physical completion and the cursor describe this same reached body. -/
theorem close_completion (external : External σ) (allocator : Nat) (source : View) (original : List NodeId)
    (lookup : NormalizationOwnership.State) (handle : Handle) (slice : ArgumentSlice)
    (body : Except Fault α × OwnedCall.State σ) (cursor : World σ → Nat)
    (leading suffix : List (Event Failure)) (logical : Interner.Scoped.Session)
    (completion : Close.Completion external allocator source original lookup handle slice body leading suffix)
    (projected : logical = scopeAt (cursorGraph cursor) lookup handle.values body.2)
    (start : cursor body.2.world = leading.length) :
    let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
    let execution := Close.capture external allocator lookup phase handle body.2
    let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
    ∃ after, finish external allocator body.1 body.2 = (body.1, after) ∧
      CleanupPost external allocator source original slice body.2 after ∧
      after.world.memory = execution.2.effects.session ∧
      Close.checked execution leading suffix lookup logical.scope.phase logical.scope.items logical.heap =
        .ok (Interner.Scoped.close resources logical) := by
  obtain ⟨after, finished, post, reached, accepted⟩ := completion
  have shape : scopeAt (cursorGraph cursor) lookup handle.values body.2 =
      (⟨⟨some lookup, handle.values, if body.2.scope.handedOff then .transfer else .cleanup⟩,
        { body.2.world.graph with allocationCursor := leading.length }⟩ : Interner.Scoped.Session) := by
    exact (show (⟨⟨some lookup, handle.values, if body.2.scope.handedOff then .transfer else .cleanup⟩,
      { body.2.world.graph with allocationCursor := cursor body.2.world }⟩ : Interner.Scoped.Session) =
      ⟨⟨some lookup, handle.values, if body.2.scope.handedOff then .transfer else .cleanup⟩,
        { body.2.world.graph with allocationCursor := leading.length }⟩ by rw [start])
  refine ⟨after, finished, post, reached, ?_⟩
  rw [projected, shape]
  obtain ⟨_, admittedScope⟩ := TraceBridge.check_physical_sound _ _ _ accepted
  obtain ⟨_, _, _, closes⟩ := Scope.admit_sound _ _ _ _ admittedScope
  rw [← closes]
  exact accepted

/-- Close the state actually reached by scoped miss control. Graph simulation
and lifetime contracts have separate duties; both apply to the same native
continuation. The observed cursor must meet the recorded cleanup segment. -/
theorem closed_miss_after_take (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (ready : Ready allocator source original handle before.memory) (admitted : Admitted external)
    (physical : Primitives σ) (memory : Contracts allocator source original physical)
    (cursor : World σ → Nat) (predicate : World σ → Prop) (model : Interner.Primitives)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (aligned : key.arguments = handle.values)
    (graphs : ∀ slice, key.arguments = slice.items → Graphs (cursorGraph cursor) predicate physical model key slice deterministic)
    (succeeded : (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).1 = .ok ())
    (initial : predicate (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2.world)
    (completed : ordinary (Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic
      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2).1 = true)
    (leading suffix : List (Event Failure))
    (start : cursor (Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic
      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2).2.world = leading.length) :
    let called := OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩
    let lookup := (Take.capture external allocator origin handle before.memory).1.2
    let body := Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic called.2
    ∃ slice remaining after, called.2.scope = ⟨some remaining, some slice, false⟩ ∧
      Normalization.Taken allocator source original handle before.memory slice remaining called.2.world.memory ∧
      finish external allocator body.1 body.2 = (body.1, after) ∧
      CleanupPost external allocator source original slice body.2 after ∧ predicate body.2.world ∧
      let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
      let execution := Close.capture external allocator lookup phase remaining body.2
      let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
      let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources model) request key deterministic
        (scopeAt (cursorGraph cursor) lookup remaining.values called.2)
      body.1 = logical.1.mapError Fault.language ∧
      logical.2 = scopeAt (cursorGraph cursor) lookup remaining.values body.2 ∧
      after.world.memory = execution.2.effects.session ∧
      Close.checked execution leading suffix lookup logical.2.scope.phase logical.2.scope.items logical.2.heap =
        .ok (Interner.Scoped.close resources logical.2) := by
  obtain ⟨slice, remaining, locals, taken, completion⟩ :=
    Close.miss_after_take external allocator origin source original handle before ready admitted physical memory
      request key deterministic aligned succeeded completed leading suffix
  let called := OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩
  let lookup := (Take.capture external allocator origin handle before.memory).1.2
  let body := Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic called.2
  let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
  let execution := Close.capture external allocator lookup phase remaining body.2
  let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
  have frame : Frame predicate remaining slice called.2 := by
    exact ⟨congrArg Local.lookup locals, congrArg Local.slice locals, initial⟩
  have projected := miss (cursorGraph cursor) predicate external allocator physical model resources
    lookup remaining.values remaining slice request key deterministic (graphs slice (aligned.trans taken.values.symm))
    called.2 frame completed
  obtain ⟨after, finished, post, reached, accepted⟩ := close_completion external allocator source original lookup remaining slice
    body cursor leading suffix _ completion projected.2.2.symm start
  exact ⟨slice, remaining, after, locals, taken, finished, post, projected.1.2.2,
    projected.2.1, projected.2.2.symm, reached, accepted⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ScopeProjection
