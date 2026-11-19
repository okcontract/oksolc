/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTakeAdmission
import Compiler.Extraction.InternerCallerInitializationVerified

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

/-- A successful take retains the actual live slice and detached lookup for
subsequent graph work. Ordinary OOM retains the ready lookup and reached state. -/
def Coupled (allocator : Nat) (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (cursor : Nat) (reached : Session σ) (logical : Bool × NormalizationOwnership.State)
    (called : Except Fault Unit × OwnedCall.State σ) (scope : Except Interner.Error Unit × Interner.Scoped.Session) : Prop :=
  called.1 = scope.1.mapError Fault.language ∧ called.2.world.graph = before.graph ∧
  called.2.world.memory = reached ∧
  scope.2 = ⟨⟨some logical.2, handle.values, if logical.1 then .cleanup else .lookup⟩,
    { before.graph with allocationCursor := cursor }⟩ ∧
  Valid called.2.world.memory ∧
  match called.1 with
  | .error fault => fault = .language .outOfMemory ∧ called.2.scope = { lookup := some handle } ∧
      Ready allocator source original handle called.2.world.memory
  | .ok () => ∃ slice remaining, called.2.scope = ⟨some remaining, some slice, false⟩ ∧
      Normalization.Taken allocator source original handle before.memory slice remaining called.2.world.memory

theorem coupled (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (leading suffix : List (Event Failure)) (scope : Except Interner.Error Unit × Interner.Scoped.Session)
    (ready : Ready allocator source original handle before.memory) (admitted : Admitted external)
    (accepted : checked (capture external allocator origin handle before.memory) leading suffix (token origin handle)
      handle.values { before.graph with allocationCursor := leading.length } = .ok scope) :
    let execution := capture external allocator origin handle before.memory
    Coupled allocator source original handle before (leading.length + execution.2.events.length)
      execution.2.effects.session execution.1 (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩) scope := by
  dsimp only [Coupled]
  let execution := capture external allocator origin handle before.memory
  obtain ⟨clean, projected⟩ := checked_scope external allocator origin handle before.memory leading suffix
    { before.graph with allocationCursor := leading.length } scope rfl accepted
  change execution.2.effects.rejected = none at clean
  obtain ⟨nativeResult, nativeAfter, taken, post⟩ := take_refines external allocator source original handle before.memory ready admitted
  have spec := capture_spec external allocator origin handle before.memory
  dsimp only at spec
  rw [taken] at spec
  have observation := congrArg Prod.fst spec
  have memory := congrArg Prod.snd spec
  change observeTake execution.1 execution.2.effects = some nativeResult at observation
  change execution.2.effects.session = nativeAfter at memory
  have status := observe_take_result execution.1 execution.2.effects nativeResult clean observation
  have callRun := caller external allocator origin handle (⟨before, { lookup := some handle }⟩ : OwnedCall.State σ) rfl
  change (observeTake execution.1 execution.2.effects).map _ = _ at callRun
  rw [observation] at callRun
  have callState := (Option.some.inj callRun).symm
  have scopedState := congrArg Prod.snd projected
  have scopedResult := congrArg Prod.fst projected
  change scope.1 = (if execution.1.1 then .ok () else .error .outOfMemory) at scopedResult
  rw [← memory] at post
  cases nativeResult with
  | error failure =>
    cases failure with
    | outOfMemory =>
      have failed : execution.1.1 = false := by
        cases success : execution.1.1 with
        | false => rfl
        | true => simp [success, Except.map] at status
      simp only [callState, scopedResult, failed, Bool.false_eq_true, ↓reduceIte, Except.mapError, memoryFault]
      exact ⟨True.intro, True.intro, True.intro, scopedState, post.2.2.2.valid, True.intro, True.intro, post.2.2.2⟩
    | allocation | preparation | release => exact False.elim post
  | ok pair =>
    rcases pair with ⟨slice, remaining⟩
    have succeeded : execution.1.1 = true := by
      cases success : execution.1.1 with
      | true => rfl
      | false => simp [success, Except.map] at status
    simp only [callState, scopedResult, succeeded, ↓reduceIte, Except.mapError]
    exact ⟨True.intro, True.intro, True.intro, scopedState, post.ready.valid, slice, remaining, rfl, post⟩

/-- General native/scoped take, with acceptance derived from the input contract
and the actual recorder. No allocation success or checked-result premise is used. -/
theorem verified (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (leading suffix : List (Event Failure)) (ready : Ready allocator source original handle before.memory)
    (admitted : Admitted external) :
    let execution := capture external allocator origin handle before.memory
    let graph := { before.graph with allocationCursor := leading.length }
    let scope := Interner.Scoped.take
      (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete))
      ⟨⟨some (token origin handle), handle.values, .lookup⟩, graph⟩
    checked execution leading suffix (token origin handle) handle.values graph = .ok scope ∧
    Coupled allocator source original handle before (leading.length + execution.2.events.length)
      execution.2.effects.session execution.1 (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩) scope := by
  have accepted := checked_ready external allocator origin source original handle before.memory leading suffix
    { before.graph with allocationCursor := leading.length } ready admitted rfl
  exact ⟨accepted, coupled external allocator origin source original handle before leading suffix _ ready admitted accepted⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take
