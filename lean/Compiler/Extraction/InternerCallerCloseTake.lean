/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerCloseVerified

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace

theorem taken_token (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session σ)
    (succeeded : (Take.capture external allocator origin handle before).1.1 = true) :
    (Take.capture external allocator origin handle before).1.2.owned = false ∧
      (Take.capture external allocator origin handle before).1.2.owner = .caller := by
  cases owned : handle.owned with
  | some slice => simp [Take.capture, NormalizationOwnership.Code.takeWith, token, owned, NormalizationOwnership.State.move, normalizationOwnershipCode]
  | none =>
    have ready : NormalizationOwnership.Ready (token origin handle) := by
      simp [NormalizationOwnership.Ready, token, owned]
    have taken := NormalizationOwnership.take_with_success
      ((record (primitives external 0 allocator handle.items handle.items handle.values)).allocate .duplicate)
      (⟨⟨before, handle, none, none⟩, []⟩ : Recorded (ResourceAdapter.State σ) Failure)
      (Take.capture external allocator origin handle before).2 (token origin handle)
      (Take.capture external allocator origin handle before).1.2 ready (by rw [← succeeded]; rfl)
    exact ⟨taken.2.2.1, taken.2.2.2⟩

/-- The native finish result, lifetime postcondition, and checked scoped close
all refer to the same reached continuation state. -/
def Completion (external : External σ) (allocator : Nat) (source : View) (original : List NodeId)
    (lookup : NormalizationOwnership.State) (handle : Handle) (slice : ArgumentSlice)
    (body : Except Fault α × OwnedCall.State σ) (leading suffix : List (Event Failure)) : Prop :=
  let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
  let execution := capture external allocator lookup phase handle body.2
  ∃ after, finish external allocator body.1 body.2 = (body.1, after) ∧
    CleanupPost external allocator source original slice body.2 after ∧
    after.world.memory = execution.2.effects.session ∧
    checked execution leading suffix lookup phase handle.values { body.2.world.graph with allocationCursor := leading.length } =
      .ok ⟨⟨some execution.1, handle.values, phase⟩,
        { body.2.world.graph with allocationCursor := leading.length + execution.2.events.length }⟩

/-- Complete cleanup at the actual reached state from its lifetime facts.
This boundary is shared by generic callbacks and the native pointwise step. -/
theorem of_post (external : External σ) (allocator : Nat) (source : View) (original : List NodeId)
    (lookup : NormalizationOwnership.State) (handle : Handle) (slice : ArgumentSlice)
    (body : Except Fault α × OwnedCall.State σ)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (owner : lookup.owner = .caller)
    (post : Post allocator source original slice handle body)
    (separate : original ≠ [] → source.allocation ≠ slice.address) (completed : ordinary body.1 = true)
    (leading suffix : List (Event Failure)) :
    Completion external allocator source original lookup handle slice body leading suffix := by
  have bodyShape : (⟨body.2.world, ⟨some handle, some slice, body.2.scope.handedOff⟩⟩ : OwnedCall.State σ) = body.2 := by
    have localShape : (⟨some handle, some slice, body.2.scope.handedOff⟩ : Local) = body.2.scope := by
      rw [← post.1, ← post.2.1]
    rw [localShape]
  have linked := taken_verified external allocator lookup source original handle slice body.2.scope.handedOff body.2.world
    detached unowned owner (post.2.2 completed).1 (post.2.2 completed).2 separate leading suffix
  dsimp only at linked
  rw [bodyShape] at linked
  obtain ⟨after, closed, clean, memory, accepted⟩ := linked
  refine ⟨after, ?_, clean, memory, accepted⟩
  simp only [finish, completed, ↓reduceIte, closed]

/-- Successful native take supplies both the detached native locals and the
token returned by that same recorded operation. This does not assume a free
token or equate local segment offsets with an invocation-wide cursor. -/
theorem take_success (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (ready : Ready allocator source original handle before.memory) (admitted : Admitted external)
    (succeeded : (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).1 = .ok ()) :
    let called := OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩
    let lookup := (Take.capture external allocator origin handle before.memory).1.2
    lookup.owned = false ∧ lookup.owner = .caller ∧
      ∃ slice remaining, called.2.scope = ⟨some remaining, some slice, false⟩ ∧
        Normalization.Taken allocator source original handle before.memory slice remaining called.2.world.memory := by
  have derived := Take.verified external allocator origin source original handle before [] [] ready admitted
  have coupled := derived.2
  have status := coupled.1
  have projected := Take.checked_scope external allocator origin handle before.memory [] []
    { before.graph with allocationCursor := 0 } _ rfl derived.1
  have logicalSuccess : (Take.capture external allocator origin handle before.memory).1.1 = true := by
    rw [projected.2, succeeded] at status
    cases result : (Take.capture external allocator origin handle before.memory).1.1 <;>
      simp [result, Except.mapError] at status ⊢
  have shape := taken_token external allocator origin handle before.memory logicalSuccess
  have successPost := coupled.2.2.2.2.2
  rw [succeeded] at successPost
  obtain ⟨slice, remaining, locals, taken⟩ := successPost
  exact ⟨shape.1, shape.2, slice, remaining, locals, taken⟩

theorem after_take (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (ready : Ready allocator source original handle before.memory) (admitted : Admitted external)
    (continuation : OwnedCall.State σ → Except Fault α × OwnedCall.State σ)
    (succeeded : (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).1 = .ok ())
    (preserved : ∀ slice remaining,
      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2.scope = ⟨some remaining, some slice, false⟩ →
      Normalization.Taken allocator source original handle before.memory slice remaining
        (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2.world.memory →
      Post allocator source original slice remaining
        (continuation (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2))
    (completed : ordinary (continuation (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2).1 = true)
    (leading suffix : List (Event Failure)) :
    let called := OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩
    let logical := (Take.capture external allocator origin handle before.memory).1.2
    ∃ slice remaining, called.2.scope = ⟨some remaining, some slice, false⟩ ∧
      Normalization.Taken allocator source original handle before.memory slice remaining called.2.world.memory ∧
      Completion external allocator source original logical remaining slice (continuation called.2) leading suffix := by
  obtain ⟨unowned, owner, slice, remaining, locals, taken⟩ :=
    take_success external allocator origin source original handle before ready admitted succeeded
  have post := preserved slice remaining locals taken
  exact ⟨slice, remaining, locals, taken,
    of_post external allocator source original _ remaining slice _ taken.detached unowned owner post taken.separate completed leading suffix⟩

/-- The actual miss continuation supplies the local preservation obligation
from the existing graph contracts, including recursive errors and handoff. -/
theorem miss_after_take (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (ready : Ready allocator source original handle before.memory) (admitted : Admitted external)
    (p : Primitives σ) (contracts : Contracts allocator source original p)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (aligned : key.arguments = handle.values)
    (succeeded : (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).1 = .ok ())
    (completed : ordinary (Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic
      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2).1 = true)
    (leading suffix : List (Event Failure)) :
    let called := OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩
    let logical := (Take.capture external allocator origin handle before.memory).1.2
    ∃ slice remaining, called.2.scope = ⟨some remaining, some slice, false⟩ ∧
      Normalization.Taken allocator source original handle before.memory slice remaining called.2.world.memory ∧
      Completion external allocator source original logical remaining slice
        (Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic called.2) leading suffix := by
  apply after_take external allocator origin source original handle before ready admitted
    (Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic) succeeded _ completed leading suffix
  intro slice remaining locals taken
  have held : Held allocator source original slice
      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2.world :=
    ⟨⟨taken.ready.valid, taken.ready.source⟩, taken.live, taken.separate⟩
  have post := miss_post external allocator p source original contracts request key slice remaining deterministic
    (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2.world
    (aligned.trans taken.values.symm) held
  have nativeState : (⟨(OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2.world,
      ⟨some remaining, some slice, false⟩⟩ : OwnedCall.State σ) =
      (OwnedCall.take external allocator ⟨before, { lookup := some handle }⟩).2 := by rw [← locals]
  simpa only [nativeState] using post

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close
