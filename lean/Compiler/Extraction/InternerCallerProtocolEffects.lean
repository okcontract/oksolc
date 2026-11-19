/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesEffects
import Compiler.Extraction.InternerCallerMemoryEffects
import Compiler.Extraction.InternerCallerProtocolScope

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open NormalizationOwnership.Trace

variable {left : External σ} {right : External τ} {project : σ → τ}
  (mapped : left.Transport right project)
include mapped

theorem Initialization.capture_transport (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (before : Session σ) :
    Initialization.capture right budget allocator commutative source buffer values (before.mapEffects project) =
      ((Initialization.capture left budget allocator commutative source buffer values before).1,
       (Initialization.capture left budget allocator commutative source buffer values before).2.mapEffects
         (ResourceAdapter.State.mapEffects project)) :=
  NormalizationOwnership.init_prepared_transport normalizationOwnershipCode _ _ _
    (record_map (ResourceAdapter.primitives_transport mapped budget allocator source buffer values))
    commutative source.length buffer.length ⟨ResourceAdapter.initial source values before, []⟩

theorem Take.capture_transport (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (handle : Handle) (before : Session σ) :
    Take.capture right allocator origin handle (before.mapEffects project) =
      ((Take.capture left allocator origin handle before).1,
       (Take.capture left allocator origin handle before).2.mapEffects (ResourceAdapter.State.mapEffects project)) :=
  NormalizationOwnership.take_transport normalizationOwnershipCode _ _ _
    ((record_map (ResourceAdapter.primitives_transport mapped 0 allocator handle.items handle.items handle.values)).allocate .duplicate)
    (ResourceAdapter.token origin handle) ⟨⟨before, handle, none, none⟩, []⟩

theorem Close.capture_transport (allocator : Nat) (lookup : NormalizationOwnership.State)
    (phase : NormalizationOwnership.Exit) (handle : Handle) (before : OwnedCall.State σ) :
    Close.capture right allocator lookup phase handle (before.mapEffects project) =
      ((Close.capture left allocator lookup phase handle before).1,
       (Close.capture left allocator lookup phase handle before).2.mapEffects (ResourceAdapter.State.mapEffects project)) :=
  NormalizationOwnership.close_transport normalizationOwnershipCode _ _ _
    (record_map (ResourceAdapter.primitives_transport mapped 0 allocator handle.items handle.items handle.values)).release
    phase lookup ⟨⟨before.world.memory, handle, before.scope.slice, none⟩, []⟩

namespace ProtocolTrace

/-- Retain the complete caller observation while projecting native private
effects. In particular, this is not event erasure or a scope reset. -/
def Recorded.mapEffects (project : σ → τ) (before : Recorded σ) : Recorded τ :=
  ⟨before.native.mapEffects project, before.tokens, before.events⟩

omit mapped in
theorem map_scope (project : σ → τ) (before : Recorded σ) :
    scopeView (before.mapEffects project) = scopeView before := rfl

omit mapped in
theorem record_transport {left : OwnedCall.Action σ α} {right : OwnedCall.Action τ α}
    (native : Effect.Transport (OwnedCall.State.mapEffects project) left right)
    {observed : Observation σ} {other : Observation τ}
    (observations : ∀ before tokens, other (before.mapEffects project) tokens = observed before tokens) :
    Effect.Transport (Recorded.mapEffects project) (record left observed) (record right other) := by
  intro before
  simp only [record, Recorded.mapEffects, observations]
  rw [native before.native]

namespace EffectTransport

theorem initialization (budget allocator : Nat) (source buffer : View) (request : Interner.Request)
    (before : OwnedCall.State σ) (tokens : Tokens) :
    ProtocolTrace.initialization right budget allocator source buffer request (before.mapEffects project) tokens =
      ProtocolTrace.initialization left budget allocator source buffer request before tokens := by
  unfold ProtocolTrace.initialization
  cases Interner.Scoped.commutative request.item with
  | error fault => rfl
  | ok commutative =>
    dsimp only
    simp only [show (before.mapEffects project).world.memory = before.world.memory.mapEffects project from rfl]
    rw [Initialization.capture_transport mapped]
    rfl

theorem taking (allocator : Nat) (before : OwnedCall.State σ) (tokens : Tokens) :
    ProtocolTrace.taking right allocator (before.mapEffects project) tokens =
      ProtocolTrace.taking left allocator before tokens := by
  unfold ProtocolTrace.taking
  simp only [show (before.mapEffects project).scope = before.scope from rfl]
  cases before.scope.lookup with
  | none => rfl
  | some handle =>
    cases tokens.lookup with
    | none => rfl
    | some lookup =>
      dsimp only
      simp only [show (before.mapEffects project).world.memory = before.world.memory.mapEffects project from rfl]
      rw [Take.capture_transport mapped]; rfl

theorem closing (allocator : Nat) (before : OwnedCall.State σ) (tokens : Tokens) :
    ProtocolTrace.closing right allocator (before.mapEffects project) tokens =
      ProtocolTrace.closing left allocator before tokens := by
  unfold ProtocolTrace.closing
  simp only [show (before.mapEffects project).scope = before.scope from rfl]
  cases before.scope.lookup with
  | none => rfl
  | some handle =>
    cases tokens.lookup with
    | none => rfl
    | some lookup => dsimp only; rw [Close.capture_transport mapped]; rfl

end EffectTransport

/-- Only local graph observations remain premises. Caller control, native
normalization and cleanup observations are derived, including failure paths. -/
structure GraphObservations.Transport (left : GraphObservations σ) (right : GraphObservations τ)
    (project : σ → τ) : Prop where
  simplify : ∀ key slice before, right.simplify key slice (before.mapEffects project) = left.simplify key slice before
  publish : ∀ key slice id before, right.publish key slice id (before.mapEffects project) = left.publish key slice id before
  insert : ∀ key slice deterministic before,
    right.insert key slice deterministic (before.mapEffects project) = left.insert key slice deterministic before

namespace EffectTransport

omit mapped in
theorem graph {left : ArgumentSlice → GraphAction σ α} {right : ArgumentSlice → GraphAction τ α}
    (native : ∀ slice, Effect.Transport (World.mapEffects project) (left slice) (right slice))
    {observed : ArgumentSlice → World σ → List ProtocolEvent} {other : ArgumentSlice → World τ → List ProtocolEvent}
    (events : ∀ slice before, other slice (before.mapEffects project) = observed slice before) :
    Effect.Transport (Recorded.mapEffects project)
      (record (OwnedCall.graph left) (graphObservation observed)) (record (OwnedCall.graph right) (graphObservation other)) := by
  apply record_transport (OwnedCall.EffectTransport.graph left right native)
  intro before tokens
  simp only [graphObservation, OwnedCall.State.mapEffects]
  cases before.scope.slice with
  | none => rfl
  | some slice => dsimp only; rw [events]

theorem findBody (budget allocator : Nat) {p : Primitives σ} {q : Primitives τ}
    (native : p.Transport q project) (queries : Queries)
    {ports : GraphObservations σ} {other : GraphObservations τ} (observed : ports.Transport other project)
    (source buffer : View) (request : Interner.Request) :
    Effect.Transport (Recorded.mapEffects project)
      (ProtocolTrace.findBody left budget allocator p queries ports source buffer request)
      (ProtocolTrace.findBody right budget allocator q queries other source buffer request) := by
  unfold ProtocolTrace.findBody Interner.FindCode.controlRun Interner.FindCode.controlOwned Interner.FindCode.controlMiss
  simp only [execution]
  repeat first
    | exact record_transport (Caller.EffectTransport.initLookup mapped budget allocator source buffer _)
        (initialization mapped budget allocator source buffer _)
    | exact record_transport (OwnedCall.EffectTransport.take mapped allocator) (taking mapped allocator)
    | exact graph (native.simplify _) (observed.simplify _)
    | exact graph (fun slice => native.publish _ slice _) (fun slice => observed.publish _ slice _)
    | exact graph (fun slice => native.insert _ slice _) (fun slice => observed.insert _ slice _)
    | exact record_transport (fun _ => rfl) (fun _ _ => rfl)
    | exact Effect.Transport.pure (Recorded.mapEffects project) _
    | apply Effect.Transport.bind (Recorded.mapEffects project)
    | split
    | intro value

theorem finish (allocator : Nat) (result : Except Fault α) :
    Effect.Transport (Recorded.mapEffects project)
      (ProtocolTrace.finish left allocator result) (ProtocolTrace.finish right allocator result) := by
  intro before
  unfold ProtocolTrace.finish
  split
  · rw [record_transport (OwnedCall.EffectTransport.cleanup mapped allocator) (closing mapped allocator) before]
  · rfl

theorem invoke (allocator : Nat) {action : Action σ α} {other : Action τ α}
    (body : Effect.Transport (Recorded.mapEffects project) action other) :
    Effect.Transport (Recorded.mapEffects project)
      (ProtocolTrace.invoke left allocator action) (ProtocolTrace.invoke right allocator other) := by
  intro before
  unfold ProtocolTrace.invoke
  rw [body before]
  exact finish mapped allocator (action before).1 (action before).2

/-- The same source caller now retains its entire capture across the host
projection: result, native locals, scoped tokens and ordered protocol events. -/
theorem find (budget allocator : Nat) {p : Primitives σ} {q : Primitives τ}
    (native : p.Transport q project) (queries : Queries)
    {ports : GraphObservations σ} {other : GraphObservations τ} (observed : ports.Transport other project)
    (source buffer : View) (request : Interner.Request) :
    Effect.Transport (Recorded.mapEffects project)
      (ProtocolTrace.find left budget allocator p queries ports source buffer request)
      (ProtocolTrace.find right budget allocator q queries other source buffer request) :=
  invoke mapped allocator (findBody mapped budget allocator native queries observed source buffer request)

end EffectTransport
end ProtocolTrace
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
