/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPhysicalDispatchPreservation
import Compiler.Extraction.InternerCallerCloseTake

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ScopeProjection
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Recursive

/-- During miss control, graph actions retain the caller's two descriptors.
Handoff changes only the local custody flag. Native graph invariants are kept
separate from the current slice's lifetime, which cleanup proves independently. -/
def Frame (predicate : World σ → Prop) (handle : Handle) (slice : ArgumentSlice) (before : OwnedCall.State σ) : Prop :=
  before.scope.lookup = some handle ∧ before.scope.slice = some slice ∧ predicate before.world

def scopeAt (observe : World σ → Interner.Heap) (lookup : NormalizationOwnership.State)
    (items : List NodeId) (before : OwnedCall.State σ) : Interner.Scoped.Session :=
  ⟨⟨some lookup, items, if before.scope.handedOff then .transfer else .cleanup⟩, observe before.world⟩

/-- Local graph simulation obligations. They concern actual primitive calls,
not the enclosing miss result or its cleanup. The simplify field is the
proper-child dispatch obligation; insertion/publication retain their duties. -/
structure Graphs (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (physical : Primitives σ) (model : Interner.Primitives) (key : Key) (slice : ArgumentSlice) (deterministic : Bool) : Prop where
  simplify : ProjectsAt observe predicate (physical.simplify key slice) (model.simplify key)
  publish : ∀ id, ProjectsAt observe predicate (physical.publish key slice id) (model.publish key id)
  insert : ProjectsAt observe predicate (physical.insert key slice deterministic) (model.insert key deterministic)

/-- Lift the actual first graph action without requiring its input facts at
all later worlds. Caller descriptors still refer to this same invocation. -/
theorem graph_at (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle) (slice : ArgumentSlice)
    (physical : ArgumentSlice → GraphAction σ α) (model : Interner.Action α)
    (before : OwnedCall.State σ) (frame : Frame predicate handle slice before)
    (projected : ordinary (physical slice before.world).1 = true → predicate (physical slice before.world).2 ∧
      (physical slice before.world).1 = (model (observe before.world)).1.mapError Fault.language ∧
      observe (physical slice before.world).2 = (model (observe before.world)).2) :
    ordinary (OwnedCall.graph physical before).1 = true →
      Frame predicate handle slice (OwnedCall.graph physical before).2 ∧
      (OwnedCall.graph physical before).1 = (Interner.Scoped.liftGraph model (scopeAt observe lookup items before)).1.mapError Fault.language ∧
      scopeAt observe lookup items (OwnedCall.graph physical before).2 =
        (Interner.Scoped.liftGraph model (scopeAt observe lookup items before)).2 := by
  intro completed
  simp only [OwnedCall.graph, frame.2.1] at completed ⊢
  have result := projected completed
  exact ⟨⟨frame.1, frame.2.1, result.1⟩, result.2.1, by
    simp only [scopeAt, Interner.Scoped.liftGraph]
    rw [result.2.2]⟩

theorem graph (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle) (slice : ArgumentSlice)
    (physical : ArgumentSlice → GraphAction σ α) (model : Interner.Action α)
    (projected : ProjectsAt observe predicate (physical slice) model) :
    ProjectsAt (scopeAt observe lookup items) (Frame predicate handle slice)
      (OwnedCall.graph physical) (Interner.Scoped.liftGraph model) :=
  fun before frame => graph_at observe predicate lookup items handle slice physical model before frame
    (projected before.world frame.2.2)

theorem handoff (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle) (slice : ArgumentSlice) :
    ProjectsAt (scopeAt observe lookup items) (Frame predicate handle slice)
      OwnedCall.handoff Interner.Scoped.handoff := by
  intro before frame _
  exact ⟨frame, rfl, rfl⟩

theorem pure (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle) (slice : ArgumentSlice) (value : α) :
    ProjectsAt (scopeAt observe lookup items) (Frame predicate handle slice)
      (Pure.pure value) (Pure.pure value) := fun _ frame _ => ⟨frame, rfl, rfl⟩

/-- The first simplify step consumes its actual input facts. Later graph
operations need only the retained invariant, so release/transfer can invalidate
the dispatch-only slice frame without invalidating this composition. -/
theorem miss_at (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (external : External σ) (allocator : Nat) (physical : Primitives σ) (model : Interner.Primitives)
    (resources : Interner.Scoped.Resources)
    (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle) (slice : ArgumentSlice)
    (request : Interner.Request) (key : Key) (deterministic : Bool)
    (before : OwnedCall.State σ) (frame : Frame predicate handle slice before)
    (simplifies : ordinary (physical.simplify key slice before.world).1 = true →
      predicate (physical.simplify key slice before.world).2 ∧
      (physical.simplify key slice before.world).1 = (model.simplify key (observe before.world)).1.mapError Fault.language ∧
      observe (physical.simplify key slice before.world).2 = (model.simplify key (observe before.world)).2)
    (publishes : ∀ id, ProjectsAt observe predicate (physical.publish key slice id) (model.publish key id))
    (inserts : ProjectsAt observe predicate (physical.insert key slice deterministic) (model.insert key deterministic)) :
    let executed := Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic before
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources model) request key deterministic
      (scopeAt observe lookup items before)
    ordinary executed.1 = true → Frame predicate handle slice executed.2 ∧
      executed.1 = logical.1.mapError Fault.language ∧ scopeAt observe lookup items executed.2 = logical.2 := by
  unfold Interner.FindCode.controlMiss
  simp only [OwnedCall.execution, Interner.Scoped.execution]
  split
  · apply projects_at_bind_from (scopeAt observe lookup items) (Frame predicate handle slice)
    · exact graph_at observe predicate lookup items handle slice _ _ before frame simplifies
    · intro value
      repeat first
        | exact graph observe predicate lookup items handle slice _ _ (publishes _)
        | exact graph observe predicate lookup items handle slice _ _ inserts
        | exact handoff observe predicate lookup items handle slice
        | exact pure observe predicate lookup items handle slice _
        | apply projects_at_bind (scopeAt observe lookup items) (Frame predicate handle slice)
        | split
        | intro value
  · exact (projects_at_bind (scopeAt observe lookup items) (Frame predicate handle slice) _ _ _ _
      (handoff observe predicate lookup items handle slice)
      (fun _ => graph observe predicate lookup items handle slice
        (fun slice => physical.insert key slice deterministic) (model.insert key deterministic) inserts)) before frame

/-- Exact ordinary control correspondence, including the reached handoff flag.
The existing generic bind relation compares every primitive at its reached
state; graph decisions and errors cannot be chosen independently on each side. -/
theorem miss (observe : World σ → Interner.Heap) (predicate : World σ → Prop)
    (external : External σ) (allocator : Nat) (physical : Primitives σ) (model : Interner.Primitives)
    (resources : Interner.Scoped.Resources)
    (lookup : NormalizationOwnership.State) (items : List NodeId) (handle : Handle) (slice : ArgumentSlice)
    (request : Interner.Request) (key : Key) (deterministic : Bool)
    (graphs : Graphs observe predicate physical model key slice deterministic) :
    ProjectsAt (scopeAt observe lookup items) (Frame predicate handle slice)
      (Interner.findCode.controlMiss (OwnedCall.execution external allocator physical) request key deterministic)
      (Interner.findCode.controlMiss (Interner.Scoped.execution resources model) request key deterministic) :=
  fun before frame => miss_at observe predicate external allocator physical model resources lookup items handle slice
    request key deterministic before frame (graphs.simplify before.world frame.2.2) graphs.publish graphs.insert

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ScopeProjection
