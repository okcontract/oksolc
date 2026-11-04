/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Interner.InvocationTrace ResourceAdapter

attribute [local irreducible] Close.capture

/-- Checked physical close, already derived by the miss proof, determines the
actual recorded finish. This adapter supplies no lifetime or success premise
for cleanup and preserves the caller's original ordinary result. -/
theorem finish_projected (external : External σ) (allocator : Nat) (result : Except Fault α)
    (before : World σ) (handle : Handle) (slice : ArgumentSlice) (handedOff : Bool)
    (lookup : NormalizationOwnership.State) (leading trailing : List ProtocolEvent)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (owner : lookup.owner = .caller)
    (completed : ordinary result = true) :
    let phase : NormalizationOwnership.Exit := if handedOff then .transfer else .cleanup
    let native : OwnedCall.State σ := ⟨before, ⟨some handle, some slice, handedOff⟩⟩
    let captured := Close.capture external allocator lookup phase handle native
    let input : Recorded σ := ⟨native, { lookup := some lookup, items := handle.values, phase }, leading⟩
    ∀ projected : Interner.Scoped.Session,
      Close.checked captured (normalizations leading) (normalizations trailing) lookup phase handle.values
        (scopeView input).heap = .ok projected →
      let actual := finish external allocator result input
      (actual.1, scopeView actual.2) = (result, projected) ∧
        actual.2.events = leading ++ captured.2.events.map Event.normalization ∧ actual.2.tokens.incomplete = false := by
  intro phase native captured input projected accepted actual
  have clean := (TraceBridge.check_physical_sound _ _ _ accepted).1
  change captured.2.effects.rejected = none at clean
  let after : OwnedCall.State σ := ⟨{ before with memory := captured.2.effects.session },
    ⟨none, if handedOff then some slice else none, handedOff⟩⟩
  have spec := Close.taken_spec external allocator lookup handle slice handedOff before detached unowned owner
  change Close.observe native captured.2.effects = some (cleanup external allocator native) at spec
  have closed : cleanup external allocator native = (.ok (), after) := by
    simpa only [Close.observe, clean, native, after, Option.some.injEq] using spec.symm
  have linked := close_from_cleanup external allocator native after handle lookup handle.values leading trailing rfl
    spec closed rfl
  have same := Except.ok.inj (linked.2.2.1.symm.trans accepted)
  have view : scopeView (record (cleanup external allocator) (closing external allocator) input).2 = projected :=
    linked.2.2.2.1.trans same
  have nativeResult : (record (cleanup external allocator) (closing external allocator) input).1 = .ok () := congrArg Prod.fst closed
  simp only [actual, finish, completed, ↓reduceIte, nativeResult]
  refine ⟨Prod.ext rfl view, ?_, ?_⟩
  · rfl
  · exact linked.2.2.2.2

namespace Native
open Recursive

/-- Exact ordinary body/finish correspondence and the actual recorded protocol
stream. Kept as one endpoint so conditional and history-derived consumers share
the same result, scope and cleanup claim. -/
def MissProjected (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault) : Prop :=
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let ports := graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let middle := Native.middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input
      request key slice deterministic before
    let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup
    let events := leading ++ middle ++ observed.body ++ observed.cleanup ++ trailing
    let resources := Interner.InvocationTrace.resources events (.preparation .incomplete)
    let logicalModel := dispatchModel (MissStream.replay seed events observed.candidate mismatch) model usizeBits debug
    let initialRecord : Recorded (Publication.Effects σ) :=
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩
    let body := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
      request key deterministic initialRecord
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources logicalModel)
      request key deterministic (scopeView initialRecord)
    ordinary body.1 = true →
      let actual := finish (Publication.external ops.arguments) base.allocator body.1 body.2
      (body.1, scopeView body.2) = (logical.1.mapError Fault.language, logical.2) ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, Interner.Scoped.close resources logical.2) ∧
      actual.2.events = leading ++ middle ++ observed.body ++ observed.cleanup ∧ actual.2.tokens.incomplete = false

/-- Record the actual native miss and close from its reached frame and scoped
projection. Both child relations share this exact body/result/history proof;
no cleanup success or final recorded body is assumed. -/
theorem miss_from_projection (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (values : List NodeId) (originalRows : List Storage.Cell)
    (aligned : key.arguments = slice.items)
    (preserved : ordinary (MissStream.selected
      (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
      request key slice deterministic before).1 = true →
      InputFrame safety base.allocator owner originalRows source values slice
        (MissStream.selected (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
          request key slice deterministic before).2)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller)
    (start : cursor before = leading.length)
    (projection : ordinary (MissStream.selected
      (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
      request key slice deterministic before).1 = true →
      MissStream.Projected ops allocate safety owner meaning base growth usizeBits children debug source address input
        request key slice deterministic before handle lookup cursor model seed
        (leading ++ middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input
          request key slice deterministic before) trailing mismatch) :
    MissProjected ops allocate safety owner meaning base growth usizeBits children observations debug source buffer address input
      request key slice deterministic before handle lookup model seed leading trailing mismatch := by
  unfold MissProjected
  intro p ports middle observed events resources logicalModel initialRecord body logical completed actual
  have recorded := miss_recorded ops allocate safety owner meaning base growth usizeBits children observations debug source buffer address input
    request key slice deterministic before handle lookup values originalRows leading aligned preserved
  let native := Interner.findCode.controlMiss (OwnedCall.execution (Publication.external ops.arguments) base.allocator p)
    request key deterministic ⟨before, ⟨some handle, some slice, false⟩⟩
  change body = (native.1, ⟨native.2, { lookup := some lookup, items := handle.values, phase := observed.phase },
    leading ++ middle ++ observed.body⟩) ∧ native.2.scope.lookup = some handle ∧ native.2.scope.slice = some slice ∧
    observed.phase = (if native.2.scope.handedOff then .transfer else .cleanup) at recorded
  have nativeOrdinary : ordinary native.1 = true := by simpa only [recorded.1] using completed
  have selectedOrdinary := missBody_selected_ordinary (Publication.external ops.arguments) base.budget base.allocator p
    base.queries ports source buffer request key slice deterministic initialRecord handle rfl completed
  have projected := projection selectedOrdinary
  dsimp only [MissStream.Projected, cursorGraph] at projected
  rw [start] at projected
  change native.1 = logical.1.mapError Fault.language ∧
    logical.2 = ⟨⟨some lookup, handle.values, observed.phase⟩,
      { native.2.world.graph with allocationCursor := (leading ++ middle ++ observed.body).length }⟩ ∧
    (ordinary native.1 = true → Close.checked
      (Close.capture (Publication.external ops.arguments) base.allocator lookup observed.phase handle native.2)
      (normalizations (leading ++ middle ++ observed.body)) (normalizations trailing)
      lookup observed.phase handle.values logical.2.heap = .ok (Interner.Scoped.close resources logical.2)) at projected
  have shape : native.2 = ⟨native.2.world, ⟨some handle, some slice, native.2.scope.handedOff⟩⟩ := by
    have rebuild : ∀ state : OwnedCall.State (Publication.Effects σ), state.scope.lookup = some handle →
        state.scope.slice = some slice → state = ⟨state.world, ⟨some handle, some slice, state.scope.handedOff⟩⟩ := by
      rintro ⟨world, lookup, slice, flag⟩ rfl rfl
      rfl
    exact rebuild native.2 recorded.2.1 recorded.2.2.1
  have bodyView : scopeView body.2 = logical.2 := by
    rw [recorded.1]
    exact projected.2.1.symm
  have closed := finish_projected (Publication.external ops.arguments) base.allocator native.1 native.2.world handle slice
    native.2.scope.handedOff lookup (leading ++ middle ++ observed.body) trailing detached unowned caller nativeOrdinary
    (Interner.Scoped.close resources logical.2)
  have closeChecked := projected.2.2 nativeOrdinary
  conv at closeChecked => lhs; rw [projected.2.1, shape, recorded.2.2.2]
  have finished := closed closeChecked
  have cleanupEvents := miss_cleanup_segment ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before handle lookup detached unowned caller nativeOrdinary
  rw [← shape, ← recorded.2.2.2] at finished
  change let finished := (finish (Publication.external ops.arguments) base.allocator native.1
      ⟨native.2, { lookup := some lookup, items := handle.values, phase := observed.phase }, leading ++ middle ++ observed.body⟩)
    (finished.1, scopeView finished.2) = (native.1, Interner.Scoped.close resources logical.2) ∧
      finished.2.events = (leading ++ middle ++ observed.body) ++
        (Close.capture (Publication.external ops.arguments) base.allocator lookup observed.phase handle native.2).2.events.map Event.normalization ∧
      finished.2.tokens.incomplete = false at finished
  have bodyResult := congrArg Prod.fst recorded.1
  have bodyState := congrArg Prod.snd recorded.1
  dsimp only at bodyResult bodyState
  rw [← bodyResult, ← bodyState] at finished
  refine ⟨Prod.ext ((congrArg Prod.fst recorded.1).trans projected.1) bodyView, ?_, ?_, finished.2.2⟩
  · exact finished.1.trans (congrArg (fun result => (result, Interner.Scoped.close resources logical.2))
      ((congrArg Prod.fst recorded.1).trans projected.1))
  · exact finished.2.1.trans (congrArg (fun tail => (leading ++ middle ++ observed.body) ++ tail) cleanupEvents)

/-- The recorded native miss, including its ordinary deferred close, implements
the scoped miss under proper-child preservation. The reached header, publication
admission, phase and cleanup are derived. The two child-stream cursor boundaries
remain explicit; this theorem does not certify arbitrary child observations. -/
theorem miss_verified (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true →
      ∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller)
    (start : cursor before = leading.length) :
    cursor (MissStream.selected (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
      request key slice deterministic before).2 =
        (leading ++ middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input
          request key slice deterministic before).length →
    MissProjected ops allocate safety owner meaning base growth usizeBits children observations debug source buffer address input
      request key slice deterministic before handle lookup model seed leading trailing mismatch := by
  intro boundary
  have preserved := MissStream.selected_preserved ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before cursor model seed predicate values originalRows initial frame aligned coupled
  refine miss_from_projection ops allocate safety owner meaning base growth usizeBits children observations
    debug source buffer address input request key slice deterministic before handle lookup cursor model seed values originalRows
    aligned (fun completed => (preserved completed).1.2) leading trailing mismatch detached unowned caller start ?_
  intro completed
  exact (MissStream.scoped_from_children ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before handle lookup cursor model seed predicate values originalRows initial frame aligned coupled
    (leading ++ middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input
      request key slice deterministic before) trailing mismatch detached unowned caller).2 completed boundary

end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
