/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerNativeProtocol
import Compiler.Extraction.InternerCallerProtocolScope
import Compiler.Extraction.InternerMissReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Interner.InvocationTrace

/-- The existing source miss control, interpreted by the actual recorder. -/
def missBody (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (deterministic : Bool) : Action σ NodeId :=
  Interner.findCode.controlMiss (execution external budget allocator p q observations source buffer) request key deterministic

theorem missBody_erases (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (deterministic : Bool) :
    Effect.Transport Recorded.native (missBody external budget allocator p q observations source buffer request key deterministic)
      (Interner.findCode.controlMiss (OwnedCall.execution external allocator p) request key deterministic) := by
  unfold missBody Interner.FindCode.controlMiss
  simp only [execution, OwnedCall.execution]
  repeat first
    | exact record_erases _ _
    | exact Effect.Transport.pure Recorded.native _
    | apply Effect.Transport.bind Recorded.native
    | split
    | intro value

/-- An ordinary recorded miss cannot hide a rejected dispatcher result.
The recorder erases to the same source control, for any observation ports. -/
theorem missBody_selected_ordinary (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : Recorded σ) (handle : Handle)
    (locals : before.native.scope = ⟨some handle, some slice, false⟩)
    (completed : ordinary (missBody external budget allocator p q observations source buffer request key deterministic before).1 = true) :
    ordinary (MissStream.selected p request key slice deterministic before.native.world).1 = true := by
  have erased := missBody_erases external budget allocator p q observations source buffer request key deterministic before
  have nativeOrdinary := completed
  rw [← congrArg Prod.fst erased] at nativeOrdinary
  have route := MissStream.routed external allocator p request key slice deterministic before.native (congrArg Local.slice locals)
  cases chosen : (MissStream.selected p request key slice deterministic before.native.world).1 with
  | ok value => rfl
  | error fault => simpa only [route, chosen] using nativeOrdinary

/-- Earlier protocol history cannot affect source miss control or native
operations. Its complete ordinary or rejected return retains that history. -/
theorem missBody_prefix (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (leading : List ProtocolEvent) :
    Effect.Transport (prepend leading) (missBody external budget allocator p q observations source buffer request key deterministic)
      (missBody external budget allocator p q observations source buffer request key deterministic) := by
  unfold missBody Interner.FindCode.controlMiss
  simp only [execution]
  repeat first
    | exact record_prefix _ _ _
    | exact Effect.Transport.pure (prepend leading) _
    | apply Effect.Transport.bind (prepend leading)
    | split
    | intro value

theorem miss_finish_history (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (before : Recorded σ) :
    let body := missBody external budget allocator p q observations source buffer request key deterministic before
    ∃ suffix, (finish external allocator body.1 body.2).2.events = before.events ++ suffix := by
  let action := missBody external budget allocator p q observations source buffer request key deterministic
  let input := { before with events := [] }
  have prefixed := invoke_prefix external allocator action before.events
    (missBody_prefix external budget allocator p q observations source buffer request key deterministic before.events) input
  have same : prepend before.events input = before := by simp only [prepend, input, List.append_nil]
  rw [same] at prefixed
  exact ⟨(invoke external allocator action input).2.events, congrArg (fun ran => ran.2.events) prefixed⟩

/-- Route the recorded execution at the actual dispatcher result. The source
guard contributes no child events when skipped. Caller tokens survive the
dispatcher; insertion hands off before the call, publication after success. -/
theorem miss_routed (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : Recorded σ) (present : before.native.scope.slice = some slice) :
    let decision := MissStream.selected p request key slice deterministic before.native.world
    let middle := if deterministic && request.item.kind == 1 then observations.simplify key slice before.native.world else []
    let reached : Recorded σ := ⟨{ before.native with world := decision.2 }, before.tokens, before.events ++ middle⟩
    missBody external budget allocator p q observations source buffer request key deterministic before =
      match decision.1 with
      | .error fault => (.error fault, reached)
      | .ok none => (do
          record OwnedCall.handoff handingOff
          record (graph (fun owned => p.insert key owned deterministic))
            (graphObservation (fun owned => observations.insert key owned deterministic))) reached
      | .ok (some id) => (do
          let _ ← record (graph (fun owned => p.publish key owned id))
            (graphObservation (fun owned => observations.publish key owned id))
          record OwnedCall.handoff handingOff
          pure id) reached := by
  simp only [missBody, MissStream.selected, Interner.FindCode.controlMiss, execution]
  split
  · simp only [record, graph, graphObservation, present, bind, Effect.bind]
    cases ran : p.simplify key slice before.native.world with
    | mk result after =>
      simp only [ran]
      cases result with
      | error fault => rfl
      | ok value => cases value <;> simp only [Effect.bind, record, graph, graphObservation, present] <;> rfl
  · simp only [List.append_nil]
    rfl

/-- An unselected insertion observation cannot affect the actual caller. This
reuses source routing for both publication and dispatcher errors. -/
theorem miss_insert_irrelevant (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (first second : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : Recorded σ) (present : before.native.scope.slice = some slice)
    (simplify : first.simplify = second.simplify) (publish : first.publish = second.publish)
    (notInserted : (MissStream.selected p request key slice deterministic before.native.world).1 ≠ .ok none) :
    missBody external budget allocator p q first source buffer request key deterministic before =
      missBody external budget allocator p q second source buffer request key deterministic before := by
  rw [miss_routed external budget allocator p q first source buffer request key slice deterministic before present,
    miss_routed external budget allocator p q second source buffer request key slice deterministic before present]
  dsimp only
  rw [← simplify, ← publish]
  cases chosen : (MissStream.selected p request key slice deterministic before.native.world).1 with
  | error fault => rfl
  | ok value => cases value with
    | none => exact False.elim (notInserted chosen)
    | some id => rfl

/-- The selected insertion records the actual reached port, after source-order
handoff. This statement is independent of the graph observer and its replay. -/
theorem miss_insert_recorded (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (ports : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World σ) (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading : List ProtocolEvent)
    (chosen : (MissStream.selected p request key slice deterministic before).1 = .ok none) :
    let decision := MissStream.selected p request key slice deterministic before
    let middle := if deterministic && request.item.kind == 1 then ports.simplify key slice before else []
    let actual := p.insert key slice deterministic decision.2
    missBody external budget allocator p q ports source buffer request key deterministic
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩ =
      (actual.1, ⟨⟨actual.2, ⟨some handle, some slice, true⟩⟩,
        { lookup := some lookup, items := handle.values, phase := .transfer },
        leading ++ middle ++ ports.insert key slice deterministic decision.2⟩) := by
  have route := miss_routed external budget allocator p q ports source buffer request key slice deterministic
    ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩ rfl
  dsimp only at route
  rw [chosen] at route
  simpa only [record, OwnedCall.handoff, handingOff, graph, graphObservation, bind, Effect.bind, List.append_nil] using route

namespace Native

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)

def middle : List ProtocolEvent :=
  if deterministic && request.item.kind == 1 then
    (graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input).simplify key slice before
  else []

attribute [local irreducible] Insertion.Native.recordExecution Publication.publish Close.capture

/-- A reached valid frame justifies the recorder's native insertion header and
publication guard. Thus the actual source miss emits the existing replay
segment and retains exactly its phase, on every selected result. -/
theorem miss_recorded (values : List NodeId) (originalRows : List Storage.Cell) (leading : List ProtocolEvent)
    (aligned : key.arguments = slice.items)
    (preserved : ordinary (MissStream.selected (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
      request key slice deterministic before).1 = true →
      InputFrame safety base.allocator owner originalRows source values slice
        (MissStream.selected (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
          request key slice deterministic before).2) :
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let ports := graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup
    let native := Interner.findCode.controlMiss (OwnedCall.execution (Publication.external ops.arguments) base.allocator p)
      request key deterministic ⟨before, ⟨some handle, some slice, false⟩⟩
    missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request key deterministic
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩ =
        (native.1, ⟨native.2, { lookup := some lookup, items := handle.values, phase := observed.phase },
          leading ++ middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input request key slice deterministic before ++ observed.body⟩) ∧
      native.2.scope.lookup = some handle ∧ native.2.scope.slice = some slice ∧
      observed.phase = (if native.2.scope.handedOff then .transfer else .cleanup) := by
  intro p ports observed native
  have route := miss_routed (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
    request key slice deterministic
    ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩ rfl
  have nativeRoute := MissStream.routed (Publication.external ops.arguments) base.allocator p request key slice deterministic
    ⟨before, ⟨some handle, some slice, false⟩⟩ rfl
  dsimp only [p, physical] at route nativeRoute preserved
  rw [route]
  change native = _ at nativeRoute
  rw [nativeRoute]
  cases chosen : (MissStream.selected (MissStream.physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).1 with
  | error fault =>
    simp only [chosen, observed, MissStream.segment, List.append_nil]
    exact ⟨rfl, trivial, trivial, rfl⟩
  | ok value =>
    have ready := MissStream.tail_inputs (preserved (by simp only [chosen, ordinary])) aligned
    cases value with
    | none =>
      obtain ⟨cells, backing, header, rows⟩ := ready.2.2
      have emitted := insertion_events ops allocate safety owner meaning base growth usizeBits children observations debug source address input
        key slice deterministic (MissStream.selected p request key slice deterministic before).2 cells backing rows header
      dsimp only [p, physical] at emitted
      change ports.insert key slice deterministic _ = _ at emitted
      have captured := miss_insert_recorded (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
        request key slice deterministic before handle lookup leading chosen
      dsimp only [p, physical] at captured
      rw [route] at captured
      simp only [chosen] at captured ⊢
      rw [captured]
      simp only [chosen, observed, MissStream.segment, rows, Option.getD_some, bind, Effect.bind,
        OwnedCall.handoff, graph, emitted]
      exact ⟨rfl, trivial, trivial, rfl⟩
    | some id =>
      have admitted := Publication.admit_complete base.allocator source key slice _ ready.2.1
      have emitted := publication_events ops allocate safety owner meaning base growth usizeBits children observations debug source address input
        key slice id (MissStream.selected p request key slice deterministic before).2 admitted
      dsimp only [p, physical] at emitted
      change ports.publish key slice id _ = _ at emitted
      have published := Publication.publish_stream ops.probe ops.arguments base.allocator source key slice id
        (MissStream.selected p request key slice deterministic before).2 ([] : List ProtocolEvent) [] ready.1.1.1 ready.2.1 ready.1.2.1
      have resultEq : (p.publish key slice id (MissStream.selected p request key slice deterministic before).2).1 =
          (if (ops.probe key (Publication.forget (MissStream.selected p request key slice deterministic before).2.memory)).1
            then .ok () else .error (.language .outOfMemory)) := by
        simpa only [p, physical, MissStream.physical, context_publishes] using published.2.2
      dsimp only [p, physical] at resultEq
      simp only [chosen, observed, MissStream.segment, bind, Effect.bind, record, graph, graphObservation, emitted]
      simp only [resultEq]
      cases accepted : (ops.probe key (Publication.forget (MissStream.selected
        (MissStream.physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
          request key slice deterministic before).2.memory)).1 <;>
        simp only [Bool.false_eq_true, ↓reduceIte, OwnedCall.handoff, handingOff, pure, Effect.pure, List.append_nil] <;>
        exact ⟨rfl, trivial, trivial, trivial⟩

/-- The selected cleanup segment is the recorder at the body's reached state.
Transferred insertion closes a detached lookup without another event; an
ordinary error retains its real cleanup events. -/
theorem miss_cleanup_segment (detached : handle.owned = none) (unowned : lookup.owned = false)
    (caller : lookup.owner = .caller) :
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup
    let native := Interner.findCode.controlMiss (OwnedCall.execution (Publication.external ops.arguments) base.allocator p)
      request key deterministic ⟨before, ⟨some handle, some slice, false⟩⟩
    ordinary native.1 = true →
      (Close.capture (Publication.external ops.arguments) base.allocator lookup observed.phase handle native.2).2.events.map Event.normalization =
        observed.cleanup := by
  intro p observed native completed
  have route := MissStream.routed (Publication.external ops.arguments) base.allocator p request key slice deterministic
    ⟨before, ⟨some handle, some slice, false⟩⟩ rfl
  change native = _ at route
  dsimp only [p, physical] at route
  rw [route] at completed ⊢
  cases chosen : (MissStream.selected (MissStream.physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).1 with
  | error fault =>
    simp only [chosen] at completed
    simp only [observed, MissStream.segment, chosen, completed, ↓reduceIte]
  | ok value =>
    cases value with
    | none =>
      simp only [observed, MissStream.segment, chosen, bind, Effect.bind, handoff, graph]
      exact congrArg (List.map Event.normalization)
        (Close.transferred_stream (Publication.external ops.arguments) base.allocator lookup handle slice
          ((MissStream.physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input).insert
            key slice deterministic (MissStream.selected p request key slice deterministic before).2).2
          ([] : List ProtocolEvent) [] detached unowned caller).1
    | some id =>
      simp only [observed, MissStream.segment, chosen, MissStream.physical, context_publishes,
        bind, Effect.bind, graph, handoff, pure, Effect.pure]
      cases Publication.publish ops.probe ops.arguments base.allocator source key slice id
        (MissStream.selected p request key slice deterministic before).2 with
      | mk result world => cases result <;> rfl

end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
