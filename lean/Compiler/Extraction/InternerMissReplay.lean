/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissAdmission

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- Decompose the existing scoped source control at its actual first decision.
This is the logical counterpart of `routed`, not another miss interpreter. -/
theorem scoped_routed (resources : Interner.Scoped.Resources) (model : Interner.Primitives)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (before : Interner.Scoped.Session) :
    let decision := if deterministic && request.item.kind == 1 then model.simplify key before.heap else (.ok none, before.heap)
    Interner.findCode.controlMiss (Interner.Scoped.execution resources model) request key deterministic before =
      match decision.1 with
      | .error fault => (.error fault, { before with heap := decision.2 })
      | .ok none => (do Interner.Scoped.handoff; Interner.Scoped.liftGraph (model.insert key deterministic))
          { before with heap := decision.2 }
      | .ok (some id) => (do let _ ← Interner.Scoped.liftGraph (model.publish key id); Interner.Scoped.handoff; pure id)
          { before with heap := decision.2 } := by
  simp only [Interner.FindCode.controlMiss, Interner.Scoped.execution]
  split
  · simp only [Interner.Scoped.liftGraph, bind, Effect.bind]
    cases ran : model.simplify key before.heap with
    | mk result after =>
      simp only [ran]
      cases result with
      | error fault => rfl
      | ok value => cases value <;> rfl
  · rfl

/-- Publication and dispatcher-error branches do not consult insertion. Their
existing scoped execution can therefore be reused with another insertion model. -/
theorem scoped_insert_irrelevant (resources : Interner.Scoped.Resources) (first second : Interner.Primitives)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (before : Interner.Scoped.Session)
    (simplify : first.simplify = second.simplify) (publish : first.publish = second.publish)
    (notInserted : (if deterministic && request.item.kind == 1 then first.simplify key before.heap
      else (.ok none, before.heap)).1 ≠ .ok none) :
    Interner.findCode.controlMiss (Interner.Scoped.execution resources first) request key deterministic before =
      Interner.findCode.controlMiss (Interner.Scoped.execution resources second) request key deterministic before := by
  rw [scoped_routed resources first, scoped_routed resources second]
  dsimp only
  rw [← simplify, ← publish]
  cases chosen : (if deterministic && request.item.kind == 1 then first.simplify key before.heap
      else (.ok none, before.heap)).1 with
  | error fault => rfl
  | ok value => cases value with
    | none => exact False.elim (notInserted chosen)
    | some id => rfl

/-- Lift an exact dispatcher result/graph projection through source control.
No suffix simulation is assumed: the result exposes the actual next scoped
operation, which the recorded native suffix will discharge. -/
theorem scoped_selected (resources : Interner.Scoped.Resources) (model : Interner.Primitives)
    (request : Interner.Request) (key : Key) (deterministic : Bool) (before : Interner.Scoped.Session)
    (native : Except Fault (Option NodeId)) (reached : Interner.Heap)
    (result : native = (if deterministic && request.item.kind == 1 then
      model.simplify key before.heap else (.ok none, before.heap)).1.mapError Fault.language)
    (projected : reached = (if deterministic && request.item.kind == 1 then
      model.simplify key before.heap else (.ok none, before.heap)).2) :
    let actual := Interner.findCode.controlMiss (Interner.Scoped.execution resources model) request key deterministic before
    (actual.1.mapError Fault.language, actual.2) =
      match (generalizing := false) native with
      | .error fault => (.error fault, { before with heap := reached })
      | .ok none =>
        let tail := (do Interner.Scoped.handoff; Interner.Scoped.liftGraph (model.insert key deterministic))
          { before with heap := reached }
        (tail.1.mapError Fault.language, tail.2)
      | .ok (some id) =>
        let tail := (do let _ ← Interner.Scoped.liftGraph (model.publish key id); Interner.Scoped.handoff; pure id)
          { before with heap := reached }
        (tail.1.mapError Fault.language, tail.2) := by
  dsimp only
  subst native
  subst reached
  rw [scoped_routed]
  cases decision : (if deterministic && request.item.kind == 1 then model.simplify key before.heap else (.ok none, before.heap)) with
  | mk outcome after =>
    cases outcome with
    | error fault => rfl
    | ok value => cases value <;> rfl

/-- Publication and insertion are replayed from their existing protocol, never
supplied as unconstrained graph callbacks. A branch without an insertion
candidate rejects an unexpected insertion attempt. -/
def replay (seed : Interner.Primitives) (events : List (Event Failure Insertion.Native.Fault))
    (candidate : Option Storage.Cell) (mismatch : Insertion.Native.Fault) : Interner.Primitives :=
  { seed with
    publish := Interner.InvocationTrace.publish events
    insert := fun key deterministic => match candidate with
      | some cell => Interner.InsertionExecution.action cell key deterministic (operations events mismatch)
      | none => fun before => (.error .safetyFault, before) }

theorem scoped_publish_return (action : Interner.Action Unit) (before : Interner.Scoped.Session) (id : NodeId) :
    (do let _ ← Interner.Scoped.liftGraph action; Interner.Scoped.handoff; pure id) before =
      (let tail := (do let _ ← Interner.Scoped.liftGraph action; Interner.Scoped.handoff : Interner.Scoped.Action Unit) before
       (tail.1.map (fun _ => id), tail.2)) := by
  simp only [bind, Effect.bind, Interner.Scoped.liftGraph, Interner.Scoped.handoff]
  cases action before.heap with
  | mk outcome after => cases outcome <;> rfl

/-- Protocol observations for the selected suffix. The body and deferred close
are separate so the miss result's cursor denotes the point before cleanup.
These are protocol events, not a count of physical host calls. -/
structure Segment where
  body : List (Event Failure Insertion.Native.Fault)
  cleanup : List (Event Failure Insertion.Native.Fault)
  candidate : Option Storage.Cell
  phase : NormalizationOwnership.Exit

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)

/-- Observe existing native insertion/publication/close executors at the actual
dispatcher result. The ordinary composition theorem below establishes admission;
the default rows and skipped semantic close confer no acceptance on their own. -/
def segment : Segment :=
  let p := physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input
  let decision := selected p request key slice deterministic before
  let reached := decision.2
  match decision.1 with
  | .ok none =>
    let cells := reached.graph.representatives.getD []
    let captured := Insertion.Native.recordExecution ops allocate safety base.allocator owner source address meaning input
      key slice deterministic cells reached growth []
    let candidate := Insertion.cell input key slice ((key.eval meaning reached.graph.read).getD 0) captured.1.2 captured.2.effects
    ⟨captured.2.events.map Event.insertion, [], some candidate, .transfer⟩
  | .ok (some id) =>
    let response := ops.probe key (Publication.forget reached.memory)
    let tail := (do let _ ← graph (fun owned => Publication.publish ops.probe ops.arguments base.allocator source key owned id); handoff
      : Action (Publication.Effects σ) Unit) ⟨reached, ⟨some handle, some slice, false⟩⟩
    let phase : NormalizationOwnership.Exit := if response.1 then .transfer else .cleanup
    let close := Caller.Close.capture (Publication.external ops.arguments) base.allocator lookup phase handle tail.2
    ⟨[.publicationProbe key response.1], close.2.events.map Event.normalization, none, phase⟩
  | .error fault =>
    let close := Caller.Close.capture (Publication.external ops.arguments) base.allocator lookup .cleanup handle
      ⟨reached, ⟨some handle, some slice, false⟩⟩
    ⟨[], if ordinary (.error fault : Except Fault NodeId) then close.2.events.map Event.normalization else [], none, .cleanup⟩

/-- The whole logical miss uses the real dispatcher and recorded suffix ports.
Its returned cursor precedes checked deferred cleanup in that same tagged stream. -/
def Projected (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault) : Prop :=
  let observed := segment ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before handle lookup
  let events := leading ++ observed.body ++ observed.cleanup ++ trailing
  let logicalModel := dispatchModel (replay seed events observed.candidate mismatch) model usizeBits debug
  let p := physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input
  let actual := Interner.findCode.controlMiss (execution (Publication.external ops.arguments) base.allocator p)
    request key deterministic ⟨before, ⟨some handle, some slice, false⟩⟩
  let logical := Interner.findCode.controlMiss (Interner.Scoped.execution (resources events (.preparation .incomplete)) logicalModel)
    request key deterministic ⟨⟨some lookup, handle.values, .cleanup⟩, cursorGraph cursor before⟩
  let close := Caller.Close.capture (Publication.external ops.arguments) base.allocator lookup observed.phase handle actual.2
  actual.1 = logical.1.mapError Fault.language ∧
    logical.2 = ⟨⟨some lookup, handle.values, observed.phase⟩,
      { actual.2.world.graph with allocationCursor := (leading ++ observed.body).length }⟩ ∧
    (ordinary actual.1 = true →
      Caller.Close.checked close (normalizations (leading ++ observed.body)) (normalizations trailing)
        lookup observed.phase handle.values logical.2.heap =
          .ok (Interner.Scoped.close (resources events (.preparation .incomplete)) logical.2))

attribute [local irreducible] Insertion.Native.recordExecution Publication.publish Caller.Close.capture

private theorem pair_eq {a b : α} {c d : β} (first : a = b) (second : c = d) :
    (a, c) = (b, d) := Prod.ext first second

/-- Compose the recorded suffix with an exact dispatcher projection. The local
native completions supply the actual replay ports; no insertion/publication
graph projection is supplied for arbitrary worlds. -/
theorem projected (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (values : List NodeId) (leading trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault)
    (complete : Completion ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup values leading trailing mismatch)
    (result : (selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).1 = (if deterministic && request.item.kind == 1 then
      (dispatchModel seed model usizeBits debug).simplify key (cursorGraph cursor before) else (.ok none, cursorGraph cursor before)).1.mapError Fault.language)
    (reached : { (selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).2.graph with allocationCursor := leading.length } =
      (if deterministic && request.item.kind == 1 then (dispatchModel seed model usizeBits debug).simplify key (cursorGraph cursor before)
        else (.ok none, cursorGraph cursor before)).2) :
    Projected ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup cursor model seed leading trailing mismatch := by
  unfold Projected
  intro observed events logicalModel p actual logical close
  have route := scoped_selected (resources events (.preparation .incomplete)) logicalModel request key deterministic
    ⟨⟨some lookup, handle.values, .cleanup⟩, cursorGraph cursor before⟩
    (selected p request key slice deterministic before).1
    { (selected p request key slice deterministic before).2.graph with allocationCursor := leading.length } result reached
  have native := routed (Publication.external ops.arguments) base.allocator p request key slice deterministic
    ⟨before, ⟨some handle, some slice, false⟩⟩ rfl
  dsimp only [p] at native route
  dsimp only [Completion] at complete
  cases chosen : (selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).1 with
  | ok value =>
    cases value with
    | none =>
      rw [chosen] at complete
      obtain ⟨cells, rows, inserted⟩ := complete
      dsimp only [Inserted] at inserted
      have pair := pair_eq inserted.result.symm inserted.reached
      have mapped := route.trans (by
        simpa only [chosen, logicalModel, dispatchModel, replay, events, observed, segment, rows,
          Option.getD_some, List.append_nil] using pair)
      have same := (congrArg Prod.snd mapped).trans inserted.reached.symm
      change logical.2 = _ at same
      refine ⟨(congrArg Prod.fst mapped).symm, ?_, ?_⟩
      · simpa only [observed, segment, chosen, rows, Option.getD_some] using congrArg Prod.snd mapped
      · intro ordinaryResult
        rw [chosen] at native
        have scope : actual.2.scope = ⟨some handle, some slice, true⟩ := by
          rw [show actual = _ from native]
          simp only [handoff, graph, bind, Effect.bind]
        have state : actual.2 = ⟨actual.2.world, ⟨some handle, some slice, true⟩⟩ := by rw [← scope]
        have closeEq := congrArg (Caller.Close.capture (Publication.external ops.arguments) base.allocator lookup .transfer handle) state
        simpa only [close, same, closeEq, observed, segment, chosen, rows, Option.getD_some, events, List.append_nil]
          using (inserted.closed ordinaryResult).1
    | some id =>
      rw [chosen] at complete
      dsimp only [Published] at complete
      have pair := pair_eq complete.2.1.symm complete.2.2.1
      have mapped := route.trans (by
        simpa only [chosen, logicalModel, dispatchModel, replay, events, observed, segment, scoped_publish_return] using pair)
      have same := (congrArg Prod.snd mapped).trans complete.2.2.1.symm
      change logical.2 = _ at same
      refine ⟨(congrArg Prod.fst mapped).symm, ?_, ?_⟩
      · simpa only [observed, segment, chosen] using congrArg Prod.snd mapped
      · intro _
        obtain ⟨after, finished, post, memory, checked⟩ := complete.2.2.2
        simpa only [close, same, actual, p, complete.1, observed, segment, chosen, events] using checked
  | error fault =>
    rw [chosen] at native
    have pair : (logical.1.mapError Fault.language, logical.2) =
        (actual.1, ⟨⟨some lookup, handle.values, observed.phase⟩,
          { actual.2.world.graph with allocationCursor := (leading ++ observed.body).length }⟩) := by
      simpa only [chosen, actual, p, native, observed, segment, List.append_nil] using route
    have same := congrArg Prod.snd pair
    change logical.2 = _ at same
    refine ⟨(congrArg Prod.fst pair).symm, same, ?_⟩
    intro ordinaryResult
    rw [chosen] at complete
    dsimp only [Failed] at complete
    obtain ⟨after, finished, post, memory, checked⟩ := complete.2.2 ordinaryResult
    have ordinaryFault : ordinary (.error fault : Except Fault NodeId) = true := by
      simpa only [actual, p, native] using ordinaryResult
    simpa only [close, same, actual, p, native, observed, segment, chosen,
      ordinaryFault, ↓reduceIte, events, List.append_nil] using checked

/-- The proper-child hypothesis now reaches the whole scoped miss through
recorded suffix ports. The dispatcher's ending cursor must still be bound to
the supplied leading event segment; initialization and child-event recording
are separate remaining obligations, not insertion/publication projections. -/
theorem scoped_from_children (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true →
      ∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    Completion ops allocate safety owner meaning base growth usizeBits children debug source address input
      request key slice deterministic before handle lookup values leading trailing mismatch ∧
    (ordinary (selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
        request key slice deterministic before).1 = true →
      cursor (selected (physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input)
        request key slice deterministic before).2 = leading.length →
      Projected ops allocate safety owner meaning base growth usizeBits children debug source address input
        request key slice deterministic before handle lookup cursor model seed leading trailing mismatch) := by
  have complete := from_children ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before cursor model seed predicate values originalRows initial frame aligned coupled
    handle lookup leading trailing mismatch detached unowned caller
  refine ⟨complete, fun completed boundary => ?_⟩
  have preserved := selected_preserved ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before cursor model seed predicate values originalRows initial frame aligned coupled completed
  apply projected ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before handle lookup cursor model seed values leading trailing mismatch complete preserved.2.1
  simpa only [cursorGraph, boundary] using preserved.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
