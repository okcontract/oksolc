/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionInvocation
import Compiler.Extraction.InternerPublicationInvocation
import Compiler.Extraction.InternerCallerRecursionEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Interner.InvocationTrace

/-- Observe the actual first miss decision. A skipped dispatcher makes no call
and leaves the world unchanged. `routed` binds this observation to the existing
source control; it is not a replacement caller interpreter. -/
def selected (physical : Primitives σ) (request : Interner.Request) (key : Key)
    (slice : ArgumentSlice) (deterministic : Bool) (before : World σ) :=
  if deterministic && request.item.kind == 1 then physical.simplify key slice before else (.ok none, before)

/-- All source branches retain the exact reached dispatcher world. An error
does not run either tail; publication hands off after success, insertion before
the call. No supplied branch choice or unchanged-graph premise is needed. -/
theorem routed (external : External σ) (allocator : Nat) (physical : Primitives σ)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : State σ) (present : before.scope.slice = some slice) :
    let decision := selected physical request key slice deterministic before.world
    Interner.findCode.controlMiss (execution external allocator physical) request key deterministic before =
      match decision.1 with
      | .error fault => (.error fault, { before with world := decision.2 })
      | .ok none => (do handoff; graph (fun owned => physical.insert key owned deterministic))
          { before with world := decision.2 }
      | .ok (some id) => (do let _ ← graph (fun owned => physical.publish key owned id); handoff; pure id)
          { before with world := decision.2 } := by
  simp only [selected, Interner.FindCode.controlMiss, execution]
  split
  · simp only [graph, present, bind, Effect.bind]
    cases ran : physical.simplify key slice before.world with
    | mk result after =>
      simp only [ran]
      cases result with
      | error fault => rfl
      | ok value => cases value <;> simp only [Effect.bind, graph, present] <;> rfl
  · rfl

theorem finish_map (external : External σ) (allocator : Nat) (result : Except Fault α)
    (before : State σ) (f : α → β) :
    finish external allocator (result.map f) before =
      (let ran := finish external allocator result before; (ran.1.map f, ran.2)) := by
  cases result <;> simp only [Except.map, finish, ordinary]
  all_goals split <;> try rfl
  all_goals cases cleanup external allocator before with
  | mk outcome after => cases outcome <;> rfl

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (container : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (owner usizeBits : Nat)
    (children : ConstructorItem.NativeRecursion.Constructors (Publication.Effects σ))
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)

/-- Use the already bound production ports and the actual shared native
dispatcher, including its proper children. -/
abbrev physical :=
  ((ConstructorItem.NativeRecursion.context
    (ConstructorItem.NativeRecursion.callerContext ops allocate safety container meaning base growth)
    owner usizeBits children debug).primitives source address input)

attribute [local irreducible] Insertion.Native.insert Insertion.Native.recordExecution
  Publication.publish Caller.Close.capture

/-- Exact selected insertion suffix, shared by local and proper-child composition. -/
def Inserted (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (cells : List Storage.Cell)
    (mismatch : Insertion.Native.Fault) : Prop :=
    let p := physical ops allocate safety container meaning base growth owner usizeBits children debug source address input
    let reached := (selected p request key slice deterministic before).2
    let captured := Insertion.Native.recordExecution ops allocate safety base.allocator container source address meaning input
      key slice deterministic cells reached growth []
    let candidate := Insertion.cell input key slice ((key.eval meaning reached.graph.read).getD 0) captured.1.2 captured.2.effects
    let closeLeading := leading ++ captured.2.events.map Event.insertion
    let events := closeLeading ++ trailing
    let action := Interner.InsertionExecution.action candidate key deterministic (operations events mismatch)
    let logical := (do Interner.Scoped.handoff; Interner.Scoped.liftGraph action)
      ⟨⟨some lookup, handle.values, .cleanup⟩, { reached.graph with allocationCursor := leading.length }⟩
    let actual := Interner.findCode.controlMiss (execution (Publication.external ops.arguments) base.allocator p)
      request key deterministic ⟨before, ⟨some handle, some slice, false⟩⟩
    Caller.Close.HandoffCompletion (Publication.external ops.arguments) base.allocator lookup handle slice
      closeLeading trailing (actual.1, actual.2.world) logical
      (finish (Publication.external ops.arguments) base.allocator actual.1 actual.2)

/-- A source-selected insertion consumes the earlier stream proof at the
dispatcher's reached world. Header/rows describe that world, not caller entry.
This includes the guard-skipped and simplify-returned-none paths. -/
theorem inserted (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (cells : List Storage.Cell)
    (backing : Compiler.ZigAir.Memory.Address) (mismatch : Insertion.Native.Fault)
    (chosen : (selected (physical ops allocate safety container meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).1 = .ok none)
    (header : readItems (selected (physical ops allocate safety container meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).2.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : (selected (physical ops allocate safety container meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).2.graph.representatives = some cells)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    Inserted ops allocate safety container meaning base growth owner usizeBits children debug source address input
      request key slice deterministic before handle lookup leading trailing cells mismatch := by
  unfold Inserted
  intro p reached captured candidate closeLeading events action logical actual
  have route := routed (Publication.external ops.arguments) base.allocator p request key slice deterministic
    ⟨before, ⟨some handle, some slice, false⟩⟩ rfl
  dsimp only [p] at route
  rw [chosen] at route
  have inserted := Insertion.Native.finished_insert_stream ops allocate safety base.allocator container source address meaning input
    key slice deterministic cells reached growth mismatch leading trailing backing header rows
    ⟨some lookup, handle.values, .cleanup⟩ handle lookup rfl rfl detached unowned caller
  simpa only [actual, route, physical, p, ConstructorItem.NativeRecursion.context_inserts,
    execution, handoff, graph, bind, Effect.bind, Insertion.Native.finishInsertion] using inserted

/-- Exact selected publication suffix, shared by local and proper-child composition. -/
def Published (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (values : List NodeId) (id : NodeId) (leading trailing : List (Event Failure ι)) : Prop :=
    let p := physical ops allocate safety container meaning base growth owner usizeBits children debug source address input
    let reached := (selected p request key slice deterministic before).2
    let response := ops.probe key (Publication.forget reached.memory)
    let tail := (do let _ ← graph (fun owned => Publication.publish ops.probe ops.arguments base.allocator source key owned id); handoff
      : Action (Publication.Effects σ) Unit) ⟨reached, ⟨some handle, some slice, false⟩⟩
    let phase : NormalizationOwnership.Exit := if response.1 then .transfer else .cleanup
    let close := Caller.Close.capture (Publication.external ops.arguments) base.allocator lookup phase handle tail.2
    let closeLeading := leading ++ [.publicationProbe key response.1]
    let events := closeLeading ++ close.2.events.map Event.normalization ++ trailing
    let logical := (do let _ ← Interner.Scoped.liftGraph (Interner.InvocationTrace.publish events key id); Interner.Scoped.handoff)
      ⟨⟨some lookup, handle.values, .cleanup⟩, { reached.graph with allocationCursor := leading.length }⟩
    let actual := Interner.findCode.controlMiss (execution (Publication.external ops.arguments) base.allocator p)
      request key deterministic ⟨before, ⟨some handle, some slice, false⟩⟩
    actual = (tail.1.map (fun _ => id), tail.2) ∧
      actual.1 = (logical.1.map (fun _ => id)).mapError Fault.language ∧
      logical.2 = ⟨⟨some lookup, handle.values, phase⟩, { actual.2.world.graph with allocationCursor := closeLeading.length }⟩ ∧
      ∃ after, finish (Publication.external ops.arguments) base.allocator actual.1 actual.2 = (actual.1, after) ∧
        CleanupPost (Publication.external ops.arguments) base.allocator source values slice actual.2 after ∧
        after.world.memory = close.2.effects.session ∧
        Caller.Close.checked close (normalizations closeLeading) (normalizations trailing) lookup phase handle.values logical.2.heap =
          .ok (Interner.Scoped.close (resources events (.preparation .incomplete)) logical.2)

/-- Publication receives the ID and world returned by the actual dispatcher.
Its existing probe/handoff/close proof supplies the full selected suffix;
the final ID return changes neither ownership nor the reached graph. -/
theorem published (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (values : List NodeId) (id : NodeId) (leading trailing : List (Event Failure ι))
    (chosen : (selected (physical ops allocate safety container meaning base growth owner usizeBits children debug source address input)
      request key slice deterministic before).1 = .ok (some id))
    (held : Held base.allocator source values slice
      (selected (physical ops allocate safety container meaning base growth owner usizeBits children debug source address input)
        request key slice deterministic before).2)
    (admitted : Publication.Input base.allocator source key slice
      (selected (physical ops allocate safety container meaning base growth owner usizeBits children debug source address input)
        request key slice deterministic before).2)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    Published ops allocate safety container meaning base growth owner usizeBits children debug source address input
      request key slice deterministic before handle lookup values id leading trailing := by
  unfold Published
  intro p reached response tail phase close closeLeading events logical actual
  have route := routed (Publication.external ops.arguments) base.allocator p request key slice deterministic
    ⟨before, ⟨some handle, some slice, false⟩⟩ rfl
  dsimp only [p] at route
  rw [chosen, physical, ConstructorItem.NativeRecursion.context_publishes] at route
  have native : actual = (tail.1.map (fun _ => id), tail.2) := by
    rw [show actual = _ from route]
    simp only [tail, graph, bind, Effect.bind, handoff]
    cases Publication.publish ops.probe ops.arguments base.allocator source key slice id reached with
    | mk result world => cases result <;> rfl
  have closed := Publication.closed_publish_stream ops.probe ops.arguments base.allocator source values key slice id reached
    handle lookup leading trailing held admitted detached unowned caller
  have result : tail.1 = logical.1.mapError Fault.language := closed.2.2.1
  obtain ⟨after, finished, post, memory, checked⟩ := closed.2.2.2.2
  refine ⟨native, ?_, ?_, after, ?_, ?_, memory, checked⟩
  · rw [native, result]
    cases logical.1 <;> rfl
  · simpa only [native] using closed.2.2.2.1
  · rw [native, finish_map, finished]
  · simpa only [native] using post

/-- Exact selected error suffix, shared by local and proper-child composition. -/
def Failed (external : External σ) (allocator : Nat) (p : Primitives σ)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World σ) (handle : Handle) (lookup : NormalizationOwnership.State)
    (source : View) (values : List NodeId) (fault : Fault) (leading trailing : List (Event Failure ι)) : Prop :=
    let reached := (selected p request key slice deterministic before).2
    let actual := Interner.findCode.controlMiss (execution external allocator p) request key deterministic
      ⟨before, ⟨some handle, some slice, false⟩⟩
    let close := Caller.Close.capture external allocator lookup .cleanup handle actual.2
    let events := leading ++ close.2.events.map Event.normalization ++ trailing
    let logical : Interner.Scoped.Session := ⟨⟨some lookup, handle.values, .cleanup⟩,
      { reached.graph with allocationCursor := leading.length }⟩
    actual = (.error fault, ⟨reached, ⟨some handle, some slice, false⟩⟩) ∧
      (ordinary actual.1 = false → finish external allocator actual.1 actual.2 = actual) ∧
      (ordinary actual.1 = true → ∃ after, finish external allocator actual.1 actual.2 = (actual.1, after) ∧
        CleanupPost external allocator source values slice actual.2 after ∧
        after.world.memory = close.2.effects.session ∧
        Caller.Close.checked close (normalizations leading) (normalizations trailing) lookup .cleanup handle.values logical.heap =
          .ok (Interner.Scoped.close (resources events (.preparation .incomplete)) logical))

/-- A dispatcher error does not publish, insert or hand off. Ordinary errors
use the retained incoming ownership to derive cleanup; semantic rejection
retains the exact native locals without an accepted-close claim. -/
theorem failed (external : External σ) (allocator : Nat) (p : Primitives σ)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World σ) (handle : Handle) (lookup : NormalizationOwnership.State)
    (source : View) (values : List NodeId) (fault : Fault) (leading trailing : List (Event Failure ι))
    (chosen : (selected p request key slice deterministic before).1 = .error fault)
    (held : ordinary (.error fault : Except Fault NodeId) = true →
      Held allocator source values slice (selected p request key slice deterministic before).2)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    Failed external allocator p request key slice deterministic before handle lookup source values fault leading trailing := by
  unfold Failed
  intro reached actual close events logical
  have route := routed external allocator p request key slice deterministic ⟨before, ⟨some handle, some slice, false⟩⟩ rfl
  dsimp only at route
  rw [chosen] at route
  have native : actual = (.error fault, ⟨reached, ⟨some handle, some slice, false⟩⟩) := route
  refine ⟨native, fun rejected => by simp only [finish, rejected, Bool.false_eq_true, ↓reduceIte], ?_⟩
  intro ordinaryResult
  have retained := held (by simpa only [native] using ordinaryResult)
  have post : Post allocator source values slice handle actual := by
    rw [native]
    exact ⟨rfl, rfl, fun _ => ⟨retained.1, fun _ => retained.2.1⟩⟩
  have completed := Caller.Close.of_post external allocator source values lookup handle slice actual
    detached unowned caller post retained.2.2 ordinaryResult (normalizations leading) (normalizations trailing)
  have checked := Caller.ScopeProjection.close_completion external allocator source values lookup handle slice actual
    (fun _ => leading.length) (normalizations leading) (normalizations trailing) logical completed
    (by simp only [logical, Caller.ScopeProjection.scopeAt, Recursive.cursorGraph, native]; rfl)
    (by simp only [normalizations_length])
  simpa only [close, native, logical, events, resources, normalizations_append, normalizations_embed, List.append_assoc] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
