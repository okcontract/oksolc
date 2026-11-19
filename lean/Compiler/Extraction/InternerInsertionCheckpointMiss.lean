/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionCheckpoint
import Compiler.Extraction.InternerCallerProtocolMissReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Caller.ProtocolTrace (ProtocolEvent)

/-- Fixed-stream graph ports for caller composition. The insertion candidate
comes from the source inputs and reached checkpoint, never a completed call. -/
def graphReplay (seed : Interner.Primitives) (input : AssemblyClone.NativeFields.ItemValue)
    (normalized : ArgumentSlice) (meaning : Meaning) (stream : List ProtocolEvent)
    (mismatch : Insertion.Native.Fault) : Interner.Primitives :=
  { seed with
    publish := Interner.InvocationTrace.publish stream
    insert := fun key deterministic => insertionReplay input normalized meaning key deterministic stream mismatch }

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

attribute [local irreducible] Insertion.Native.insert Close.capture

/-- The source-selected insertion and its actual recorded close consume one
checkpoint model. The reached frame and dispatcher projection remain the
proper-child obligations; no candidate, final graph or cleanup is assumed. -/
theorem checkpoint_insert_miss
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (source buffer : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (values : List NodeId) (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (leading stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let ports := AllocationTrace.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let decision := MissStream.selected p request key slice deterministic before
    let middle := if deterministic && request.item.kind == 1 then ports.simplify key slice before else []
    let closeLeading := leading ++ middle ++ ports.insert key slice deterministic decision.2
    let logicalModel := dispatchModel (AllocationTrace.graphReplay seed input slice meaning stream mismatch) model usizeBits debug
    let initialRecord : Recorded (Publication.Effects σ) :=
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩
    let logicalDecision := if deterministic && request.item.kind == 1 then logicalModel.simplify key (scopeView initialRecord).heap
      else (.ok none, (scopeView initialRecord).heap)
    let resources := Interner.InvocationTrace.resources stream (.preparation .incomplete)
    let body := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
      request key deterministic initialRecord
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources logicalModel)
      request key deterministic (scopeView initialRecord)
    ∀ (_chosen : decision.1 = .ok none)
      (_frame : CallFrame safety base.allocator owner rows source values slice address input parent decision.2)
      (_inside : closeLeading <+: stream)
      (_selected : decision.1 = logicalDecision.1.mapError Fault.language)
      (_reached : { decision.2.graph with allocationCursor := (leading ++ middle).length } = logicalDecision.2)
      (_completed : ordinary body.1 = true),
      let actual := finish (Publication.external ops.arguments) base.allocator body.1 body.2
      (body.1, scopeView body.2) = (logical.1.mapError Fault.language, logical.2) ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, Interner.Scoped.close resources logical.2) ∧
      actual.2.events = closeLeading ∧ actual.2.tokens.incomplete = false := by
  intro p ports decision middle closeLeading logicalModel initialRecord logicalDecision resources body logical
    chosen frame inside selected reached completed actual
  let inserted := Insertion.Native.insert ops allocate safety base.allocator owner source address meaning input key slice deterministic growth decision.2
  have recorded := miss_insert_recorded (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
    request key slice deterministic before handle lookup leading chosen
  change body = (inserted.1, ⟨⟨inserted.2, ⟨some handle, some slice, true⟩⟩,
    { lookup := some lookup, items := handle.values, phase := .transfer }, closeLeading⟩) at recorded
  have ordinaryInsert : ordinary inserted.1 = true := by simpa only [recorded] using completed
  have replayed := CallFrame.insertion_checkpoint_stream ops allocate base growth usizeBits children observations debug frame
    meaning key deterministic mismatch (leading ++ middle) stream admitted inside ordinaryInsert
  let port := AllocationTrace.insertionReplay input slice meaning key deterministic stream mismatch
    { decision.2.graph with allocationCursor := (leading ++ middle).length }
  change (inserted.1, { inserted.2.graph with allocationCursor := (leading ++ middle).length +
      (ports.insert key slice deterministic decision.2).length }) = (port.1.mapError Fault.language, port.2) at replayed
  have route := MissStream.scoped_selected resources logicalModel request key deterministic (scopeView initialRecord)
    decision.1 { decision.2.graph with allocationCursor := (leading ++ middle).length } selected reached
  rw [chosen] at route
  have logicalResult : logical.1.mapError Fault.language = inserted.1 := by
    exact (congrArg Prod.fst route).trans (congrArg Prod.fst replayed).symm
  have logicalState : logical.2 = ⟨⟨some lookup, handle.values, .transfer⟩,
      { inserted.2.graph with allocationCursor := closeLeading.length }⟩ := by
    have state : logical.2 = ⟨⟨some lookup, handle.values, .transfer⟩, port.2⟩ := congrArg Prod.snd route
    rw [← congrArg Prod.snd replayed] at state
    simpa only [closeLeading, List.length_append] using state
  have bodyView : scopeView body.2 = logical.2 := by
    rw [recorded, logicalState]; rfl
  obtain ⟨trailing, streamEq⟩ := inside
  have closed := Close.transferred_stream (Publication.external ops.arguments) base.allocator lookup handle slice
    inserted.2 closeLeading trailing detached unowned caller
  have checked : Close.checked
      (Close.capture (Publication.external ops.arguments) base.allocator lookup .transfer handle
        ⟨inserted.2, ⟨some handle, some slice, true⟩⟩)
      (normalizations closeLeading) (normalizations trailing) lookup .transfer handle.values
      { inserted.2.graph with allocationCursor := closeLeading.length } =
        .ok (Interner.Scoped.close resources logical.2) := by
    simpa only [resources, ← streamEq, logicalState] using closed.2.2.2.1
  have finished := finish_projected (Publication.external ops.arguments) base.allocator inserted.1 inserted.2 handle slice true
    lookup closeLeading trailing detached unowned caller ordinaryInsert (Interner.Scoped.close resources logical.2) checked
  have actualEq : actual = finish (Publication.external ops.arguments) base.allocator inserted.1
      ⟨⟨inserted.2, ⟨some handle, some slice, true⟩⟩,
        { lookup := some lookup, items := handle.values, phase := .transfer }, closeLeading⟩ := by
    simp only [actual, recorded]
  refine ⟨Prod.ext ((congrArg Prod.fst recorded).trans logicalResult.symm) bodyView, ?_, ?_, ?_⟩
  · rw [actualEq]
    exact finished.1.trans (congrArg (fun result => (result, Interner.Scoped.close resources logical.2)) logicalResult.symm)
  · rw [actualEq]
    simpa only [↓reduceIte, closed.1, List.map_nil, List.append_nil] using finished.2.1
  · rw [actualEq]
    exact finished.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
