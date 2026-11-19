/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointSourceReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

/-- Proper native bodies supply the selected dispatcher's result and live
call frame. The actual captured history supplies admission and both relative
cursor boundaries, including an ordinary failing child. The caller may append
its checkpoint-aware insertion/publication and cleanup suffix to that history. -/
theorem selected_from_bodies (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (request : Interner.Request) (key : Key) (slice : ArgumentSlice)
    (deterministic : Bool) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (models : Models) (seed : Interner.Primitives) (values : List NodeId) (originalRows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (frame : CallFrame safety outerBase.allocator owner originalRows source values slice address input parent (ChildTrace.erase before))
    (aligned : key.arguments = slice.items) (leading suffix : List ProtocolEvent) :
    let traced := children ops allocate safety owner meaning base growth usizeBits (depth + 1)
    let action := MissStream.selected
      (MissStream.physical outerOps outerAllocate safety owner meaning outerBase outerGrowth owner usizeBits traced debug source address input)
      request key slice deterministic
    let decision := action before
    let middle := Caller.ProtocolTrace.Native.middle outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      traced (ChildTrace.liftObservations (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1))))
      debug source address input request key slice deterministic before
    let stream := ChildTrace.history decision.2 ++ suffix
    let model := replay leading stream before models
    let logical := if deterministic && request.item.kind == 1 then
      (dispatchModel seed model usizeBits debug).simplify key { before.graph with allocationCursor := leading.length }
      else (.ok none, { before.graph with allocationCursor := leading.length })
    ((deterministic && (request.item.kind == 1)) = true → ∀ rows,
      BodiesAt leading stream before
        (fun world => CallFrame safety outerBase.allocator owner originalRows source values slice address input parent world ∧
          InputFrame safety outerBase.allocator owner rows source values slice world)
        (Nested.storageReads rows) debug (body ops allocate safety owner meaning base growth usizeBits depth) models) →
    ChildTrace.history decision.2 = ChildTrace.history before ++ middle ∧
      (ordinary decision.1 = true →
        CallFrame safety outerBase.allocator owner originalRows source values slice address input parent (ChildTrace.erase decision.2) ∧
        decision.1 = logical.1.mapError Fault.language ∧
        { decision.2.graph with allocationCursor := (leading ++ middle).length } = logical.2) := by
  intro traced action decision middle stream model logical bodies
  exact selected_from_sources (depth + 1) ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth debug source address input request key slice deterministic before
    models seed values originalRows parent frame aligned leading suffix (by
      intro selected rows
      with_reducible
        exact step_source_projects ops allocate safety owner meaning base growth usizeBits depth leading stream before
          (fun world => CallFrame safety outerBase.allocator owner originalRows source values slice address input parent world ∧
            InputFrame safety outerBase.allocator owner rows source values slice world)
          (Nested.storageReads rows) debug models (bodies selected rows))

/-- The fixed input/checkpoint model consumes proper-child body replay through
the entire recorded miss and deferred close. Reached frame, selected result,
cursor alignment and stream admission are derived together. Input geometry is
the existing initialization/take obligation; no completed candidate is used. -/
theorem checkpoint_from_bodies (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (request : Interner.Request) (key : Key) (slice : ArgumentSlice)
    (deterministic : Bool) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (models : Models) (seed : Interner.Primitives) (incoming : Nat) (values : List NodeId) (originalRows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (frame : CallFrame safety outerBase.allocator owner originalRows source values slice address input parent (ChildTrace.erase before))
    (aligned : key.arguments = slice.items) (incomingAddress : deterministic = false → slice.address = incoming)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (admitted : Admitted outerOps.arguments)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let traced := children ops allocate safety owner meaning base growth usizeBits (depth + 1)
    let observations := ChildTrace.liftObservations (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)))
    let p := Caller.ProtocolTrace.Native.physical outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      traced debug source address input
    let ports := graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      traced observations debug source address input
    let decision := MissStream.selected p request key slice deterministic before
    let middle := if deterministic && request.item.kind == 1 then ports.simplify key slice before else []
    let observed := MissStream.segment outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      traced debug source address input request key slice deterministic before handle lookup
    let bodyEvents := match decision.1 with
      | .ok none => ports.insert key slice deterministic decision.2
      | _ => observed.body
    let history := leading ++ middle ++ bodyEvents ++ observed.cleanup
    let stream := history ++ trailing
    let rawStream := ChildTrace.history decision.2 ++ (bodyEvents ++ observed.cleanup ++ trailing)
    let model := replay leading rawStream before models
    let logicalModel := dispatchModel (inputGraphReplay seed input incoming meaning stream mismatch) model usizeBits debug
    let initialRecord : Caller.ProtocolTrace.Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, { lookup := some lookup, items := handle.values, phase := .cleanup }, leading⟩
    let actualBody := Caller.ProtocolTrace.missBody (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator p
      outerBase.queries ports source buffer request key deterministic initialRecord
    let resources := Interner.InvocationTrace.resources stream (.preparation .incomplete)
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources logicalModel)
      request key deterministic (Caller.ProtocolTrace.scopeView initialRecord)
    ((deterministic && (request.item.kind == 1)) = true → ∀ rows,
      BodiesAt leading rawStream before
        (fun world => CallFrame safety outerBase.allocator owner originalRows source values slice address input parent world ∧
          InputFrame safety outerBase.allocator owner rows source values slice world)
        (Nested.storageReads rows) debug (body ops allocate safety owner meaning base growth usizeBits depth) models) →
    ordinary actualBody.1 = true →
      let actual := Caller.ProtocolTrace.finish (Publication.external outerOps.arguments) outerBase.allocator actualBody.1 actualBody.2
      (actualBody.1, Caller.ProtocolTrace.scopeView actualBody.2) = (logical.1.mapError Fault.language, logical.2) ∧
      (actual.1, Caller.ProtocolTrace.scopeView actual.2) =
        (logical.1.mapError Fault.language, Interner.Scoped.close resources logical.2) ∧
      actual.2.events = history ∧ actual.2.tokens.incomplete = false := by
  intro traced observations p ports decision middle observed bodyEvents history stream rawStream model logicalModel initialRecord
    actualBody resources logical bodies completed actual
  have proper := selected_from_bodies depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth debug source address input request key slice deterministic before models seed values originalRows
    parent frame aligned leading (bodyEvents ++ observed.cleanup ++ trailing) (by with_reducible exact bodies)
  have selectedOrdinary := Caller.ProtocolTrace.missBody_selected_ordinary (Publication.external outerOps.arguments)
    outerBase.budget outerBase.allocator p outerBase.queries ports source buffer request key slice deterministic initialRecord handle rfl completed
  have checked := proper.2 selectedOrdinary
  have preserved : ordinary decision.1 = true → CallFrame safety outerBase.allocator owner originalRows source values slice address input
      (fun world => parent (ChildTrace.erase world)) decision.2 :=
    fun ordinaryResult => (CallFrame.mapAllocator_iff Prod.fst).mp (proper.2 ordinaryResult).1
  have result := Caller.ProtocolTrace.Native.checkpoint_miss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    traced observations debug source buffer address input request key slice deterministic before handle lookup model seed values originalRows
    (fun world => parent (ChildTrace.erase world)) leading stream mismatch admitted aligned detached unowned caller
    preserved ⟨trailing, rfl⟩ checked.2.1 checked.2.2 completed
  let oldModel := dispatchModel (graphReplay seed input slice meaning stream mismatch) model usizeBits debug
  have sameLogical : Interner.findCode.controlMiss (Interner.Scoped.execution resources oldModel)
      request key deterministic (Caller.ProtocolTrace.scopeView initialRecord) = logical := by
    apply MissStream.scoped_ports resources oldModel logicalModel request key deterministic _ rfl rfl
    exact insertionReplay_inputs input slice incoming meaning key deterministic stream mismatch aligned.symm incomingAddress
  change (actualBody.1, Caller.ProtocolTrace.scopeView actualBody.2) = (_, _) ∧
    (actual.1, Caller.ProtocolTrace.scopeView actual.2) = (_, _) ∧ actual.2.events = history ∧ actual.2.tokens.incomplete = false at result
  dsimp only [logical] at sameLogical
  rw [sameLogical] at result
  with_reducible exact result

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
