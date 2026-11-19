/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationResourceMiss
import Compiler.Extraction.InternerCheckpointConstructorReplay
import Compiler.Extraction.InternerCallerProtocolHistory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

theorem selected_from_sources (depth : Nat)
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
    let traced := children ops allocate safety owner meaning base growth usizeBits depth
    let action := MissStream.selected
      (MissStream.physical outerOps outerAllocate safety owner meaning outerBase outerGrowth owner usizeBits traced debug source address input)
      request key slice deterministic
    let decision := action before
    let middle := Caller.ProtocolTrace.Native.middle outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      traced (ChildTrace.liftObservations (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))
      debug source address input request key slice deterministic before
    let stream := ChildTrace.history decision.2 ++ suffix
    let model := replay leading stream before models
    let logical := if deterministic && request.item.kind == 1 then
      (dispatchModel seed model usizeBits debug).simplify key { before.graph with allocationCursor := leading.length }
      else (.ok none, { before.graph with allocationCursor := leading.length })
    ((deterministic && (request.item.kind == 1)) = true → ∀ rows,
      (Resource.projection ChildTrace.history stream (cursorGraph (MissStream.childCursor leading.length before))
        (Frame before (fun world => CallFrame safety outerBase.allocator owner originalRows source values slice address input parent world ∧
          InputFrame safety outerBase.allocator owner rows source values slice world))).SourceConstructorsAt
        (Nested.storageReads rows) debug traced model) →
    ChildTrace.history decision.2 = ChildTrace.history before ++ middle ∧
      (ordinary decision.1 = true →
        CallFrame safety outerBase.allocator owner originalRows source values slice address input parent (ChildTrace.erase decision.2) ∧
        decision.1 = logical.1.mapError Fault.language ∧
        { decision.2.graph with allocationCursor := (leading ++ middle).length } = logical.2) := by
  intro traced action decision middle stream model logical bodies
  let predicate := CallFrame safety outerBase.allocator owner originalRows source values slice address input parent
  have boundaries := Caller.ProtocolTrace.Native.history_boundaries outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth))
    debug source address input request key slice deterministic before leading.length
  have preserved := MissStream.selected_resource_preserved outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    traced debug source address input request key slice deterministic before ChildTrace.history stream
    (MissStream.childCursor leading.length before) model seed (Frame before predicate) values originalRows
    ⟨frame, List.prefix_refl _⟩ ((InputFrame.mapAllocator_iff Prod.fst).mp frame.1) aligned (by
      intro selected rows
      rw [frame_input]
      exact bodies selected rows)
    (Resource.Admitted.captured ChildTrace.history action before suffix)
  refine ⟨boundaries.1, fun completed => ?_⟩
  have checked := preserved completed
  refine ⟨checked.1.1.1, ?_⟩
  have stop : MissStream.childCursor leading.length before decision.2 = leading.length + middle.length := boundaries.2.2
  have same := checked.2
  change decision.1 = _ ∧ cursorGraph (MissStream.childCursor leading.length before) decision.2 = _ at same
  simpa only [cursorGraph, boundaries.2.1, stop, List.length_append] using same


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
