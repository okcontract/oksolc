/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolHistory
import Compiler.Extraction.InternerResourceMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- Resource-conditional proper children now justify the actual recorded caller
body and deferred close. The ordinary result, full event history and completed
tokens follow from the shared native recorder and cleanup proof. -/
theorem miss_resource_verified (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (history : World (Publication.Effects σ) → List ε) (stream : List ε)
    (cursor : World (Publication.Effects σ) → Nat)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true →
      ∀ rows, (Resource.projection history stream (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller)
    (start : cursor before = leading.length)
    (admitted : Resource.Admitted history stream
      (MissStream.selected (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
        request key slice deterministic) before) :
    cursor (MissStream.selected (physical ops allocate safety owner meaning base growth usizeBits children debug source address input)
      request key slice deterministic before).2 =
        (leading ++ middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input
          request key slice deterministic before).length →
    MissProjected ops allocate safety owner meaning base growth usizeBits children observations debug source buffer address input
      request key slice deterministic before handle lookup model seed leading trailing mismatch := by
  intro boundary
  have preserved := MissStream.selected_resource_preserved ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before history stream cursor model seed predicate values originalRows initial frame aligned coupled admitted
  refine miss_from_projection ops allocate safety owner meaning base growth usizeBits children observations
    debug source buffer address input request key slice deterministic before handle lookup cursor model seed values originalRows
    aligned (fun completed => (preserved completed).1.2) leading trailing mismatch detached unowned caller start ?_
  intro completed
  exact (MissStream.scoped_from_resources ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic before history stream cursor model seed predicate values originalRows initial frame aligned coupled
    handle lookup (leading ++ middle ops allocate safety owner meaning base growth usizeBits children observations debug source address input
      request key slice deterministic before) trailing mismatch detached unowned caller admitted).2 completed boundary

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent)

/-- The actual child capture supplies admission and both replay cursor
boundaries. The native caller body consumes only the remaining resource-aware
proper-child contract; success, cleanup and a recorded final state are derived. -/
theorem miss_resource_traced (buffer : View) (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List ProtocolEvent)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let child := ChildTrace.constructors children observations
    let action := MissStream.selected
      (physical ops allocate safety owner meaning base growth usizeBits child debug source address input)
      request key slice deterministic
    let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits child debug source address input
      request key slice deterministic before handle lookup
    let stream := ChildTrace.history (action before).2 ++ observed.body ++ observed.cleanup ++ trailing
    ((deterministic && (request.item.kind == 1)) = true → ∀ rows,
      (Resource.projection ChildTrace.history stream
        (cursorGraph (MissStream.childCursor leading.length before)) (fun world => predicate world ∧
          InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt
            (Nested.storageReads rows) debug child model) →
    MissProjected ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations)
      (ChildTrace.liftObservations observations) debug source buffer address input request key slice deterministic before handle lookup
      model seed leading trailing mismatch := by
  intro child action observed stream coupled
  have bounds := history_boundaries ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    request key slice deterministic before leading.length
  have admitted : Resource.Admitted ChildTrace.history stream action before := by
    simpa only [stream, List.append_assoc] using
      Resource.Admitted.captured ChildTrace.history action before (observed.body ++ observed.cleanup ++ trailing)
  refine miss_resource_verified ops allocate safety owner meaning base growth usizeBits child
    (ChildTrace.liftObservations observations) debug source buffer address input request key slice deterministic before handle lookup
    ChildTrace.history stream (MissStream.childCursor leading.length before) model seed predicate values originalRows
    initial frame aligned coupled leading trailing mismatch detached unowned caller bounds.2.1 admitted ?_
  simpa only [List.length_append] using bounds.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
