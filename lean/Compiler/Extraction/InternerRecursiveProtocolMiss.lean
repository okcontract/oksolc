/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolHistory
import Compiler.Extraction.InternerRecursiveProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace Recursive Interner.InvocationTrace

attribute [local irreducible] unfold Caller.ProtocolTrace.Native.MissProjected

/-- Specialize the history-derived miss to the same finite native constructor
captures. Both boundaries and all child observations are computed. The proper
child's model/frame relation remains an induction obligation, not host behavior. -/
theorem miss_projected (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits depth : Nat)
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List ProtocolEvent)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (values : List NodeId) (rows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety outerBase.allocator owner rows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : ∀ rows, (projectionAt (cursorGraph (MissStream.childCursor leading.length before)) (fun world => predicate world ∧
      InputFrame safety outerBase.allocator owner rows source values slice world)).SourceConstructorsAt (Nested.storageReads rows) debug
        (children ops allocate safety owner meaning base growth usizeBits depth) model)
    (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    Caller.ProtocolTrace.Native.MissProjected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (children ops allocate safety owner meaning base growth usizeBits depth)
      (ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))
      debug source buffer address input request key slice deterministic before handle lookup model seed leading trailing mismatch :=
  Caller.ProtocolTrace.Native.miss_traced_verified outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug source address input
    request key slice deterministic before buffer handle lookup leading trailing model seed predicate values rows initial frame aligned
    (fun _ => coupled) mismatch detached unowned caller

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
