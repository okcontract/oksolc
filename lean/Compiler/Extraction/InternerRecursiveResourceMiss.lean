/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecordedResourceMiss
import Compiler.Extraction.InternerRecursiveProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

/-- Actual finite child captures supply the resource stream and both child
boundaries of the scoped miss. The stream includes the existing insertion or
publication suffix and deferred cleanup. Neither successful allocation nor
dispatcher admission/cursor equality is a caller premise. Proper-child resource
correspondence, native entry validity and a shared logical model remain duties
of the recursive induction. -/
theorem scoped_resource_miss (depth : Nat)
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
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety outerBase.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let traced := children ops allocate safety owner meaning base growth usizeBits depth
    let action := MissStream.selected
      (MissStream.physical outerOps outerAllocate safety owner meaning outerBase outerGrowth owner usizeBits traced debug source address input)
      request key slice deterministic
    let captured := action (ChildTrace.restore [] (ChildTrace.erase before))
    let middle := ChildTrace.history captured.2
    let cursor := MissStream.childCursor leading.length before
    let tailLeading := leading ++ middle
    let observed := MissStream.segment outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
      request key slice deterministic before handle lookup
    let stream := ChildTrace.history (action before).2 ++ observed.body ++ observed.cleanup ++ trailing
    ((deterministic && (request.item.kind == 1)) = true → ∀ rows,
      (Resource.projection ChildTrace.history stream (cursorGraph cursor) (fun world => predicate world ∧
        InputFrame safety outerBase.allocator owner rows source values slice world)).SourceConstructorsAt
          (Nested.storageReads rows) debug traced model) →
      ChildTrace.history (action before).2 = ChildTrace.history before ++ middle ∧
      MissStream.Completion outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
        request key slice deterministic before handle lookup values tailLeading trailing mismatch ∧
      (ordinary (action before).1 = true →
        MissStream.Projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
          request key slice deterministic before handle lookup cursor model seed tailLeading trailing mismatch) :=
  MissStream.scoped_recorded_resources safety owner usizeBits meaning outerOps outerAllocate outerBase outerGrowth
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth))
    debug source address input request key slice deterministic before model seed predicate values originalRows initial frame aligned
    handle lookup leading trailing mismatch detached unowned caller

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
