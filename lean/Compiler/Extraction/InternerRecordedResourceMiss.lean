/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerResourceMiss
import Compiler.Extraction.InternerMissChildTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open ConstructorItem ConstructorItem.NativeRecursion

/-- History-independent native children determine the same captured miss
boundaries for any observation family. The existing resource-aware dispatcher,
insertion, publication and cleanup proofs remain the only composition path.
Actual observations and proper-child replay must be supplied by their owners. -/
def CapturedMiss
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent) : Prop :=
  ∀ (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (request : Interner.Request) (key : Key) (slice : ArgumentSlice)
    (deterministic : Bool) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (_initial : predicate before)
    (_frame : InputFrame safety outerBase.allocator owner originalRows source values slice before)
    (_aligned : key.arguments = slice.items)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (_detached : handle.owned = none) (_unowned : lookup.owned = false) (_caller : lookup.owner = .caller),
    let traced := ChildTrace.constructors children observations
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
          request key slice deterministic before handle lookup cursor model seed tailLeading trailing mismatch)

theorem scoped_recorded_resources
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent) :
    CapturedMiss safety owner usizeBits meaning outerOps outerAllocate outerBase outerGrowth children observations := by
  intro debug source address input request key slice deterministic before model seed predicate values originalRows initial frame aligned
    handle lookup leading trailing mismatch detached unowned caller
  intro traced action captured middle cursor tailLeading observed stream coupled
  have boundaries := child_boundaries outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    children observations debug source address input
    request key slice deterministic before leading.length
  have admitted : Resource.Admitted ChildTrace.history stream action before := by
    simpa only [stream, List.append_assoc] using
      Resource.Admitted.captured ChildTrace.history action before (observed.body ++ observed.cleanup ++ trailing)
  have complete := MissStream.scoped_from_resources outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    traced debug source address input request key slice deterministic before ChildTrace.history stream cursor model seed
    predicate values originalRows initial frame aligned coupled handle lookup tailLeading trailing mismatch detached unowned caller admitted
  refine ⟨boundaries.1, complete.1, fun completed => complete.2 completed ?_⟩
  simpa only [tailLeading, List.length_append] using boundaries.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
