/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecordedResourceMiss
import Compiler.Extraction.InternerAllocationSourceReplay
import Compiler.Extraction.InternerNativeFrameEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

/-- The actual allocation-aware family now consumes the same complete scoped
miss composition as the earlier protocol-only family. Native children and their
computed observations retain the same inputs and depth. No copied insertion,
publication or cleanup proof is needed. Proper-child replay remains explicit. -/
theorem scoped_resource_miss (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) :
    MissStream.CapturedMiss safety owner usizeBits meaning outerOps outerAllocate outerBase outerGrowth
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) :=
  MissStream.scoped_recorded_resources safety owner usizeBits meaning outerOps outerAllocate outerBase outerGrowth
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth))

/-- Native input ownership is transported without losing the raw history
prefix required to interpret the caller-relative allocation cursor. -/
theorem frame_input (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (predicate : World (Publication.Effects σ) → Prop) (safety : Bool) (allocator owner : Nat)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (slice : ArgumentSlice) :
    (fun world => Frame root predicate world ∧ InputFrame safety allocator owner rows source values slice world) =
      Frame root (fun world => predicate world ∧ InputFrame safety allocator owner rows source values slice world) := by
  funext world
  apply propext
  simp only [Frame, ChildTrace.erase, InputFrame.mapAllocator_iff, and_left_comm, and_comm]


/-- Consume the common entry proof in the complete scoped miss. The remaining
premise is replay of each actual native body, including its proper children;
entry identities, admission, rebasing and cursor advance are derived here. -/
theorem scoped_from_bodies (depth : Nat)
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
    (models : Models) (seed : Interner.Primitives)
    (predicate : World (Publication.Effects σ) → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate (ChildTrace.erase before))
    (frame : InputFrame safety outerBase.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    let traced := children ops allocate safety owner meaning base growth usizeBits (depth + 1)
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
    let model := replay leading stream before models
    ((deterministic && (request.item.kind == 1)) = true → ∀ rows,
      BodiesAt leading stream before
        (fun world => predicate world ∧ InputFrame safety outerBase.allocator owner rows source values slice world)
        (Nested.storageReads rows) debug (body ops allocate safety owner meaning base growth usizeBits depth) models) →
      ChildTrace.history (action before).2 = ChildTrace.history before ++ middle ∧
      MissStream.Completion outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
        request key slice deterministic before handle lookup values tailLeading trailing mismatch ∧
      (ordinary (action before).1 = true →
        MissStream.Projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
          request key slice deterministic before handle lookup cursor model seed tailLeading trailing mismatch) := by
  intro traced action captured middle cursor tailLeading observed stream model bodies
  refine scoped_resource_miss (depth + 1) ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth debug source address input request key slice deterministic before model seed
    (Frame before predicate) values originalRows ⟨initial, List.prefix_refl _⟩ frame aligned
    handle lookup leading trailing mismatch detached unowned caller ?_
  intro selected rows
  rw [frame_input]
  exact step_source_projects ops allocate safety owner meaning base growth usizeBits depth leading stream before
    (fun world => predicate world ∧ InputFrame safety outerBase.allocator owner rows source values slice world)
    (Nested.storageReads rows) debug models (bodies selected rows)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
