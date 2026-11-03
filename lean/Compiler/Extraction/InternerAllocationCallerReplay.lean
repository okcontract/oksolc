/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationResourceMiss
import Compiler.Extraction.InternerCallerResourceReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

/-- The actual caller body consumes resource replay of the marked proper
constructors. Entry admission, identities and caller-relative cursor alignment
are derived by the common source step; the existing native recorder then proves
body result, scoped state, complete cleanup history and non-incomplete tokens.
The proper children's body obligations remain the recursive hypothesis. -/
theorem caller_from_bodies (depth : Nat)
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
    let observed := MissStream.segment outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
      request key slice deterministic before handle lookup
    let stream := ChildTrace.history (action before).2 ++ observed.body ++ observed.cleanup ++ trailing
    let model := replay leading stream before models
    ((deterministic && (request.item.kind == 1)) = true → ∀ rows,
      BodiesAt leading stream before
        (fun world => predicate world ∧ InputFrame safety outerBase.allocator owner rows source values slice world)
        (Nested.storageReads rows) debug (body ops allocate safety owner meaning base growth usizeBits depth) models) →
      Caller.ProtocolTrace.Native.MissProjected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced
        (ChildTrace.liftObservations (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1))))
        debug source buffer address input request key slice deterministic before handle lookup model seed leading trailing mismatch := by
  intro traced action observed stream model bodies
  refine Caller.ProtocolTrace.Native.miss_resource_traced outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits (depth + 1))
    (ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)))
    debug source address input request key slice deterministic before buffer handle lookup leading trailing model seed
    (Frame before predicate) values originalRows ⟨initial, List.prefix_refl _⟩ frame aligned mismatch detached unowned caller ?_
  intro selected rows
  rw [frame_input]
  exact step_source_projects ops allocate safety owner meaning base growth usizeBits depth leading stream before
    (fun world => predicate world ∧ InputFrame safety outerBase.allocator owner rows source values slice world)
    (Nested.storageReads rows) debug models (bodies selected rows)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
