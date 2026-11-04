/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInvocationChildHistory
import Compiler.Extraction.InternerCallerProtocolMissReplay
import Compiler.Extraction.InternerMissChildTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- The native recorder's fresh outer history equals the existing traced
dispatcher's suffix. The inner history may be nonempty; both wrappers observe
the same child at its native input. Every dispatcher result is covered. -/
theorem dispatch_history (owner usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (key : Key) (slice : ArgumentSlice) (before : ChildTrace.TracedWorld σ ProtocolEvent) :
    ChildTrace.history (dispatch owner usizeBits (ChildTrace.constructors children observations)
      (ChildTrace.liftObservations observations) debug key slice before).2 =
    ChildTrace.history ((Dispatch.simplifyWithInputs (NativeReads.reads owner before.memory.memory)
      (ChildTrace.constructors children observations) usizeBits key.instruction key.arguments debug operand slice.address)
      (ChildTrace.restore [] (ChildTrace.erase before))).2 := by
  have transported := (Recursive.erasing (Publication.Effects.mapAllocator ChildTrace.flatten)).simplify_operands
    (ChildTrace.constructors_flatten children observations) ⟨operand_erases _⟩
    (NativeReads.reads owner before.memory.memory) usizeBits key.instruction key.arguments debug slice.address
    (ChildTrace.restore [] before)
  exact (congrArg (fun ran => ChildTrace.history ran.2) transported).symm

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

/-- Identify the source-selected recorder history with the segment used by
the existing child-boundary theorem, including the skipped source guard. -/
theorem middle_history :
    let p := physical ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations)
      debug source address input
    middle ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations)
      (ChildTrace.liftObservations observations) debug source address input request key slice deterministic before =
    ChildTrace.history (MissStream.selected p request key slice deterministic (ChildTrace.restore [] (ChildTrace.erase before))).2 := by
  intro p
  simp only [middle, MissStream.selected]
  split
  · dsimp only [p, physical, MissStream.physical, graphObservations]
    rw [dispatcher_snapshot]
    exact dispatch_history owner usizeBits children observations debug key slice before
  · rfl

/-- Both cursor boundaries follow from the same computed native segment. No
event-count premise, child-success premise or unchanged-world assumption is
used. This still does not establish the children's own resource admission. -/
theorem history_boundaries (start : Nat) :
    let p := physical ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations)
      debug source address input
    let events := middle ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations)
      (ChildTrace.liftObservations observations) debug source address input request key slice deterministic before
    ChildTrace.history (MissStream.selected p request key slice deterministic before).2 = ChildTrace.history before ++ events ∧
      MissStream.childCursor start before before = start ∧
      MissStream.childCursor start before (MissStream.selected p request key slice deterministic before).2 = start + events.length := by
  have history := middle_history ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    request key slice deterministic before
  simpa only [history] using MissStream.child_boundaries ops allocate safety owner meaning base growth usizeBits children observations
    debug source address input request key slice deterministic before start

/-- Consume the computed history immediately. Proper-child model/frame
preservation remains the induction hypothesis; neither cursor boundary nor a
reached-state resource obligation is an additional premise. -/
theorem miss_traced_verified (buffer : View) (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List ProtocolEvent)
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (values : List NodeId) (originalRows : List Storage.Cell)
    (initial : predicate before)
    (frame : InputFrame safety base.allocator owner originalRows source values slice before)
    (aligned : key.arguments = slice.items)
    (coupled : (deterministic && (request.item.kind == 1)) = true →
      ∀ rows, (projectionAt (cursorGraph (MissStream.childCursor leading.length before)) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source values slice world)).SourceConstructorsAt (Nested.storageReads rows) debug (ChildTrace.constructors children observations) model)
    (mismatch : Insertion.Native.Fault)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller) :
    MissProjected ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations)
      (ChildTrace.liftObservations observations) debug source buffer address input request key slice deterministic before handle lookup
      model seed leading trailing mismatch := by
  have bounds := history_boundaries ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    request key slice deterministic before leading.length
  apply miss_verified ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations)
    (ChildTrace.liftObservations observations) debug source buffer address input request key slice deterministic before handle lookup
    (MissStream.childCursor leading.length before) model seed predicate values originalRows initial frame aligned coupled
    leading trailing mismatch detached unowned caller bounds.2.1
  simpa only [List.length_append] using bounds.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
