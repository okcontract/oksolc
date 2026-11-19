/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationRecursiveModels
import Compiler.Extraction.InternerCheckpointSourceReplay
import Compiler.Extraction.InternerCheckpointNativeEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- Derive the reached miss law from finite proper-child resource replay and
its actual completed recorder. Neither stream decomposition nor a selected
result or final graph correspondence is supplied by the caller. -/
theorem miss_from_recursive_sources (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (allocators : outerBase.allocator = base.allocator)
    (debug : AssemblyItem.Fields.Values) (source buffer : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (request : Interner.Request)
    (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (handle : Handle) (lookup : NormalizationOwnership.State)
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (models : List ProtocolEvent → AllocationTrace.Models) (seed : Interner.Primitives)
    (incoming : Nat) (stream leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (frame : CallFrame safety base.allocator owner rows source request.arguments slice address input parent (ChildTrace.erase before))
    (aligned : key.arguments = slice.items)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (caller : lookup.owner = .caller)
    (sources : AllocationTrace.RecursiveSources ops allocate safety owner usizeBits meaning base growth debug depth models) :
    let children := AllocationTrace.children ops allocate safety owner meaning base growth usizeBits depth
    let observations := ChildTrace.liftObservations
      (ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits depth))
    let ports := AllocationTrace.graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      children observations debug source address input
    let p := physical outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children debug source address input
    let taken : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
      ⟨⟨before, ⟨some handle, some slice, false⟩⟩, {lookup := some lookup, items := handle.values, phase := .cleanup}, leading⟩
    let body := missBody (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator p outerBase.queries
      ports source buffer request key deterministic taken
    ordinary body.1 = true →
    (finish (Publication.external outerOps.arguments) outerBase.allocator body.1 body.2).2.events ++ trailing = stream →
    Miss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children observations debug source address input
      request (AllocationTrace.streamReplay stream (models stream)) seed incoming stream mismatch key deterministic taken trailing := by
  intro children observations ports p taken body completed joined
  have kept := stack.traced_selected_frame depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth debug source address input request key slice deterministic before
    request.arguments rows parent admitted typed frame
  have history := checkpoint_miss_history outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    children observations debug source buffer address input request key slice deterministic before handle lookup
    request.arguments rows leading aligned detached unowned caller (fun done => by
      rw [allocators]
      exact ((CallFrame.mapAllocator_iff Prod.fst).mp (kept done)).1) completed
  have finalHistory := joined
  rw [history] at finalHistory
  intro otherSlice otherHandle otherLookup locals tokens otherAligned
  have sliceSame : slice = otherSlice := Option.some.inj (congrArg Local.slice locals)
  have handleSame : handle = otherHandle := Option.some.inj (congrArg Local.lookup locals)
  have lookupSame : lookup = otherLookup := Option.some.inj (congrArg (fun t : Tokens => t.lookup) tokens)
  subst otherSlice
  subst otherHandle
  subst otherLookup
  let decision := MissStream.selected p request key slice deterministic before
  let middle := if deterministic && request.item.kind == 1 then ports.simplify key slice before else []
  let observed := MissStream.segment outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    children debug source address input request key slice deterministic before handle lookup
  let bodyEvents := match decision.1 with
    | .ok none => ports.insert key slice deterministic decision.2
    | _ => observed.body
  let suffix := bodyEvents ++ observed.cleanup ++ trailing
  let rawStream := ChildTrace.history decision.2 ++ suffix
  have boundary := history_boundaries outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits depth))
    debug source address input request key slice deterministic before leading.length
  have edges : ChildTrace.history decision.2 = ChildTrace.history before ++ middle := boundary.1
  have fixedStream : AllocationTrace.rebase leading (ChildTrace.history before).length rawStream = stream := by
    change AllocationTrace.rebase leading (ChildTrace.history before).length (ChildTrace.history decision.2 ++ suffix) = stream
    rw [edges]
    simp only [AllocationTrace.rebase, List.append_assoc, List.drop_left]
    simpa only [middle, bodyEvents, observed, suffix, ports, children, observations, p, decision,
      Native.middle, AllocationTrace.graphObservations, List.append_assoc] using finalHistory
  have checked := AllocationTrace.selected_from_sources depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth debug source address input request key slice deterministic before
    (models stream) (AllocationTrace.inputGraphReplay seed input incoming meaning stream mismatch)
    request.arguments rows parent (by simpa only [allocators] using frame) aligned leading suffix (by
      intro selected reachedRows
      rw [callFrame_input, allocators]
      have proper := sources leading rawStream before reachedRows source request.arguments slice address input
        (CallFrame safety base.allocator owner rows source request.arguments slice address input parent) (.call stack)
      rw [fixedStream] at proper
      exact proper)
  refine ⟨rows, fun world => parent (ChildTrace.erase world),
    fun done => (CallFrame.mapAllocator_iff Prod.fst).mp (checked.2 done).1, finalHistory, fun done => ?_⟩
  have same := (checked.2 done).2
  rw [checked.1, AllocationTrace.replay_appended] at same
  have consumed : leading ++ Native.middle outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      children observations debug source address input request key slice deterministic before ++ suffix = stream := by
    simpa only [suffix, bodyEvents, observed, decision, p, middle, ports, Native.middle,
      AllocationTrace.graphObservations, List.append_assoc] using finalHistory
  rw [consumed] at same
  exact same

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
