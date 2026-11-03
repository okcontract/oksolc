/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointNativeCaller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open NativeRecursion Recursive Caller.ProtocolTrace Interner.InvocationTrace

/-- Actual constructor entry supplies the frame, ownership and complete stream
needed by the proper-child induction. The only recursive premise is the
canonical source-aware resource relation. -/
theorem item_induction_from_sources (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (allocators : outerBase.allocator = base.allocator)
    (debug : AssemblyItem.Fields.Values) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (models : List ProtocolEvent → AllocationTrace.Models) (seed : Interner.Primitives)
    (stream leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (stack : Enclosing safety base.allocator owner parent)
    (facts : NativeGraph.Facts safety outerBase.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (retained : ∀ after : ChildTrace.TracedWorld σ ProtocolEvent, Valid after.memory → after.graph = before.graph →
      Retains before after → parent (ChildTrace.erase after))
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : Admitted ops.arguments) (outerAdmitted : Admitted outerOps.arguments)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (sources : AllocationTrace.RecursiveSources ops allocate safety owner usizeBits meaning base growth debug depth models) :
    let children := AllocationTrace.children ops allocate safety owner meaning base growth usizeBits depth
    let observations := ChildTrace.liftObservations
      (NativeRecursion.ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits depth))
    let entryContext := NativeRecursion.context (callerContext outerOps outerAllocate safety owner meaning outerBase outerGrowth)
      owner usizeBits children debug
    let entryPorts := AllocationTrace.graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      children observations debug
    let actual := item entryContext entryPorts source request debug before leading
    ordinary actual.1 = true → actual.2.events ++ trailing = stream →
    ItemInduction outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children observations debug
      (AllocationTrace.streamReplay stream (models stream)) seed stream mismatch before.memory.memory.nextId source request before leading trailing := by
  intro children observations entryContext entryPorts actual completed joined
  intro constructed address memory made room allocated
  obtain ⟨addressed, item⟩ := prepare_success request.item debug before constructed address facts.valid domain typed made
  have constructedFacts := facts.frame item.valid (by rw [item.graph]; exact facts.projected)
    (congrArg Interner.Heap.table item.graph) (congrArg Publication.Effects.keys item.effects)
    (fun id cell found _ => item.memory id cell found) (fun _ _ found => item.heap ▸ found)
  have nativeItem := item.represented
  rw [← addressed] at nativeItem
  have returned := (item_returned entryContext entryPorts source request debug before constructed address _ memory leading
    made room allocated).2.1
  have result := congrArg Prod.fst returned
  have history := congrArg (fun outcome => outcome.2.2.1) returned
  change actual.1 = _ at result
  change actual.2.events = _ at history
  rw [result] at completed
  rw [history] at joined
  have ordinaryBody := finish_body_ordinary _ _ _ _ completed
  have checked := Caller.ProtocolTrace.Native.CheckpointEntry.caller_induction_from_sources depth ops allocate safety owner usizeBits
    meaning base growth outerOps outerAllocate outerBase outerGrowth allocators debug source request constructed address
    (input request.item debug) memory _ data capacity rows parent models seed stream leading trailing mismatch stack constructedFacts
    (good_frame before constructed source request.arguments ⟨facts.valid, represented⟩ item.valid item.memory).2
    (by rw [item.effects]; exact privateSource) (array.frame (fun _ cell found => item.memory _ cell found))
    (fun after valid graph kept => retained after valid (graph.trans item.graph)
      ⟨kept.1.trans (congrArg Publication.Effects.keys item.effects),
        fun id cell found => kept.2.1 id cell (item.memory id cell found),
        fun id block found => kept.2.2 id block (item.heap ▸ found)⟩)
    nativeItem rfl allocated admitted outerAdmitted typed sources ordinaryBody joined
  have cursor : constructed.memory.memory.nextId + 1 = before.memory.memory.nextId + 2 := by
    rw [item.nextId]
  simpa only [cursor] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointEntry
