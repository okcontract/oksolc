/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorEntryWords
import Compiler.Extraction.InternerAllocationRecursiveWords
import Compiler.Extraction.InternerNativeInvocation
import Compiler.Extraction.InternerAllocationRecursiveReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (env : AddressMask.Environment) (other : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)
    (allocators : outerBase.allocator = base.allocator) (budgets : outerBase.budget = base.budget)
    (queries : outerBase.queries = base.queries)
    (debug : AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments) (outerAdmitted : Admitted outerOps.arguments)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : ∀ item, outerBase.queries.deterministic item = Interner.Queries.queries.deterministic item)
    (capacityQuery : ∀ heap cursor, seed.atCapacity {heap with allocationCursor := cursor} = outerBase.queries.atCapacity heap)
    (classificationQuery : ∀ item, seed.deterministic item = outerBase.queries.deterministic item)

include hosts allocators budgets queries admitted outerAdmitted typed closedQuery capacityQuery classificationQuery mismatch

/-- The complete raw item invocation consumes closed proper-child replay and
word laws, then reuses the existing native scope/frame induction. Actual entry
supplies the stream and identity; no child law, final graph or successful
allocation is a premise. All initial native admission remains explicit. -/
theorem recursive_invocation_verified (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other)
    (depth : Nat) (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (stack : Enclosing safety base.allocator owner parent)
    (source : View) (request : Interner.Request) (before : World (Publication.Effects σ))
    (initial : parent before) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph) (expected : Word)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected) :
    let nativeBase := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth
    let nativeChildren := NativeRecursion.unfold nativeBase owner usizeBits depth
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent) before.graph
      (invoke nativeBase.external base.budget base.allocator
        ((context nativeBase owner usizeBits nativeChildren debug).primitives source) base.queries source request debug before) expected := by
  intro nativeBase nativeChildren
  let meaning := Dispatch.wordDispatchMeaning env other
  let root : ChildTrace.TracedWorld σ ProtocolEvent := ChildTrace.restore [] before
  let observations := NativeRecursion.ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth)
  let nativeContext := context nativeBase owner usizeBits nativeChildren debug
  let nativePorts := graphObservations ops allocate safety owner meaning base growth usizeBits nativeChildren observations debug
  let tracedChildren := children ops allocate safety owner meaning base growth usizeBits depth
  let entryContext := context (callerContext outerOps outerAllocate safety owner meaning outerBase outerGrowth)
    owner usizeBits tracedChildren debug
  let entryPorts := graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    tracedChildren (ChildTrace.liftObservations observations) debug
  let captured := ConstructorItem.ProtocolTrace.item entryContext entryPorts source request debug root []
  let stream := captured.2.events
  let models := recursiveModels meaning usizeBits seed stream mismatch depth
  have sources := recursive_sources ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth hosts allocators budgets queries debug seed mismatch
    admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth
  have outerFacts : NativeGraph.Facts safety outerBase.allocator owner data capacity root rows := by
    rw [allocators]
    exact (NativeGraph.Facts.mapAllocator_iff (fun effects => (effects, ([] : List ProtocolEvent)))).mpr facts
  have projected := ConstructorItem.ProtocolTrace.CheckpointEntry.item_from_sources depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth allocators debug (recursiveModels meaning usizeBits seed · mismatch depth) seed
    stream [] [] mismatch rows parent stack root (by simpa only [root, ChildTrace.erase_restore] using initial)
    data capacity outerFacts admitted outerAdmitted typed sources closedQuery (capacityQuery _ _) classificationQuery
    source request represented privateSource array domain (List.append_nil _)
  have words := recursive_words env other usizeBits seed stream mismatch pushes pushValues depth
  have safe := requestModel_safe env other usizeBits seed stream mismatch (streamReplay stream models)
    words.correct words.addresses words.shifts debug before.memory.memory.nextId request
    {before.graph with allocationCursor := 0} expected (valid.with_cursor _) (fun _ => pushValues) evaluated
  have nativeWords := projected.words _ _ _ _ _ _ meaning expected (by simpa only [List.append_nil] using safe)
  have mapped : ConstructorItem.ProtocolTrace.item nativeContext nativePorts source request debug before [] =
      ConstructorItem.ProtocolTrace.mapReturn (Publication.Effects.mapAllocator Prod.fst) captured :=
    ConstructorItem.ProtocolTrace.EffectTransport.item
    (context_erases (hosts.callerBase safety owner meaning budgets allocators queries) owner usizeBits
      (children_erases ops allocate safety owner meaning base growth usizeBits depth) debug)
    (checkpoint_observations_traced hosts safety owner meaning allocators usizeBits nativeChildren observations debug)
    source request debug root []
  have erased : invoke nativeBase.external base.budget base.allocator (nativeContext.primitives source)
      base.queries source request debug before =
      (captured.1, captured.2.native.mapEffects (Publication.Effects.mapAllocator Prod.fst)) := by
    change invoke nativeContext.external nativeContext.budget nativeContext.allocator (nativeContext.primitives source)
      nativeContext.queries source request debug before = _
    rw [ConstructorItem.ProtocolTrace.item_erases nativeContext nativePorts source request debug before [], mapped]
    rfl
  have frames := stack.unfold_invocation_frame ops allocate safety owner usizeBits base growth meaning debug depth rows parent
    source request before initial data capacity facts represented privateSource array domain admitted typed
  intro completed
  refine ⟨(frames completed).1, (frames completed).2, ?_⟩
  rw [erased]
  exact nativeWords

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
