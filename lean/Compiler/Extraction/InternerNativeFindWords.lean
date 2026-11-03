/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInvocationAdmission

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

attribute [local irreducible] NativeRecursion.unfold

/-- The exact native find body, followed by its actual deferred cleanup,
preserves words on ordinary outcomes. The original represented native item and
source supply admission; closed finite replay supplies child correctness.
Caller.Verified's ownership and cleanup-result correspondence are separate
obligations, not assumptions hidden in this word theorem. -/
theorem native_find_words (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (env : AddressMask.Environment) (other : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (debug : AssemblyItem.Fields.Values) (seed : Interner.Primitives) (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : ∀ item, base.queries.deterministic item = Interner.Queries.queries.deterministic item)
    (capacityQuery : ∀ heap cursor, seed.atCapacity {heap with allocationCursor := cursor} = base.queries.atCapacity heap)
    (classificationQuery : ∀ item, seed.deterministic item = base.queries.deterministic item)
    (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other)
    (depth : Nat) (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (stack : Enclosing safety base.allocator owner parent)
    (source : View) (request : Interner.Request) (before : World (Publication.Effects σ))
    (initial : parent before) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (item : AssemblyClone.NativeFields.Represents before.memory.memory address native)
    (sameItem : native.item = request.item)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph) (expected : Word)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected) :
    let nativeBase := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth
    let nativeChildren := NativeRecursion.unfold nativeBase owner usizeBits depth
    let actual := (context nativeBase owner usizeBits nativeChildren debug).primitives source address native
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := {before with memory := {before.memory with memory}}
    let ran := Caller.invoke nativeBase.external base.allocator
      (Caller.findBody nativeBase.external base.budget base.allocator actual base.queries source buffer request) input
    Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph ran.1 ran.2.world.graph
      (fun id after => after.read id = some expected) := by
  intro nativeBase nativeChildren actual buffer input ran
  let meaning := Dispatch.wordDispatchMeaning env other
  let outerOps := ChildTrace.HostLift.operations (ε := ProtocolEvent) ops
  let outerAllocate := ChildTrace.HostLift.backing (ε := ProtocolEvent) allocate
  let outerBase := ChildTrace.HostLift.base (ε := ProtocolEvent) base
  let outerGrowth := growth.map (ChildTrace.HostLift.growth (ε := ProtocolEvent))
  have hosts := ChildTrace.HostLift.hosts (ε := ProtocolEvent) ops allocate growth
  let root : ChildTrace.TracedWorld σ ProtocolEvent := ChildTrace.restore [] before
  let observations := NativeRecursion.ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth)
  let traced := children ops allocate safety owner meaning base growth usizeBits depth
  let p := Caller.ProtocolTrace.Native.physical outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    traced debug source address native
  let ports := graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    traced (ChildTrace.liftObservations observations) debug source address native
  let entry := ConstructorItem.ProtocolTrace.start {root with memory := {root.memory with memory}} []
  let captured := Caller.ProtocolTrace.find (Publication.external outerOps.arguments) base.budget base.allocator p base.queries
    ports source buffer request entry
  let stream := captured.2.events
  let models := recursiveModels meaning usizeBits seed stream mismatch depth
  let logical := dispatchModel (inputGraphReplay seed native (before.memory.memory.nextId + 1) meaning stream mismatch)
    (streamReplay stream models) usizeBits debug
  have sources := recursive_sources ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth hosts rfl rfl rfl debug seed mismatch
    admitted (hosts.arguments.admitted admitted) typed closedQuery capacityQuery classificationQuery depth
  have outerFacts : NativeGraph.Facts safety base.allocator owner data capacity root rows :=
    (NativeGraph.Facts.mapAllocator_iff (fun effects => (effects, ([] : List ProtocolEvent)))).mpr facts
  have lifted := stack.mapAllocator (σ := ChildTrace.Recorded σ ProtocolEvent) Prod.fst
  have projected : ConstructorItem.ProtocolTrace.EntryProjected logical request before.graph [] [] captured := by
    intro completed
    have bodyOrdinary := Caller.ProtocolTrace.finish_body_ordinary _ _ _ _ completed
    have induction := Caller.ProtocolTrace.Native.CheckpointEntry.caller_induction_from_sources depth ops allocate safety owner usizeBits
      meaning base growth outerOps outerAllocate outerBase outerGrowth rfl debug source request root address native memory pointer
      data capacity rows parent (recursiveModels meaning usizeBits seed · mismatch depth) seed stream [] [] mismatch stack outerFacts
      represented privateSource array (fun after valid graph kept =>
        lifted.retained (by simpa only [root, ChildTrace.erase_restore] using initial) valid graph kept)
      item sameItem allocated admitted (hosts.arguments.admitted admitted) typed sources bodyOrdinary (List.append_nil _)
    have checked := Caller.ProtocolTrace.Native.CheckpointEntry.find_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth
      usizeBits traced (ChildTrace.liftObservations observations) debug source address native request (streamReplay stream models) seed stream mismatch
      root memory pointer [] [] other (fun _ => none) 0 ⟨outerFacts.valid, represented⟩ (hosts.arguments.admitted admitted)
      allocated (closedQuery _) (capacityQuery _ _) (classificationQuery _) induction bodyOrdinary
    simpa only [List.append_nil] using checked
  have words := recursive_words env other usizeBits seed stream mismatch pushes pushValues depth
  have safe := callerModel_safe env other usizeBits seed stream mismatch (streamReplay stream models)
    words.correct words.addresses words.shifts debug native (before.memory.memory.nextId + 1) request sameItem
    {before.graph with allocationCursor := 0} expected (valid.with_cursor _) (fun _ => pushValues) evaluated
  have nativeWords := projected.words _ _ _ _ _ _ meaning expected (by simpa only [List.append_nil] using safe)
  have contextTransport := context_erases (hosts.callerBase safety owner meaning
    (show outerBase.budget = base.budget from rfl) (show outerBase.allocator = base.allocator from rfl)
    (show outerBase.queries = base.queries from rfl)) owner usizeBits
    (children_erases ops allocate safety owner meaning base growth usizeBits depth) debug
  let nativePorts := graphObservations ops allocate safety owner meaning base growth usizeBits nativeChildren observations debug source address native
  have mapped := Caller.ProtocolTrace.EffectTransport.find contextTransport.external base.budget base.allocator
    (contextTransport.primitives source address native) base.queries
    (checkpoint_observations_traced hosts safety owner meaning (show outerBase.allocator = base.allocator from rfl)
      usizeBits nativeChildren observations debug source address native)
    source buffer request entry
  have erased : ran = (captured.1, captured.2.native.mapEffects (Publication.Effects.mapAllocator Prod.fst)) := by
    change Caller.find nativeBase.external base.budget base.allocator actual base.queries source buffer request input = _
    rw [Caller.ProtocolTrace.find_erases nativeBase.external base.budget base.allocator actual base.queries nativePorts source buffer request input []]
    exact congrArg (fun result => (result.1, result.2.native)) mapped
  rw [erased]
  exact nativeWords

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
