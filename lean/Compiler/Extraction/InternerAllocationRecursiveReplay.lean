/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointRecursiveConstructors
import Compiler.Extraction.InternerAllocationBodyReplay
import Compiler.Extraction.InternerAllocationTraceEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)
open ConstructorItem.ProtocolTrace (Capture mapConstructors eraseCapture)

/-- The complete constructor step consumes only proper-child resource replay.
Actual entry and full capture determine native admission and each fixed model;
finite native frame preservation supplies the separate lifetime invariant. -/
theorem bodies_from_sources (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)
    (allocators : outerBase.allocator = base.allocator) (budgets : outerBase.budget = base.budget)
    (queries : outerBase.queries = base.queries)
    (debug : AssemblyItem.Fields.Values) (models : List ProtocolEvent → Models) (seed : Interner.Primitives)
    (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments) (outerAdmitted : Admitted outerOps.arguments)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (sources : RecursiveSources ops allocate safety owner usizeBits meaning base growth debug depth models)
    (closedQuery : ∀ item, outerBase.queries.deterministic item = Interner.Queries.queries.deterministic item)
    (capacityQuery : ∀ heap cursor, seed.atCapacity {heap with allocationCursor := cursor} = outerBase.queries.atCapacity heap)
    (classificationQuery : ∀ item, seed.deterministic item = outerBase.queries.deterministic item)
    (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent) :
    let completeStream := rebase leading (ChildTrace.history root).length stream
    BodiesAt leading stream root (CallFrame safety base.allocator owner rows source values normalized address native parent)
      (Nested.storageReads rows) debug (body ops allocate safety owner meaning base growth usizeBits depth)
      (bodyModels meaning usizeBits seed completeStream mismatch (streamReplay completeStream (models completeStream))) := by
  intro completeStream
  let predicate := CallFrame safety base.allocator owner rows source values normalized address native parent
  let nativeChildren := NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth
  let observations := ProtocolTrace.observe (unfold ops allocate safety owner meaning base growth usizeBits depth)
  let outerCaptured := step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (children ops allocate safety owner meaning base growth usizeBits depth) (ChildTrace.liftObservations observations)
  have prefixes :=  step_prefix ops allocate safety owner meaning base growth usizeBits nativeChildren observations
  have mapped := checkpoint_step_traced hosts safety owner meaning allocators usizeBits nativeChildren observations budgets queries
  have erased := step_erases ops allocate safety owner meaning base growth usizeBits nativeChildren observations []
  have frames := stack.unfold_frames ops allocate safety owner usizeBits base growth meaning debug (depth + 1)
    rows source values normalized address native parent admitted typed
  change (keeping predicate).SourceConstructorsAt (Nested.storageReads rows) debug
    (NativeRecursion.step (callerContext ops allocate safety owner meaning base growth) owner usizeBits nativeChildren)
    (NativeRecursion.step (callerContext ops allocate safety owner meaning base growth) owner usizeBits nativeChildren) at frames
  rw [← erased] at frames
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro opcode ids
    change BodyReplay _ _ _ _ _ (fun ids => Interner.Scoped.find _ _ _)
    apply body_replay_from_traced_entry (outerAction := outerCaptured.operation opcode ids debug)
    · intro before earlier rest
      exact congrArg (fun family => family.operation opcode ids debug before) (prefixes earlier rest)
    · intro before leading
      exact congrArg (fun family => family.operation opcode ids debug before leading) mapped
    · intro before initial completed
      exact frames.operation opcode ids () before initial completed
    · intro before earlier trailing held joined
      obtain ⟨added, data, capacity, facts, _⟩ := held.1.1.1
      have outerFacts : NativeGraph.Facts safety outerBase.allocator owner data capacity before (rows ++ added) := by
        rw [allocators]
        exact (NativeGraph.Facts.mapAllocator_iff Prod.fst).mp facts
      exact ConstructorItem.ProtocolTrace.CheckpointEntry.operation_from_sources depth ops allocate safety owner usizeBits meaning base growth
        outerOps outerAllocate outerBase outerGrowth allocators debug models seed completeStream (leading ++ earlier) trailing mismatch
        (rows ++ added) predicate (.call stack) before held.1 data capacity outerFacts admitted outerAdmitted typed sources
        closedQuery (capacityQuery _ _) classificationQuery opcode ids joined
  · intro value
    change BodyReplay _ _ _ _ _ (fun ids => Interner.Scoped.find _ _ _)
    apply body_replay_from_traced_entry (outerAction := outerCaptured.constant value debug)
    · intro before earlier rest
      exact congrArg (fun family => family.constant value debug before) (prefixes earlier rest)
    · intro before leading
      exact congrArg (fun family => family.constant value debug before leading) mapped
    · intro before initial completed
      exact frames.constant value () before initial completed
    · intro before earlier trailing held joined
      obtain ⟨added, data, capacity, facts, _⟩ := held.1.1.1
      have outerFacts : NativeGraph.Facts safety outerBase.allocator owner data capacity before (rows ++ added) := by
        rw [allocators]
        exact (NativeGraph.Facts.mapAllocator_iff Prod.fst).mp facts
      exact ConstructorItem.ProtocolTrace.CheckpointEntry.constant_from_sources depth ops allocate safety owner usizeBits meaning base growth
        outerOps outerAllocate outerBase outerGrowth allocators debug models seed completeStream (leading ++ earlier) trailing mismatch
        (rows ++ added) predicate (.call stack) before held.1 data capacity outerFacts admitted outerAdmitted typed sources
        closedQuery (capacityQuery _ _) classificationQuery value joined
  · intro id value
    change BodyReplay _ _ _ _ _ (fun ids => Interner.Scoped.find _ _ _)
    apply body_replay_from_traced_entry (outerAction := outerCaptured.materialize id value debug)
    · intro before earlier rest
      exact congrArg (fun family => family.materialize id value debug before) (prefixes earlier rest)
    · intro before leading
      exact congrArg (fun family => family.materialize id value debug before leading) mapped
    · intro before initial completed
      exact frames.materialize id value () before initial completed
    · intro before earlier trailing held joined
      obtain ⟨added, data, capacity, facts, _⟩ := held.1.1.1
      have outerFacts : NativeGraph.Facts safety outerBase.allocator owner data capacity before (rows ++ added) := by
        rw [allocators]
        exact (NativeGraph.Facts.mapAllocator_iff Prod.fst).mp facts
      exact ConstructorItem.ProtocolTrace.CheckpointEntry.materialize_from_sources depth ops allocate safety owner usizeBits meaning base growth
        outerOps outerAllocate outerBase outerGrowth allocators debug models seed completeStream (leading ++ earlier) trailing mismatch
        (rows ++ added) predicate (.call stack) before held.1 data capacity outerFacts admitted outerAdmitted typed sources
        closedQuery (capacityQuery _ _) classificationQuery id value joined
  · intro id queried slice found opcode
    change BodyReplay _ _ _ _ _ (fun ids => Interner.Scoped.find _ _ _)
    apply body_replay_from_traced_entry (outerAction := outerCaptured.borrowedOperation slice.address opcode slice.items debug)
    · intro before earlier rest
      exact congrArg (fun family => family.borrowedOperation slice.address opcode slice.items debug before) (prefixes earlier rest)
    · intro before leading
      exact congrArg (fun family => family.borrowedOperation slice.address opcode slice.items debug before leading) mapped
    · intro before initial completed
      exact frames.borrowedOperation id queried slice found opcode () before initial completed
    · intro before earlier trailing held joined
      obtain ⟨added, data, capacity, facts, _⟩ := held.1.1.1
      have outerFacts : NativeGraph.Facts safety outerBase.allocator owner data capacity before (rows ++ added) := by
        rw [allocators]
        exact (NativeGraph.Facts.mapAllocator_iff Prod.fst).mp facts
      obtain ⟨represented, privateSource, array⟩ := outerFacts.source_after_append rows added id queried slice found
      exact ConstructorItem.ProtocolTrace.CheckpointEntry.borrowed_from_sources depth ops allocate safety owner usizeBits meaning base growth
        outerOps outerAllocate outerBase outerGrowth allocators debug models seed completeStream (leading ++ earlier) trailing mismatch
        (rows ++ added) predicate (.call stack) before held.1 data capacity outerFacts admitted outerAdmitted typed sources
        closedQuery (capacityQuery _ _) classificationQuery slice opcode represented privateSource array joined
  · intro id opcode slice found shape selected bound repeated first
    change BodyReplay _ _ _ _ _ (fun ids => Interner.Scoped.find _ _ _)
    apply body_replay_from_traced_entry (outerAction := outerCaptured.localOperation opcode slice selected repeated first debug)
    · intro before earlier rest
      exact congrArg (fun family => family.localOperation opcode slice selected repeated first debug before) (prefixes earlier rest)
    · intro before leading
      exact congrArg (fun family => family.localOperation opcode slice selected repeated first debug before leading) mapped
    · intro before initial completed
      exact frames.localOperation id opcode slice found shape selected bound repeated first () before initial completed
    · intro before earlier trailing held joined
      obtain ⟨added, data, capacity, facts, _⟩ := held.1.1.1
      have outerFacts : NativeGraph.Facts safety outerBase.allocator owner data capacity before (rows ++ added) := by
        rw [allocators]
        exact (NativeGraph.Facts.mapAllocator_iff Prod.fst).mp facts
      obtain ⟨represented, _, _⟩ := outerFacts.source_after_append rows added id opcode slice found
      rcases slice with ⟨sliceAddress, items⟩
      obtain ⟨left, right, equal⟩ : ∃ left right, items = [left, right] := by
        cases items with
        | nil => simp at shape
        | cons left rest =>
          cases rest with
          | nil => simp at shape
          | cons right rest =>
            cases rest with
            | nil => exact ⟨left, right, rfl⟩
            | cons head tail => simp at shape
      subst items
      exact ConstructorItem.ProtocolTrace.CheckpointEntry.local_from_sources depth ops allocate safety owner usizeBits meaning base growth
        outerOps outerAllocate outerBase outerGrowth allocators debug models seed completeStream (leading ++ earlier) trailing mismatch
        (rows ++ added) predicate (.call stack) before held.1 data capacity outerFacts admitted outerAdmitted typed sources
        closedQuery (capacityQuery _ _) classificationQuery sliceAddress opcode left right repeated selected first represented (fun _ => bound) joined

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)
open ConstructorItem.ProtocolTrace (Capture mapConstructors eraseCapture)

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
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

include hosts allocators budgets queries admitted outerAdmitted typed closedQuery capacityQuery classificationQuery

/-- Every finite native constructor family replays against its recursively
constructed model. Proper-child correspondence is discharged by induction;
exhaustion remains nonordinary, and ordinary OOM is replayed with full cleanup. -/
theorem recursive_sources (depth : Nat) :
    RecursiveSources ops allocate safety owner usizeBits meaning base growth debug depth
      (fun stream => recursiveModels meaning usizeBits seed stream mismatch depth) := by
  induction depth with
  | zero => exact recursive_sources_zero ops allocate safety owner usizeBits meaning base growth debug
  | succ depth ih =>
    intro leading stream root rows source values normalized address native parent stack
    apply step_source_projects ops allocate safety owner meaning base growth usizeBits depth
    exact bodies_from_sources depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      hosts allocators budgets queries debug (fun stream => recursiveModels meaning usizeBits seed stream mismatch depth) seed mismatch
      admitted outerAdmitted typed ih closedQuery capacityQuery classificationQuery leading stream root
      rows source values normalized address native parent stack

/-- Complete body replay has no recursive result, reached model, final graph,
selected-dispatcher correspondence or stream-decomposition hypothesis. -/
theorem recursive_bodies (depth : Nat)
    (leading stream : List ProtocolEvent) (root : ChildTrace.TracedWorld σ ProtocolEvent)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent) :
    BodiesAt leading stream root (CallFrame safety base.allocator owner rows source values normalized address native parent)
      (Nested.storageReads rows) debug (body ops allocate safety owner meaning base growth usizeBits depth)
      (recursiveModels meaning usizeBits seed (rebase leading (ChildTrace.history root).length stream) mismatch (depth + 1)) := by
  simp (config := { failIfUnchanged := false }) only [recursiveModels]
  with_reducible
    exact bodies_from_sources depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      hosts allocators budgets queries debug (fun stream => recursiveModels meaning usizeBits seed stream mismatch depth) seed mismatch
      admitted outerAdmitted typed
      (recursive_sources ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
        hosts allocators budgets queries debug seed mismatch admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth)
      closedQuery capacityQuery classificationQuery leading stream root rows source values normalized address native parent stack
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
