/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeParentRelease

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Retain the postconditions of actual publication rollback for both its graph
and enclosing callers. The new backing may remain allocated, while the old
backing and private normalized owner may be retired. This is a proof predicate
over the existing worlds, not a second execution or storage model. -/
structure RollbackFrame (safety : Bool) (allocator owner : Nat)
    (oldData : Compiler.ZigAir.Memory.Address) (oldCapacity : Nat) (rows : List Storage.Cell)
    (owned : ArgumentSlice) (before after : World (Publication.Effects σ)) : Prop where
  native : ∃ data capacity, NativeGraph.Facts safety allocator owner data capacity after rows
  projected : after.graph = { before.graph with read := Storage.readValue rows }
  keys : after.memory.effects.keys = before.memory.effects.keys
  retained : ∀ id cell, before.memory.memory.heap.lookup id = some cell → id ≠ owner →
    (oldCapacity ≠ 0 → id ≠ oldData.allocation) → (owned.items ≠ [] → id ≠ owned.address) →
    after.memory.memory.heap.lookup id = some cell ∧ after.memory.heap id = before.memory.heap id
  consumed : Consumed owned after.memory

/-- Actual rollback together with the reached storage needed by its callers. -/
def RollbackReturn (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (owned : ArgumentSlice) (before : World (Publication.Effects σ))
    (actual : Except Fault NodeId × World (Publication.Effects σ)) : Prop :=
  actual.1 = .error (.language .outOfMemory) ∧
    ∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity before (rows ++ added) ∧
      RollbackFrame safety allocator owner data capacity (rows ++ added) owned before actual.2

/-- Preserve the existing graph-only interface. Exact logical graph equality
uses its original read-coherence premise; native framing itself does not. -/
theorem RollbackReturn.graph {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {owned : ArgumentSlice} {before : World (Publication.Effects σ)}
    {actual : Except Fault NodeId × World (Publication.Effects σ)}
    (completed : RollbackReturn safety allocator owner rows owned before actual)
    (reads : before.graph.read = Storage.readValue (before.graph.representatives.getD [])) :
    actual.1 = .error (.language .outOfMemory) ∧
      (∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity actual.2 (rows ++ added)) ∧
      actual.2.graph = before.graph ∧ Consumed owned actual.2.memory := by
  obtain ⟨result, added, data, capacity, facts, post⟩ := completed
  have same : before.graph.read = Storage.readValue (rows ++ added) := by
    simpa only [facts.projected, Option.getD_some] using reads
  refine ⟨result, ⟨added, post.native⟩, ?_, post.consumed⟩
  rw [post.projected, ← same]

/-- The original child origin separates the parent's live allocations from the
consumed owner. Reached array provenance and typed item reads separate them from
owner/backing writes. Effects and lifetime history remain those of rollback. -/
theorem RollbackFrame.parent
    {safety : Bool} {allocator owner oldCapacity : Nat} {oldData : Compiler.ZigAir.Memory.Address}
    {rows parentRows : List Storage.Cell} {source : View} {values : List NodeId}
    {normalized : ArgumentSlice} {address : Compiler.ZigAir.Memory.Address}
    {native : AssemblyClone.NativeFields.ItemValue} {outer : World (Publication.Effects σ) → Prop}
    {original before after : World (Publication.Effects σ)}
    {childSource : View} {request : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator childSource request childValues original taken owned lookup)
    (initial : CallFrame safety allocator owner parentRows source values normalized address native outer original)
    (reached : CallFrame safety allocator owner parentRows source values normalized address native outer before)
    (facts : NativeGraph.Facts safety allocator owner oldData oldCapacity before rows)
    (post : RollbackFrame safety allocator owner oldData oldCapacity rows owned before after)
    (outerKept : outer after) :
    CallFrame safety allocator owner parentRows source values normalized address native outer after :=
  CallFrame.storage_frame origin initial reached facts post.native post.keys post.retained outerKept

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
