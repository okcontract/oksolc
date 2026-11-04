/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeParentPublication
import Compiler.Extraction.InternerNativeStorageSeparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Postconditions already supplied by successful native insertion. Retain
them together for both the graph result and the live parent. This is a proof
predicate over the existing worlds and row, not a second storage model. Empty
old capacity never excludes its unallocated sentinel from either frame. -/
structure PublishedFrame (safety : Bool) (allocator owner : Nat)
    (oldData : Compiler.ZigAir.Memory.Address) (oldCapacity : Nat) (rows : List Storage.Cell)
    (key : Key) (owned : ArgumentSlice) (row : Storage.Cell)
    (before after : World (Publication.Effects σ)) : Prop where
  native : ∃ data capacity, NativeGraph.Facts safety allocator owner data capacity after (rows ++ [row])
  keys : after.memory.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, Storage.idFor rows⟩
  fresh : row.argumentsAddress = before.memory.memory.nextId
  memory : ∀ id cell, before.memory.memory.heap.lookup id = some cell → id ≠ owner →
    (oldCapacity ≠ 0 → id ≠ oldData.allocation) →
    (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
    after.memory.memory.heap.lookup id = some cell
  registry : ∀ id block, before.memory.heap id = some block →
    (oldCapacity ≠ 0 → id ≠ oldData.allocation) →
    (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
    after.memory.heap id = some block

/-- The actual successful insertion and its reached-storage witnesses. The
original key, normalized owner and fresh operand allocation remain available
when a caller specializes this result to its concrete enclosing call. -/
def PublishedReturn (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (key : Key) (owned : ArgumentSlice) (before : World (Publication.Effects σ))
    (actual : Except Fault NodeId × World (Publication.Effects σ)) : Prop :=
  actual.1 = .ok (Storage.idFor (before.graph.representatives.getD [])) ∧
    ∃ added data capacity row,
      NativeGraph.Facts safety allocator owner data capacity before (rows ++ added) ∧
      PublishedFrame safety allocator owner data capacity (rows ++ added) key owned row before actual.2

/-- Preserve the existing graph-only public result as a projection of the
stronger completion, so the conditional taken step keeps its original interface. -/
theorem PublishedReturn.graph
    {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {key : Key} {owned : ArgumentSlice} {before : World (Publication.Effects σ)}
    {actual : Except Fault NodeId × World (Publication.Effects σ)}
    (completed : PublishedReturn safety allocator owner rows key owned before actual) :
    actual.1 = .ok (Storage.idFor (before.graph.representatives.getD [])) ∧
      ∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity actual.2 (rows ++ added) := by
  obtain ⟨result, added, _, _, _, _, post⟩ := completed
  obtain ⟨data, capacity, facts⟩ := post.native
  exact ⟨result, added ++ [_], data, capacity, by simpa only [List.append_assoc] using facts⟩

/-- Successful insertion preserves the live parent through one storage frame.
Original normalization provenance separates the new key; reached custody
protects old keys, and actual duplicate freshness protects the appended operand.
Source/item separation follows the reached call's allocation provenance and
typed item reads. The next outer predicate retains its own law. -/
theorem PublishedFrame.parent
    {safety : Bool} {allocator owner oldCapacity : Nat} {oldData : Compiler.ZigAir.Memory.Address}
    {rows parentRows : List Storage.Cell} {source : View} {values : List NodeId}
    {normalized : ArgumentSlice} {address : Compiler.ZigAir.Memory.Address}
    {native : AssemblyClone.NativeFields.ItemValue} {outer : World (Publication.Effects σ) → Prop}
    {original before after : World (Publication.Effects σ)}
    {childSource : View} {request : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    {key : Key} {row : Storage.Cell}
    (origin : Caller.Origin allocator childSource request childValues original taken owned lookup)
    (initial : CallFrame safety allocator owner parentRows source values normalized address native outer original)
    (reached : CallFrame safety allocator owner parentRows source values normalized address native outer before)
    (facts : NativeGraph.Facts safety allocator owner oldData oldCapacity before rows)
    (post : PublishedFrame safety allocator owner oldData oldCapacity rows key owned row before after)
    (outerKept : outer after) :
    CallFrame safety allocator owner parentRows source values normalized address native outer after := by
  obtain ⟨added, _, _, parentFacts, custody, privateSource⟩ := reached.1.1
  have sameRows := Option.some.inj (parentFacts.projected.symm.trans facts.projected)
  subst rows
  have sourceApart := reached.arraySource.storage facts
  have itemApart := reached.2.1.storage facts
  have sourceMemory : source.length ≠ 0 → ∀ cell, before.memory.memory.heap.lookup source.allocation = some cell →
      after.memory.memory.heap.lookup source.allocation = some cell :=
    fun nonempty cell found => post.memory _ cell found (sourceApart nonempty).1 (sourceApart nonempty).2
      (fun old stored length => privateSource key old stored length nonempty)
  have live : SliceValid allocator after.memory.heap normalized := by
    by_cases empty : normalized.items = []
    · exact Or.inl empty
    · have stored := custody.live.resolve_left empty
      apply Or.inr
      exact post.registry _ _ stored (by
        intro positive same
        rw [same, (facts.storage positive).2.1] at stored
        cases stored) (by
        intro old found nonempty alias
        exact custody.apart key old found nonempty ⟨empty, alias.symm⟩)
  have kept := origin.custody_after_publication normalized initial.1.2.2.1 custody.toCustody after.memory live post.keys
  have operands : normalized.items ≠ [] → ∀ logical ∈ (parentRows ++ added) ++ [row],
      logical.arguments ≠ [] → normalized.address ≠ logical.argumentsAddress := by
    intro nonempty logical member arguments
    rcases List.mem_append.mp member with old | new
    · exact custody.operands nonempty logical old arguments
    · have same := List.mem_singleton.mp new
      subst logical
      obtain ⟨cell, found, _⟩ := facts.valid.injected _ _ (custody.live.resolve_left nonempty)
      rw [post.fresh]
      exact Nat.ne_of_lt (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
  have sourceKept : Represents after.memory.memory source values := by
    by_cases empty : values = []
    · exact ⟨reached.1.2.1.2.1, by intro index inside; simp [empty] at inside⟩
    · have nonempty : source.length ≠ 0 := by
        rw [← reached.1.2.1.2.1]; exact Nat.ne_of_gt (List.length_pos_iff.mpr empty)
      obtain ⟨cell, found⟩ := reached.1.2.1.backed nonempty
      exact represented_frame source values reached.1.2.1.2
        ((sourceMemory nonempty cell found).trans found.symm)
  obtain ⟨item, found⟩ := reached.2.1.live
  have itemKept := reached.2.1.frame ((post.memory _ item found itemApart.1 itemApart.2 (by
    intro old stored nonempty
    obtain ⟨⟨cell, located, typed, _⟩, _⟩ := facts.valid.related allocator old.address key.arguments nonempty
      ((facts.live key old stored).resolve_left nonempty)
    exact reached.2.1.apart_words _ _ cell located typed)).trans found.symm)
  obtain ⟨data, capacity, afterFacts⟩ := post.native
  refine ⟨⟨⟨added ++ [row], data, capacity, ?_, ?_, ?_⟩,
    ⟨afterFacts.valid, sourceKept⟩, live, reached.1.2.2.2⟩, itemKept, outerKept,
    reached.arraySource.frame sourceMemory⟩
  · simpa only [List.append_assoc] using afterFacts
  · exact ⟨kept, by simpa only [List.append_assoc] using operands⟩
  · exact origin.source_private_after_publication source values initial.1.2.1 privateSource post.keys

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
