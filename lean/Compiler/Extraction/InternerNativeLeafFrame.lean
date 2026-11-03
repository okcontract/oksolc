/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeParentEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- The unchanged-graph leaves retain these three observations together.
Keys are needed for parent custody and source privacy; native allocation and
registry retention alone do not establish that separation. This predicate does
not rewind allocator effects or claim that new local allocations remain live. -/
def Retains (before after : World (Publication.Effects σ)) : Prop :=
  after.memory.effects.keys = before.memory.effects.keys ∧
    (∀ id cell, before.memory.memory.heap.lookup id = some cell → after.memory.memory.heap.lookup id = some cell) ∧
    (∀ id block, before.memory.heap id = some block → after.memory.heap id = some block)

/-- Actual unchanged-graph retention preserves an enclosing live call. The
reached graph supplies validity; the initial call supplies its ownership and
typed item. Only the next outer predicate requires its separate return law. -/
theorem GraphFrame.retained_parent
    {safety : Bool} {allocator owner : Nat} {rows parentRows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop} {before after : World (Publication.Effects σ)}
    (reached : GraphFrame safety allocator owner rows (Retains before) after)
    (graph : after.graph = before.graph)
    (initial : CallFrame safety allocator owner parentRows source values normalized address native outer before)
    (outerKept : outer after) :
    GraphFrame safety allocator owner rows
      (CallFrame safety allocator owner parentRows source values normalized address native outer) after := by
  obtain ⟨added, data, capacity, facts⟩ := reached.1
  exact ⟨reached.1, initial.frame facts.valid graph reached.2.1 reached.2.2.1 reached.2.2.2 outerKept⟩

/-- All checked unchanged-graph step leaves specialize this same parent return.
Ordinary completion guards both the retained frame and the next outer law;
rejected executions acquire no cleanup or preservation conclusion. -/
theorem Returns.parent
    {safety : Bool} {allocator owner : Nat} {rows parentRows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop} {before : World (Publication.Effects σ)}
    {actual : Except Fault α × State (Publication.Effects σ)} {result : Except Fault α}
    (returned : Returns (GraphFrame safety allocator owner rows (Retains before)) actual result before.graph)
    (initial : CallFrame safety allocator owner parentRows source values normalized address native outer before)
    (outerKept : ordinary actual.1 = true → outer actual.2.world) :
    Returns (GraphFrame safety allocator owner rows
      (CallFrame safety allocator owner parentRows source values normalized address native outer)) actual result before.graph := by
  intro completed
  obtain ⟨closed, reached, same, graph⟩ := returned completed
  exact ⟨closed, reached.retained_parent graph initial (outerKept completed), same, graph⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
