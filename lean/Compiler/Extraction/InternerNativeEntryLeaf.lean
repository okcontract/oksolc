/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeCacheHit

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul

/-- An actual entry return without a taken miss. Successful results retain
their normalized key and cache provenance; errors require no word witness.
This records native observations, without assuming a semantic invariant. -/
structure EntryLeaf (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (before : World (Publication.Effects σ)) (request : Interner.Request)
    (actual : Except Fault NodeId × State (Publication.Effects σ)) : Prop where
  closed : Closed actual.2.scope
  frame : GraphFrame safety allocator owner rows (Retains before) actual.2.world
  graph : actual.2.world.graph = before.graph
  cached : ∀ id, actual.1 = .ok id → ∃ values key,
    normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values ∧
    Interner.makeKey request values = .ok key ∧ before.graph.table key = some id

/-- Package the common native retention conclusion of the existing leaf
proofs. The successful-result provenance must come from the actual branch. -/
theorem EntryLeaf.of_native
    {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {rows : List Storage.Cell} {before : World (Publication.Effects σ)} {request : Interner.Request}
    {actual : Except Fault NodeId × State (Publication.Effects σ)} {outcome : Except Fault NodeId}
    (result : actual.1 = outcome)
    (native : NativeGraph.Facts safety allocator owner data capacity actual.2.world rows)
    (closed : Closed actual.2.scope) (graph : actual.2.world.graph = before.graph)
    (keys : actual.2.world.memory.effects.keys = before.memory.effects.keys)
    (memory : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      actual.2.world.memory.memory.heap.lookup id = some cell)
    (registry : ∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block)
    (cached : ∀ id, outcome = .ok id → ∃ values key,
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values ∧
      Interner.makeKey request values = .ok key ∧ before.graph.table key = some id) :
    EntryLeaf safety allocator owner rows before request actual := by
  exact ⟨closed, ⟨⟨[], data, capacity, by simpa only [List.append_nil] using native⟩, keys, memory, registry⟩,
    graph, fun id found => cached id (result.symm.trans found)⟩

/-- Retain an enclosing parent through any native entry leaf. No semantic
invariant or logical child correspondence is needed for this frame result. -/
theorem EntryLeaf.parent {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {before : World (Publication.Effects σ)} {request : Interner.Request}
    {actual : Except Fault NodeId × State (Publication.Effects σ)}
    (leaf : EntryLeaf safety allocator owner rows before request actual)
    {parent : World (Publication.Effects σ) → Prop}
    (retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after) :
    GraphFrame safety allocator owner rows parent actual.2.world := by
  obtain ⟨added, data, capacity, native⟩ := leaf.frame.1
  exact ⟨⟨added, data, capacity, native⟩, retained _ native.valid leaf.graph leaf.frame.2⟩

/-- Semantic preservation is a separate consumer of the same native leaf.
The only successful route is justified by its actual normalized cache key. -/
theorem EntryLeaf.words {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {before : World (Publication.Effects σ)} {request : Interner.Request}
    {actual : Except Fault NodeId × State (Publication.Effects σ)}
    (leaf : EntryLeaf safety allocator owner rows before request actual) (other : Meaning) (expected : Word)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments request.sequence = some expected) :
    Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
      (fun id after => after.read id = some expected) := by
  rw [leaf.graph]
  cases result : actual.1 with
  | error error => exact Semantic.Ensures.error _ _ _ _ valid
  | ok id =>
    obtain ⟨values, key, normalized, keyed, found⟩ := leaf.cached id result
    exact Semantic.Ensures.pure _ _ _ _ valid
      (cached_word other request values key id before.graph expected valid normalized keyed found evaluated)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
