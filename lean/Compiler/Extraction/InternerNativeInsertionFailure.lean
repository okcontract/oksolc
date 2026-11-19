/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrames
import Compiler.Extraction.InternerInsertionPreparationFailure
import Compiler.Extraction.InternerInsertionNativeBody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Project the source's unappended exit and preserve the reached native graph
outside the consumed normalized owner. This is shared by direct insertion
completion and the enclosing handoff/return proof. -/
theorem CallFrame.insert_unpublished {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (deterministic : Bool)
    (reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))
    (outcome : Option Storage.Outcome) (closed : Storage.State) (after : Insertion.Native.Frame σ)
    (executed : Insertion.Native.execution ops allocate safety allocator owner source address meaning native key normalized
      deterministic (world.graph.representatives.getD []) world growth = ((.ok outcome, closed), after))
    (unappended : closed.appended = false) (unpublished : closed.published = false)
    (valid : Valid (Insertion.memory after)) (consumed : Consumed normalized (Insertion.memory after))
    (retained : Insertion.Native.PrivateFrame normalized world.memory (Insertion.memory after))
    (result : Except Fault NodeId)
    (projectedResult : (Interner.insertionOutcome (world.graph.representatives.getD []) outcome).mapError Fault.language = result)
    (parentFrame : ∀ after, Valid after → Insertion.Native.PrivateFrame normalized world.memory after →
      parent { world with memory := after }) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized deterministic growth world
    actual = (result, { world with memory := Insertion.memory after }) ∧
      GraphFrame safety allocator owner rows parent actual.2 ∧ Consumed normalized actual.2.memory := by
  obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
  simp only [facts.projected, Option.getD_some] at executed projectedResult reads
  have inserted := Insertion.Native.insert_unpublished ops allocate safety allocator owner source address meaning native key normalized
    deterministic world (rows ++ added) growth data (readHeader_items _ _ _ _ facts.header) facts.projected reads
    outcome closed after unappended unpublished executed
  rw [projectedResult] at inserted
  have preserved := facts.frame_private normalized (Insertion.memory after) frame.1.2.2.1 custody.apart custody.operands
    valid retained.allocations retained.keys
  refine ⟨inserted, ?_, ?_⟩
  · rw [inserted]
    exact ⟨⟨added, data, capacity, preserved⟩, parentFrame _ valid retained⟩
  · rw [inserted]
    exact consumed

/-- Compose a reached ordinary insertion exit before append/publication. Source
execution and private cleanup observations determine the result, native frame
and detached outer cleanup; no final caller or graph correspondence is assumed.
The enclosing parent's local frame law remains explicit. -/
theorem CallFrame.insertion_unpublished {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (deterministic : Bool) (lookup : Handle) (detached : lookup.owned = none)
    (logical : Interner.Represented meaning world.graph)
    (outcome : Option Storage.Outcome) (closed : Storage.State) (after : Insertion.Native.Frame σ)
    (executed : Insertion.Native.execution ops allocate safety allocator owner source address meaning native key normalized
      deterministic (world.graph.representatives.getD []) world growth = ((.ok outcome, closed), after))
    (unappended : closed.appended = false) (unpublished : closed.published = false)
    (valid : Valid (Insertion.memory after)) (consumed : Consumed normalized (Insertion.memory after))
    (retained : Insertion.Native.PrivateFrame normalized world.memory (Insertion.memory after))
    (result : Except Fault NodeId)
    (projectedResult : (Interner.insertionOutcome (world.graph.representatives.getD []) outcome).mapError Fault.language = result)
    (recoverable : ordinary result = true)
    (parentFrame : ∀ after, Valid after → Insertion.Native.PrivateFrame normalized world.memory after →
      parent { world with memory := after }) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some normalized, false⟩⟩
    let actual := OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2
    Returns (GraphFrame safety allocator owner rows parent) actual result world.graph ∧
      Consumed normalized actual.2.world.memory := by
  have reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []) := by
    obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
    simp only [Interner.Represented, facts.projected, Option.getD_some] at logical ⊢
    exact logical.1
  obtain ⟨inserted, preserved, finalConsumed⟩ := frame.insert_unpublished ops allocate growth meaning key deterministic reads
    outcome closed after executed unappended unpublished valid consumed retained result projectedResult parentFrame
  rw [inserted] at preserved finalConsumed
  have completed := finish_handoff (Publication.external ops.arguments) allocator lookup normalized world
    (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice deterministic growth) detached
  simp only [inserted, recoverable, ↓reduceIte] at completed
  change Returns (GraphFrame safety allocator owner rows parent) _ _ _ ∧ _
  simp only [bind, Effect.bind, handoff, graph] at completed ⊢
  rw [completed]
  exact ⟨fun _ => ⟨⟨rfl, Or.inl rfl⟩, preserved, rfl, rfl⟩, finalConsumed⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
