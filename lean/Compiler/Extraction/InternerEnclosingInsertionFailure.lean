/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingPrivateFrames
import Compiler.Extraction.InternerNativeInsertionModel

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The actual unappended, unpublished native exit preserves all enclosing
calls and closes the detached lookup. Only native source postconditions enter;
no logical read equality or final enclosing frame is assumed. -/
theorem Enclosing.insertion_unpublished {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    (frame : CallFrame safety allocator owner rows source request.arguments owned address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (outcome : Option Storage.Outcome) (closed : Storage.State) (after : Insertion.Native.Frame σ)
    (executed : Insertion.Native.execution ops allocate safety allocator owner source address meaning native key owned
      deterministic (world.graph.representatives.getD []) world growth = ((.ok outcome, closed), after))
    (unappended : closed.appended = false) (unpublished : closed.published = false)
    (valid : Valid (Insertion.memory after))
    (retained : Insertion.Native.PrivateFrame owned world.memory (Insertion.memory after)) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some owned, false⟩⟩
    FramePost (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) := by
  obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
  simp only [facts.projected, Option.getD_some] at executed
  let reached := { world with
    graph := { world.graph with read := Storage.readValue (rows ++ added) }
    memory := Insertion.memory after }
  have inserted := Insertion.Native.insert_unpublished_projected ops allocate safety allocator owner source address meaning native key owned
    deterministic world (rows ++ added) growth data (readHeader_items _ _ _ _ facts.header)
    facts.projected outcome closed after unappended unpublished executed
  have kept := facts.frame_private owned (Insertion.memory after) custody.live custody.apart custody.operands
    valid retained.allocations retained.keys
  have parentKept := stack.private_frame initial frame.parent origin facts.projected custody valid retained
  have preserved : GraphFrame safety allocator owner rows parent reached :=
    ⟨⟨added, data, capacity, kept.graph reached.graph rfl rfl⟩,
      stack.logical_fields parentKept reached.graph rfl rfl⟩
  have finished := finish_handoff (Publication.external ops.arguments) allocator lookup owned world
    (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice deterministic growth)
    origin.detached
  simp only [inserted] at finished
  change FramePost (GraphFrame safety allocator owner rows parent) _
  simp only [bind, Effect.bind, handoff, graph] at finished ⊢
  rw [finished]
  split
  · intro _; exact ⟨⟨rfl, Or.inl rfl⟩, preserved⟩
  · intro ordinary; contradiction

/-- Derive capacity, preparation refusal in both ownership modes and
backing refusal in both modes before consulting the remaining insertion
obligation. Later append/publication outcomes remain explicit. All cases execute the
same native insertion, handoff and detached-lookup return. -/
theorem Enclosing.insertion_frame {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    (frame : CallFrame safety allocator owner rows source request.arguments owned address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (admitted : Admitted ops.arguments)
    (remaining : (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      (¬ Insertion.Native.PreparationOOMAt ops allocator native owned deterministic world.memory) →
      (¬ Insertion.Native.BackingAllocationOOMAt ops allocate allocator owner native owned deterministic growth world) →
      let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
        source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
        ⟨world, ⟨some lookup, some owned, false⟩⟩
      FramePost (GraphFrame safety allocator owner rows parent)
        (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2)) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice deterministic growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some owned, false⟩⟩
    FramePost (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) := by
  classical
  obtain ⟨added, data, capacity, facts, custody, _⟩ := frame.1.1
  by_cases room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1
  · by_cases failed : Insertion.Native.PreparationOOMAt ops allocator native owned deterministic world.memory
    · obtain ⟨after, closed, executed, unappended, unpublished, valid, _, retained⟩ :=
        Insertion.Native.preparation_oom_execution_at ops allocate growth safety allocator owner source address meaning native key owned
          deterministic (world.graph.representatives.getD []) world facts.valid custody.live frame.2.1 admitted room failed
      exact stack.insertion_unpublished initial origin frame ops allocate growth meaning key deterministic
        (some .allocationFailure) closed after executed unappended unpublished valid retained
    · by_cases backing : Insertion.Native.BackingAllocationOOMAt ops allocate allocator owner native owned deterministic growth world
      · obtain ⟨after, executed, valid, retained, _⟩ := frame.backing_oom_execution_at ops allocate deterministic growth meaning key room admitted backing
        exact stack.insertion_unpublished initial origin frame ops allocate growth meaning key deterministic (some .allocationFailure)
          (Insertion.Native.appendFailureState deterministic) after executed
          (by cases deterministic <;> rfl) (by cases deterministic <;> rfl) valid retained
      · exact remaining room failed backing
  · obtain ⟨released, freed, valid, post, _⟩ := free_valid (Publication.external ops.arguments) allocator owned
      world.memory facts.valid custody.live
    have executed := Insertion.Native.capacity_execution ops allocate safety allocator owner source address meaning native key owned
      deterministic (world.graph.representatives.getD []) world growth released (by omega) freed
    exact stack.insertion_unpublished initial origin frame ops allocate growth meaning key deterministic (some .capacityFailure)
      (Storage.Release.normalized.run Storage.normalizedOwnership) _ executed rfl rfl valid
      (Insertion.Native.free_private_frame _ _ _ _ _ freed post)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
