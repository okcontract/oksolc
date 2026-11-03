/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingInsertionFailure
import Compiler.Extraction.InternerNativePublishedCompletion
import Compiler.Extraction.InternerNativeStorageSeparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- One physical publication frame preserves every enclosing call. Source
provenance and typed item reads derive storage separation at the reached world;
the original child origin supplies separation from its published owner. -/
theorem Enclosing.published {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {original before after : World (Publication.Effects σ)}
    (initial : parent original) (reached : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values original taken owned lookup)
    {rows : List Storage.Cell} {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    {key : Key} {row : Storage.Cell}
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (post : PublishedFrame safety allocator owner data capacity rows key owned row before after) :
    parent after := by
  induction stack with
  | root => trivial
  | call outer ih =>
    exact post.parent origin initial reached facts (ih initial.parent reached.parent)

/-- Successful first, spare-capacity and no-remap relocation insertion closes
the lookup and preserves the whole enclosing chain. It uses the same native
completion as the graph-only step, with no final parent-frame premise. -/
theorem Enclosing.insertion_published {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    (frame : CallFrame safety allocator owner rows source request.arguments owned address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = owned.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key owned growth world) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice true growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some owned, false⟩⟩
    FramePost (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) := by
  have completed := frame.published_frame ops allocate growth meaning key admitted aligned room success
  have graph := completed.graph
  obtain ⟨result, added, data, capacity, row, facts, post⟩ := completed
  have kept := stack.published initial frame.parent origin facts post
  have finished := finish_handoff (Publication.external ops.arguments) allocator lookup owned world
    (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice true growth)
    origin.detached
  simp only [result] at finished
  change FramePost (GraphFrame safety allocator owner rows parent) _
  simp only [bind, Effect.bind, handoff, OwnedCall.graph] at finished ⊢
  rw [finished]
  intro _
  exact ⟨⟨rfl, Or.inl rfl⟩, graph.2, kept⟩

/-- Compose the existing private-failure reduction with successful publication.
Only uncovered native outcomes retain an insertion-frame obligation. Source
provenance is supplied by the existing call frame carried by proper children. -/
theorem Enclosing.insertion_derived {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    (frame : CallFrame safety allocator owner rows source request.arguments owned address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key) (deterministic : Bool)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = owned.items)
    (remaining : (world.graph.representatives.getD []).length < 2 ^ 32 - 1 →
      (¬ Insertion.Native.PreparationOOMAt ops allocator native owned deterministic world.memory) →
      (¬ Insertion.Native.BackingAllocationOOMAt ops allocate allocator owner native owned deterministic growth world) →
      (deterministic = true → ¬ Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key owned growth world) →
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
  apply stack.insertion_frame initial origin frame ops allocate growth meaning key deterministic admitted
  intro room preparation backing
  cases deterministic with
  | false => exact remaining room preparation backing (by simp)
  | true =>
    by_cases success : Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key owned growth world
    · exact stack.insertion_published initial origin frame ops allocate growth meaning key admitted aligned room success
    · exact remaining room preparation backing (fun _ => success)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
