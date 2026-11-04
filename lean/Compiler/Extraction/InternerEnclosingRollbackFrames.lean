/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingTransferredFrames
import Compiler.Extraction.InternerNativePublicationRollback

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- One actual rollback frame preserves the finite chain of enclosing calls.
Each ancestor uses its original liveness and reached source/item geometry. -/
theorem Enclosing.rolled_back {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {original before after : World (Publication.Effects σ)}
    (initial : parent original) (reached : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values original taken owned lookup)
    {rows : List Storage.Cell} {data : Compiler.ZigAir.Memory.Address} {capacity : Nat}
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (post : RollbackFrame safety allocator owner data capacity rows owned before after) :
    parent after := by
  induction stack with
  | root => trivial
  | call outer ih =>
    exact post.parent origin initial reached facts (ih initial.parent reached.parent)

/-- First, spare and no-remap relocated publication refusal preserve the
enclosing callers through the actual insertion, handoff and lookup return.
No final parent or logical read-coherence premise is assumed. -/
theorem Enclosing.insertion_rollback {safety : Bool} {allocator owner : Nat}
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
    (refused : Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key owned growth world) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice true growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some owned, false⟩⟩
    FramePost (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) := by
  obtain ⟨result, added, data, capacity, facts, post⟩ :=
    frame.publication_rollback_frame ops allocate growth meaning key admitted aligned room refused
  have kept := stack.rolled_back initial frame.parent origin facts post
  have finished := finish_handoff (Publication.external ops.arguments) allocator lookup owned world
    (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice true growth)
    origin.detached
  simp only [result] at finished
  change FramePost (GraphFrame safety allocator owner rows parent) _
  simp only [bind, Effect.bind, handoff, OwnedCall.graph] at finished ⊢
  rw [finished]
  intro _
  exact ⟨⟨rfl, Or.inl rfl⟩, ⟨added, post.native⟩, kept⟩

/-- Reduce the remaining insertion obligation by actual publication rollback,
in addition to the already derived private failures and successful publication.
First/spare and no-remap relocated transfer are derived as well; uncovered
insertion outcomes retain their explicit obligation. -/
theorem Enclosing.insertion_rollback_derived {safety : Bool} {allocator owner : Nat}
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
      (deterministic = true → ¬ Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key owned growth world) →
      (deterministic = false → ¬ Insertion.Native.TransferredObservation ops allocate allocator owner native growth world) →
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
  refine stack.insertion_derived initial origin frame ops allocate growth meaning key deterministic admitted aligned ?_
  intro room preparation backing publication
  cases deterministic with
  | false =>
    by_cases transferred : Insertion.Native.TransferredObservation ops allocate allocator owner native growth world
    · exact stack.insertion_transferred initial origin frame ops allocate growth meaning key room transferred
    · exact remaining room preparation backing publication (by simp) (fun _ => transferred)
  | true =>
    by_cases refused : Insertion.Native.RefusedObservation ops allocate safety allocator owner meaning native key owned growth world
    · exact stack.insertion_rollback initial origin frame ops allocate growth meaning key admitted aligned room refused
    · exact remaining room preparation backing publication (fun _ => refused) (by simp)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
