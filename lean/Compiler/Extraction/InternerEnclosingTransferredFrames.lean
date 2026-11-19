/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingPublishedFrames
import Compiler.Extraction.InternerNativeUnrelocatedTransferred

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The same original child provenance separates the transferred row from
all enclosing callers. Each step shares the native storage-framing proof. -/
theorem Enclosing.transferred {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {original before after : World (Publication.Effects σ)}
    (initial : parent original) (reached : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values original taken owned lookup)
    {rows : List Storage.Cell} {data : Compiler.ZigAir.Memory.Address} {capacity : Nat} {row : Storage.Cell}
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (post : TransferredFrame safety allocator owner data capacity rows owned row before after) :
    parent after := by
  induction stack with
  | root => trivial
  | call outer ih =>
    exact post.parent origin initial reached facts (ih initial.parent reached.parent)

/-- Actual transferred first, spare or no-remap growth completes handoff and lookup cleanup,
preserving the native graph and enclosing chain without a final-frame premise. -/
theorem Enclosing.insertion_transferred {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    (frame : CallFrame safety allocator owner rows source request.arguments owned address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : Insertion.Native.TransferredObservation ops allocate allocator owner native growth world) :
    let ran := (do let _ ← handoff; graph (fun slice => Insertion.Native.insert ops allocate safety allocator owner
      source address meaning native key slice false growth) : Action (Publication.Effects σ) NodeId)
      ⟨world, ⟨some lookup, some owned, false⟩⟩
    FramePost (GraphFrame safety allocator owner rows parent)
      (OwnedCall.finish (Publication.external ops.arguments) allocator ran.1 ran.2) := by
  obtain ⟨result, added, data, capacity, row, facts, post⟩ :=
    frame.transferred ops allocate growth meaning key room success
  have kept := stack.transferred initial frame.parent origin facts post
  have finished := finish_handoff (Publication.external ops.arguments) allocator lookup owned world
    (fun slice => Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice false growth)
    origin.detached
  simp only [result] at finished
  change FramePost (GraphFrame safety allocator owner rows parent) _
  simp only [bind, Effect.bind, handoff, OwnedCall.graph] at finished ⊢
  rw [finished]
  intro _
  obtain ⟨data, capacity, native⟩ := post.native
  exact ⟨⟨rfl, Or.inl rfl⟩, ⟨added ++ [row], data, capacity, by simpa only [List.append_assoc] using native⟩, kept⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
