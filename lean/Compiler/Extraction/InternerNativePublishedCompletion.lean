/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFirstCompletion
import Compiler.Extraction.InternerNativeSpareCompletion
import Compiler.Extraction.InternerNativeGrowingCompletion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache RepresentativeArray

/-- Source observations for the publication paths with derived native frames.
This union is consumed once by the general step; uncovered insertion outcomes
remain explicit obligations. It is not a final-frame or preservation premise. -/
def PublishedObservation (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (growth : Option (Growth.Registered.Callbacks σ)) (world : World (Publication.Effects σ)) : Prop :=
  FirstPublished ops allocate safety allocator owner meaning input key normalized world ∨
  SparePublished ops allocate safety allocator owner meaning input key normalized world ∨
  RelocatedPublished ops allocate safety allocator owner meaning input key normalized growth world

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- One completion theorem for the derived publication paths. Actual empty,
spare or relocated storage determines the specialization; the reached graph
and input custody supply the common invariant. Retained physical postconditions
support both the graph projection and the shared enclosing-parent proof. -/
theorem CallFrame.published_frame {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key normalized growth world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    PublishedReturn safety allocator owner rows key normalized world actual := by
  rcases success with first | spare | relocated
  · exact frame.first_published ops allocate growth meaning key admitted aligned first
  · exact frame.spare_published ops allocate growth meaning key admitted aligned room spare
  · exact frame.growing_published ops allocate growth meaning key admitted aligned room relocated

/-- The existing graph-only completion is the projection used by the taken
step. Parent clients consume the same stronger completion directly. -/
theorem CallFrame.published {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key normalized growth world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    actual.1 = .ok (Storage.idFor (world.graph.representatives.getD [])) ∧
      ∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity actual.2 (rows ++ added) := by
  exact (frame.published_frame ops allocate growth meaning key admitted aligned room success).graph

/-- Actual first/spare/no-remap success derives the enclosing call frame from
the same completion used for the graph result. The reached call frame supplies
source provenance and typed item separation; empty sentinels stay unrestricted.
The original child origin is retained across recursive work. -/
theorem CallFrame.published_parent
    {safety : Bool} {allocator owner : Nat} {rows parentRows : List Storage.Cell}
    {source parentSource : View} {request : Interner.Request} {values parentValues : List NodeId}
    {normalized parentNormalized : ArgumentSlice} {lookup : Handle}
    {address parentAddress : Compiler.ZigAir.Memory.Address}
    {native parentNative : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop} {original world : World (Publication.Effects σ)}
    {taken : State (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source request.arguments normalized address native
      (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer) world)
    (origin : Caller.Origin allocator source request values original taken normalized lookup)
    (initial : CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized
      parentAddress parentNative outer original)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : Insertion.Native.PublishedObservation ops allocate safety allocator owner meaning native key normalized growth world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    outer actual.2 →
      actual.1 = .ok (Storage.idFor (world.graph.representatives.getD [])) ∧
      GraphFrame safety allocator owner rows
        (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer) actual.2 := by
  dsimp only
  intro outerKept
  have completed := frame.published_frame ops allocate growth meaning key admitted aligned room success
  have graph := completed.graph
  obtain ⟨result, added, data, capacity, row, facts, post⟩ := completed
  exact ⟨result, graph.2, post.parent origin initial frame.parent facts outerKept⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
