/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeDispatch
import Compiler.Extraction.InternerConstructorSource
import Compiler.Extraction.InternerConstructorNativeReturn
import Compiler.Extraction.InternerNativeGraphPublicationCleanup
import Compiler.Extraction.InternerCallerInsertionPreparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray Recursive

/-- The proper-child frame includes the live parent constructor item. Its
normalization origin is used only at entry, never rebased after a child. Source
allocation provenance is carried through proper children; word reads alone do
not exclude interior views into relocatable graph storage. -/
def CallFrame (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (world : World (Publication.Effects σ)) : Prop :=
  InputFrame safety allocator owner rows source values normalized world ∧
    AssemblyClone.NativeFields.Represents world.memory.memory address native ∧ parent world ∧
    ArraySource source world.memory.memory

section
variable {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}

theorem CallFrame.parent (frame : CallFrame safety allocator owner rows source values normalized address native outer world) :
    outer world := frame.2.2.1

theorem CallFrame.arraySource (frame : CallFrame safety allocator owner rows source values normalized address native outer world) :
    ArraySource source world.memory.memory := frame.2.2.2
end

/-- Reached native graph and the outer live frame, after the current caller has
consumed its own normalized owner and returned its constructor locals. -/
def GraphFrame (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop) (world : World (Publication.Effects σ)) : Prop :=
  (∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity world (rows ++ added)) ∧ parent world

/-- Native graph cleanup follows persistent item/backing ownership and the
older container; only the separate outer predicate needs its local frame law. -/
theorem GraphFrame.locals (safety : Bool) (allocator owner : Nat) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop) (itemMark scratchMark : Nat)
    (ownerOlder : owner < itemMark) (ordered : itemMark ≤ scratchMark)
    (localParent : ∀ world, parent world → parent (returnWorld itemMark scratchMark world)) :
    ∀ world, GraphFrame safety allocator owner rows parent world →
      GraphFrame safety allocator owner rows parent (returnWorld itemMark scratchMark world) := by
  intro world frame
  obtain ⟨added, data, capacity, facts⟩ := frame.1
  exact ⟨⟨added, data, capacity,
    (facts.cleanup scratchMark (Nat.lt_of_lt_of_le ownerOlder ordered)).cleanup itemMark ownerOlder⟩,
    localParent world frame.2⟩

/-- This is exact ordinary return correspondence, including the reached graph
and closed ownership scope. Rejected results retain their actual execution. -/
def Returns (frame : World σ → Prop) (actual : Except Fault α × State σ)
    (result : Except Fault α) (graph : Interner.Heap) : Prop :=
  ordinary actual.1 = true → Closed actual.2.scope ∧ frame actual.2.world ∧
    actual.1 = result ∧ actual.2.world.graph = graph

/-- Native scope and frame preservation do not depend on a logical resource
cursor. Exact result/graph correspondence and word semantics are separate. -/
def FramePost (frame : World σ → Prop) (actual : Except Fault α × State σ) : Prop :=
  ordinary actual.1 = true → Closed actual.2.scope ∧ frame actual.2.world

theorem Returns.framePost {frame : World σ → Prop} {actual : Except Fault α × State σ}
    {result : Except Fault α} {graph : Interner.Heap} (checked : Returns frame actual result graph) :
    FramePost frame actual := fun completed => ⟨(checked completed).1, (checked completed).2.1⟩

theorem Returns.of_framePost {frame : World σ → Prop} {actual : Except Fault α × State σ}
    {result : Except Fault α} {graph : Interner.Heap} (checked : FramePost frame actual)
    (projected : ordinary actual.1 = true → actual.1 = result ∧ actual.2.world.graph = graph) :
    Returns frame actual result graph :=
  fun completed => ⟨(checked completed).1, (checked completed).2, projected completed⟩

/-- Retire constructor locals in the reached native world. Rejected outcomes
retain their actual state; only ordinary outcomes require the parent law. -/
theorem FramePost.locals (frame : World σ → Prop) (actual : Except Fault α × State σ)
    (itemMark scratchMark : Nat) (checked : FramePost frame actual)
    (locals : ∀ world, frame world → frame (returnWorld itemMark scratchMark world)) :
    FramePost frame
      (if ordinary actual.1 then
        (actual.1, { actual.2 with world := returnWorld itemMark scratchMark actual.2.world })
       else actual) := by
  cases completed : ordinary actual.1 with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact checked
  | true =>
    simp only [↓reduceIte]
    intro _
    exact ⟨(checked completed).1, locals _ (checked completed).2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
