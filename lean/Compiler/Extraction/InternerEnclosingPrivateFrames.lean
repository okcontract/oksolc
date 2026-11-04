/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Native facts inspect the representatives and key table. Word interpretation
and the logical allocation cursor are separate semantic obligations. -/
theorem NativeGraph.Facts.graph {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell}
    {world : World (Publication.Effects σ)} (facts : NativeGraph.Facts safety allocator owner data capacity world rows)
    (graph : Interner.Heap) (representatives : graph.representatives = world.graph.representatives)
    (table : graph.table = world.graph.table) :
    NativeGraph.Facts safety allocator owner data capacity { world with graph } rows :=
  facts.logical_fields graph representatives table

namespace ConstructorItem.NativeRecursion

/-- The existing enclosing predicates retain the same native observations
when only the logical word interpretation or cursor changes. This is not a
semantic equivalence or permission to alter the actual execution. -/
theorem Enclosing.logical_fields {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {world : World (Publication.Effects σ)} (held : parent world)
    (graph : Interner.Heap) (representatives : graph.representatives = world.graph.representatives)
    (table : graph.table = world.graph.table) : parent { world with graph } := by
  induction stack with
  | root => trivial
  | call outer ih =>
    obtain ⟨⟨⟨added, data, capacity, facts, custody, privateSource⟩, input⟩, item, parent, array⟩ := held
    exact ⟨⟨⟨added, data, capacity, facts.graph graph representatives table, custody, privateSource⟩, input⟩,
      item, ih parent, array⟩

/-- Original child provenance and reached custody derive every ancestor's
private-cleanup law. Effects and all new allocations remain those of cleanup. -/
theorem Enclosing.private_frame {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before world : World (Publication.Effects σ)} (initial : parent before) (reached : parent world)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    {rows : List Storage.Cell} (projected : world.graph.representatives = some rows)
    (custody : Caller.GraphCustody allocator owned rows world.memory)
    {after : Session (Publication.Effects σ)} (valid : Valid after)
    (frame : Insertion.Native.PrivateFrame owned world.memory after) :
    parent { world with memory := after } := by
  induction stack with
  | root => trivial
  | call outer ih =>
    exact CallFrame.private_frame origin initial reached projected custody valid frame
      (ih initial.parent reached.parent)

end ConstructorItem.NativeRecursion
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
