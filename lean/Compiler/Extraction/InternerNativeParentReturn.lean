/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- A live input at child entry is older than the child's local mark. Cleanup
preserves its reached graph, private normalized owner and original source,
including offset views and empty sentinels. The reached backing and rows may
differ from entry; no whole-memory frame or rebased normalization is required. -/
theorem InputFrame.cleanup {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {before world : World (Publication.Effects σ)}
    (initial : InputFrame safety allocator owner rows source values normalized before)
    (reached : InputFrame safety allocator owner rows source values normalized world)
    (mark : Nat) (ordered : before.memory.memory.nextId ≤ mark) :
    InputFrame safety allocator owner rows source values normalized
      { world with memory := { world.memory with memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } } := by
  obtain ⟨_, _, _, initialFacts, _⟩ := initial.1
  obtain ⟨ownerCell, found, _⟩ := initialFacts.ownerLive
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ initialFacts.valid.memory found).1
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := reached.1
  have cleaned := facts.cleanup mark (Nat.lt_of_lt_of_le older ordered)
  refine ⟨⟨added, data, capacity, cleaned, ⟨⟨custody.live, custody.apart⟩, custody.operands⟩, privateSource⟩,
    ⟨cleaned.valid, ?_⟩, reached.2.2⟩
  by_cases empty : values = []
  · exact ⟨reached.2.1.2.1, by intro index inside; simp [empty] at inside⟩
  · have sourceOlder := ConstructorFrame.represented_older _ _ _ initial.2.1.1.memory initial.2.1.2 empty
    exact represented_frame source values reached.2.1.2
      (Compiler.ZigAir.Memory.cleanup_lookup_older _ mark source.allocation (Nat.lt_of_lt_of_le sourceOlder ordered))

/-- One local cleanup retains the actual parent item as well as its input.
The final outer predicate is separate from these derived native facts. -/
theorem CallFrame.cleanup {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before world : World (Publication.Effects σ)}
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    (reached : CallFrame safety allocator owner rows source values normalized address native parent world)
    (mark : Nat) (ordered : before.memory.memory.nextId ≤ mark)
    (outer : parent { world with memory := { world.memory with memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } }) :
    CallFrame safety allocator owner rows source values normalized address native parent
      { world with memory := { world.memory with memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } } := by
  obtain ⟨cell, found⟩ := initial.2.1.live
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ initial.1.2.1.1.memory found).1
  have array := reached.arraySource.cleanup mark (by
    intro nonempty
    obtain ⟨sourceCell, sourceFound⟩ := initial.1.2.1.backed nonempty
    exact Nat.lt_of_lt_of_le (Compiler.ZigAir.Memory.valid_lookup _ _ _ initial.1.2.1.1.memory sourceFound).1 ordered)
  exact ⟨initial.1.cleanup reached.1 mark ordered,
    reached.2.1.frame (Compiler.ZigAir.Memory.cleanup_lookup_older _ mark address.allocation
      (Nat.lt_of_lt_of_le older ordered)), outer, array⟩

/-- The exact `localParent` instance for an enclosing live call. Both captured
marks may lie after its entry; the source, item and normalized ownership need no
additional return assumption. The outer predicate remains explicitly separate. -/
theorem CallFrame.locals {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before : World (Publication.Effects σ)}
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    (itemMark scratchMark : Nat) (itemOrdered : before.memory.memory.nextId ≤ itemMark)
    (scratchOrdered : before.memory.memory.nextId ≤ scratchMark)
    (localOuter : ∀ world, parent world → parent (returnWorld itemMark scratchMark world)) :
    ∀ world, CallFrame safety allocator owner rows source values normalized address native parent world →
      CallFrame safety allocator owner rows source values normalized address native parent (returnWorld itemMark scratchMark world) := by
  intro world reached
  have inner : CallFrame safety allocator owner rows source values normalized address native (fun _ => True) before :=
    ⟨initial.1, initial.2.1, trivial, initial.arraySource⟩
  have scratch := inner.cleanup ⟨reached.1, reached.2.1, trivial, reached.arraySource⟩ scratchMark scratchOrdered trivial
  have returned := inner.cleanup scratch itemMark itemOrdered trivial
  exact ⟨returned.1, returned.2.1, localOuter world reached.parent, returned.arraySource⟩

/-- Instantiate the local-return obligation of `invoke_step` with a live
enclosing call. Both the child graph and parent input/item follow the shared
cleanup proofs; only the next outer predicate needs a return law. -/
theorem GraphFrame.parent_locals {safety : Bool} {allocator owner : Nat}
    {rows parentRows : List Storage.Cell} {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before : World (Publication.Effects σ)}
    (initial : CallFrame safety allocator owner parentRows source values normalized address native parent before)
    (itemMark scratchMark : Nat) (itemOrdered : before.memory.memory.nextId ≤ itemMark)
    (ordered : itemMark ≤ scratchMark)
    (localOuter : ∀ world, parent world → parent (returnWorld itemMark scratchMark world)) :
    ∀ world, GraphFrame safety allocator owner rows
      (CallFrame safety allocator owner parentRows source values normalized address native parent) world →
      GraphFrame safety allocator owner rows
        (CallFrame safety allocator owner parentRows source values normalized address native parent)
        (returnWorld itemMark scratchMark world) := by
  obtain ⟨_, _, _, facts, _⟩ := initial.1.1
  obtain ⟨cell, found, _⟩ := facts.ownerLive
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
  exact GraphFrame.locals safety allocator owner rows _ itemMark scratchMark
    (Nat.lt_of_lt_of_le older itemOrdered) ordered
    (initial.locals itemMark scratchMark itemOrdered (Nat.le_trans itemOrdered ordered) localOuter)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
