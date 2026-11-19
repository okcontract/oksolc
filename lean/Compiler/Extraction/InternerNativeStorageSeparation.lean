/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

theorem ArraySource.storage {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell} {world : World (Publication.Effects σ)}
    {source : View} (array : ArraySource source world.memory.memory)
    (facts : NativeGraph.Facts safety allocator owner data capacity world rows) (nonempty : source.length ≠ 0) :
    source.allocation ≠ owner ∧ (capacity ≠ 0 → source.allocation ≠ data.allocation) := by
  obtain ⟨extent, cell, found, typed⟩ := array nonempty
  obtain ⟨ownerCell, ownerFound, ownerTyped, _⟩ := facts.ownerLive
  constructor
  · exact world.memory.memory.heap.lookup_ne_of_type_ne _ _ cell ownerCell found ownerFound
      (by simp [typed, ownerTyped, Owner.viewType])
  · intro positive
    obtain ⟨_, _, backing, backingFound, backingTyped, _⟩ := (facts.storage positive).1
    exact world.memory.memory.heap.lookup_ne_of_type_ne _ _ cell backing found backingFound
      (by simp [typed, backingTyped, Backing.type, Expression.allocationType, word])

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall

namespace Compiler.Extraction.AssemblyClone.NativeFields
open Compiler.ZigAir.Memory Compiler.Extraction.RepresentativeArray

theorem no_owner_item (safety : Bool) (offset : Nat) :
    acceptsView (Owner.viewType safety) offset AssemblyItem.viewType = false := by
  cases safety <;>
    simp [acceptsView, Owner.viewType, Owner.layout, Owner.allocatorOffset, Owner.allocatorLayout,
      Owner.representativesOffset, Owner.representativesLockOffset, Owner.expressionsOffset,
      RepresentativeArray.allocationType, ExpressionMap.allocationType, ExpressionMap.lockType,
      ExpressionMap.sizeOffset, ExpressionMap.availableOffset, ExpressionMap.metadataType,
      AssemblyItem.viewType, Field.type]
  all_goals repeat' first
    | (intro)
    | split at *
  all_goals simp_all [usize]

theorem no_backing_item (capacity offset : Nat) :
    acceptsView (Backing.type capacity) offset AssemblyItem.viewType = false := by
  simp [acceptsView, Backing.type, Expression.allocationType, AssemblyItem.viewType, Field.type]
  all_goals repeat' first
    | (intro)
    | split at *
  all_goals simp_all [usize]

/-- Typed item views cannot occupy either the graph owner or representative
backing, even at interior offsets. No fresh-address or final-state premise is
needed; zero capacity leaves its unallocated sentinel unrestricted. -/
theorem Represents.storage {safety : Bool} {allocator owner capacity : Nat}
    {data : Address} {rows : List Storage.Cell}
    {world : Memory.Arguments.Normalization.OwnedCall.World (Memory.Arguments.Normalization.OwnedCall.Publication.Effects σ)}
    {address : Address} {native : ItemValue} (item : Represents world.memory.memory address native)
    (facts : Memory.Arguments.Normalization.OwnedCall.NativeGraph.Facts safety allocator owner data capacity world rows) :
    address.allocation ≠ owner ∧ (capacity ≠ 0 → address.allocation ≠ data.allocation) := by
  obtain ⟨cell, found, viewed⟩ := item.backed
  obtain ⟨ownerCell, ownerFound, ownerTyped, _⟩ := facts.ownerLive
  constructor
  · intro same
    rw [same, ownerFound] at found
    cases Option.some.inj found
    rw [ownerTyped, no_owner_item] at viewed
    contradiction
  · intro positive same
    obtain ⟨_, _, backing, backingFound, backingTyped, _⟩ := (facts.storage positive).1
    rw [same, backingFound] at found
    cases Option.some.inj found
    rw [backingTyped, no_backing_item] at viewed
    contradiction

end Compiler.Extraction.AssemblyClone.NativeFields
