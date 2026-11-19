/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphStorageFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Native facts inspect the representatives and key table. Word interpretation
and the logical allocation cursor are separate semantic obligations. -/
theorem Facts.logical_fields {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell}
    {world : World (Publication.Effects σ)} (facts : Facts safety allocator owner data capacity world rows)
    (graph : Interner.Heap) (representatives : graph.representatives = world.graph.representatives)
    (table : graph.table = world.graph.table) :
    Facts safety allocator owner data capacity { world with graph } rows :=
  { facts with projected := representatives.trans facts.projected, linked := table.trans facts.linked }

/-- These native objects supply the header, descriptor and item reads. The
existing registry/injection separately retains operand and map-key contents. -/
def Protected (owner : Nat) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (rows : List Storage.Cell) (id : Nat) : Prop :=
  id = owner ∨ (capacity ≠ 0 ∧ id = data.allocation) ∨ ∃ row ∈ rows, id = row.itemAddress

/-- Reconstruct query correspondence from retained native allocations and the
same reached registry. No final accepted-query predicate is a premise. -/
theorem Facts.frame {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {before after : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (valid : Valid after.memory)
    (projected : after.graph.representatives = some rows) (table : after.graph.table = before.graph.table)
    (keys : after.memory.effects.keys = before.memory.effects.keys)
    (native : ∀ id cell, before.memory.memory.heap.lookup id = some cell → Protected owner data capacity rows id →
      after.memory.memory.heap.lookup id = some cell)
    (registered : ∀ id block, before.memory.heap id = some block → after.memory.heap id = some block) :
    Facts safety allocator owner data capacity after rows := by
  have arguments (slice : ArgumentSlice) (live : Memory.SliceValid allocator before.memory.heap slice) :
      Memory.SliceValid allocator after.memory.heap slice := by
    rcases live with empty | stored
    · exact Or.inl empty
    · exact Or.inr (registered _ _ stored)
  obtain ⟨ownerCell, found, typed, writable⟩ := facts.ownerLive
  have ownerFrame := (native owner ownerCell found (Or.inl rfl)).trans found.symm
  have header : readHeader after.memory.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType data rows.length, .scalar (.int false 64 capacity)) := by
    unfold readHeader readItems
    rw [readField_eq_of_lookup _ _ (Owner.headerAddress ⟨owner, 0⟩) itemsOffset ownerFrame,
      readField_eq_of_lookup _ _ (Owner.headerAddress ⟨owner, 0⟩) capacityOffset ownerFrame]
    exact facts.header
  refine ⟨valid, projected, table.trans (facts.linked.trans (congrArg OwnedKeys.view keys).symm),
    ⟨ownerCell, ownerFrame.trans found, typed, writable⟩, header, facts.bounded, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro nonempty
    obtain ⟨⟨offset, _, backing, backingFound, backingTyped, backingWritable, persistent⟩, vector, descriptors⟩ := facts.storage nonempty
    have retained := native data.allocation backing backingFound (Or.inr (Or.inl ⟨nonempty, rfl⟩))
    exact ⟨⟨offset, ⟨rows, registered _ _ vector⟩, backing, retained, backingTyped, backingWritable, persistent⟩,
      registered _ _ vector, DescriptorRelation.frame _ _ _ rows descriptors (retained.trans backingFound.symm)⟩
  · intro row member
    exact ⟨registered _ _ (facts.resident row member).1, arguments _ (facts.resident row member).2⟩
  · intro row member
    obtain ⟨cell, located, cellType, query⟩ := facts.items row member
    have retained := native row.itemAddress cell located (Or.inr (Or.inr ⟨row, member, rfl⟩))
    exact ⟨cell, retained, cellType, AssemblyItem.Query.frame _ _ row (retained.trans located.symm) query⟩
  · intro query old stored
    exact arguments _ (facts.live query old (keys ▸ stored))
  · rw [keys]; exact facts.unique
  · rw [keys]; exact facts.apart
  · intro row member
    obtain ⟨cell, located, _⟩ := facts.items row member
    exact (facts.data row member).frame
      ((native row.itemAddress cell located (Or.inr (Or.inr ⟨row, member, rfl⟩))).trans located.symm)

/-- Returning constructor locals preserves persistent graph objects and the
older owner. No fixed fixture input is part of this lifetime obligation. -/
theorem Facts.cleanup {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity world rows) (mark : Nat) (ownerOlder : owner < mark) :
    Facts safety allocator owner data capacity
      { world with memory := { world.memory with memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } } rows := by
  refine facts.frame (after := { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } })
    (facts.valid.cleanup _ mark) facts.projected rfl rfl ?_ (fun _ _ found => found)
  intro id cell found retainedObject
  rcases retainedObject with rfl | ⟨nonempty, rfl⟩ | ⟨row, member, rfl⟩
  · exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ mark _ ownerOlder).trans found
  · obtain ⟨⟨_, _, backing, located, _, _, persistent⟩, _⟩ := facts.storage nonempty
    have same := Option.some.inj (found.symm.trans located)
    subst backing
    exact persistent_cleanup _ mark _ cell found persistent
  · obtain ⟨native, located, persistent⟩ := facts.valid.injected _ _ (facts.resident row member).1
    have same := Option.some.inj (found.symm.trans located)
    subst native
    exact persistent_cleanup _ mark _ cell found persistent

/-- Preparation may allocate and retire fresh objects, then release the private
normalized owner. Only old allocations outside that owner must survive. Empty
sentinels exclude no allocation. Native types and registry kinds derive graph
separation; keys and representative operands use the reached caller custody. -/
theorem Facts.frame_private {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (owned : ArgumentSlice)
    (after : Session (Publication.Effects σ))
    (live : SliceValid allocator before.memory.heap owned)
    (privateKey : OwnedKeys.Apart before.memory.effects.keys
      (fun address => owned.items ≠ [] ∧ address = owned.address))
    (privateOperands : owned.items ≠ [] → ∀ row ∈ rows, row.arguments ≠ [] → owned.address ≠ row.argumentsAddress)
    (valid : Valid after)
    (retained : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      (owned.items ≠ [] → id ≠ owned.address) →
      after.memory.heap.lookup id = some cell ∧ after.heap id = before.memory.heap id)
    (keys : after.effects.keys = before.memory.effects.keys) :
    Facts safety allocator owner data capacity { before with memory := after } rows := by
  obtain ⟨ownerCell, found, typed, writable⟩ := facts.ownerLive
  have ownerApart (nonempty : owned.items ≠ []) : owner ≠ owned.address := by
    obtain ⟨⟨native, located, shape, _⟩, _⟩ := facts.valid.related allocator owned.address owned.items nonempty (live.resolve_left nonempty)
    exact before.memory.memory.heap.lookup_ne_of_type_ne owner owned.address ownerCell native found located
      (by simp [typed, shape, Owner.viewType])
  have ownerFrame := (retained owner ownerCell found ownerApart).1.trans found.symm
  have header : readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType data rows.length, .scalar (.int false 64 capacity)) := by
    unfold readHeader readItems
    rw [readField_eq_of_lookup _ _ (Owner.headerAddress ⟨owner, 0⟩) itemsOffset ownerFrame,
      readField_eq_of_lookup _ _ (Owner.headerAddress ⟨owner, 0⟩) capacityOffset ownerFrame]
    exact facts.header
  apply facts.frame_storage owned after data capacity live privateKey privateOperands valid
    (fun id cell located _ _ apart => retained id cell located apart) keys
    ⟨ownerCell, ownerFrame.trans found, typed, writable⟩ header facts.bounded
  intro positive
  obtain ⟨⟨offset, registered, backing, located, shape, writable, persistent⟩, vector, descriptors⟩ := facts.storage positive
  have apart (nonempty : owned.items ≠ []) : data.allocation ≠ owned.address := by
    intro same
    change before.memory.heap data.allocation = some ⟨allocator, .representatives rows⟩ at vector
    rw [same, live.resolve_left nonempty] at vector
    cases vector
  have frame := retained _ backing located apart
  exact ⟨⟨offset, ⟨rows, frame.2.trans vector⟩, backing, frame.1, shape, writable, persistent⟩,
    frame.2.trans vector, DescriptorRelation.frame _ _ _ rows descriptors (frame.1.trans located.symm)⟩

/-- A private release specializes the same graph frame used after failed
preparation; no entry normalization origin or final graph premise is needed. -/
theorem Facts.release {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (owned : ArgumentSlice)
    (after : Session (Publication.Effects σ)) (nonempty : owned.items ≠ [])
    (live : SliceValid allocator before.memory.heap owned)
    (privateKey : OwnedKeys.Apart before.memory.effects.keys
      (fun address => owned.items ≠ [] ∧ address = owned.address))
    (privateOperands : ∀ row ∈ rows, row.arguments ≠ [] → owned.address ≠ row.argumentsAddress)
    (valid : Valid after)
    (released : ReleasePost before.memory.heap before.memory.memory allocator owned after.heap after.memory)
    (keys : after.effects.keys = before.memory.effects.keys) :
    Facts safety allocator owner data capacity { before with memory := after } rows := by
  apply facts.frame_private owned after live privateKey (fun _ => privateOperands) valid _ keys
  intro id cell found apart
  have kept := released.frame id (apart nonempty)
  exact ⟨kept.2.trans found, kept.1⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
