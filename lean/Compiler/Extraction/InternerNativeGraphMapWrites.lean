/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphStorageFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Map fields may change inside the owner allocation. The existing graph
invariant follows from the retained representative header and other allocations;
no unchanged-owner or post-state query correspondence is assumed. This frame
does not yet account for allocating or retiring native bucket storage. -/
theorem Facts.map_frame {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (memory : Compiler.ZigAir.Memory.State)
    (frame : ExpressionMap.Initialization.Frame safety before.memory.memory memory owner) :
    Facts safety allocator owner data capacity { before with memory := { before.memory with memory } } rows := by
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  obtain ⟨updatedOwner, updatedFound, ownerShape⟩ := frame.shape owner ownerCell ownerFound
  have valid : Valid ({ before.memory with memory } : Session (Publication.Effects σ)) := by
    refine ⟨frame.valid, ?_, facts.valid.injected.retained frame.shape⟩
    intro allocator id values nonempty stored
    obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ := facts.valid.related allocator id values nonempty stored
    have apart := before.memory.memory.heap.lookup_ne_of_type_ne id owner cell ownerCell found ownerFound
      (by simp [typed, ownerTyped, Owner.viewType])
    have kept := frame.allocations id apart
    exact ⟨⟨cell, kept.trans found, typed, writable, persistent⟩, represented_frame _ values represented kept⟩
  apply facts.frame_storage ⟨0, []⟩ { before.memory with memory } data capacity (Or.inl rfl)
    (by intro key old present nonempty impossible; exact impossible.1 rfl)
    (by intro impossible; exact False.elim (impossible rfl)) valid
    (fun id cell found apart _ _ => ⟨(frame.allocations id apart).trans found, rfl⟩) rfl
    ⟨updatedOwner, updatedFound, ownerShape.2.1.trans ownerTyped, ownerShape.2.2.1.trans ownerWritable⟩
    (frame.header.trans facts.header) facts.bounded
  intro positive
  obtain ⟨⟨offset, registered, backing, found, typed, writable, persistent⟩, vector, descriptors⟩ := facts.storage positive
  have apart := before.memory.memory.heap.lookup_ne_of_type_ne data.allocation owner backing ownerCell found ownerFound
    (by simp [typed, ownerTyped, Owner.viewType, Backing.type])
  have kept := frame.allocations data.allocation apart
  exact ⟨⟨offset, registered, backing, kept.trans found, typed, writable, persistent⟩, vector,
    DescriptorRelation.frame _ _ _ rows descriptors kept⟩

/-- Derive total native field writes and the next graph invariant from the
original graph and a valid, correctly typed field value. Query, ownership and
allocation-frame postconditions are consequences of the actual store. -/
theorem Facts.write_map {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (slot : ExpressionMap.Initialization.Slot) (value : Compiler.ZigAir.Memory.Value)
    (valueType : value.type = slot.value.type) (valueValid : value.valid = true) (active : slot.Active safety) :
    ∃ memory, ExpressionMap.Initialization.writeValue safety before.memory.memory ⟨owner, 0⟩ slot value = .ok memory ∧
      ExpressionMap.Initialization.WrittenValue safety before.memory.memory memory owner slot value ∧
      Facts safety allocator owner data capacity { before with memory := { before.memory with memory } } rows := by
  obtain ⟨cell, found, typed, writable⟩ := facts.ownerLive
  obtain ⟨memory, ran, post⟩ := ExpressionMap.Initialization.write_value_verified safety before.memory.memory owner cell
    slot value valueType valueValid active facts.valid.memory found typed writable
  exact ⟨memory, ran, post, facts.map_frame memory post.toFrame⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
