/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraph

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Reconstruct the same logical rows when native owner/backing storage changes
and a private normalized owner is consumed. Typed allocations and registry kinds
derive preservation of every old item, operand and key. An empty old sentinel is
not a changed allocation: it may alias a live key or any other native object. The
caller supplies the new physical header/storage from its actual mutation. -/
theorem Facts.frame_storage {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (owned : ArgumentSlice)
    (after : Session (Publication.Effects σ)) (newData : Compiler.ZigAir.Memory.Address) (newCapacity : Nat)
    (live : SliceValid allocator before.memory.heap owned)
    (privateKey : OwnedKeys.Apart before.memory.effects.keys
      (fun address => owned.items ≠ [] ∧ address = owned.address))
    (privateOperands : owned.items ≠ [] → ∀ row ∈ rows, row.arguments ≠ [] → owned.address ≠ row.argumentsAddress)
    (valid : Valid after)
    (retained : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      id ≠ owner → (capacity ≠ 0 → id ≠ data.allocation) → (owned.items ≠ [] → id ≠ owned.address) →
      after.memory.heap.lookup id = some cell ∧ after.heap id = before.memory.heap id)
    (keys : after.effects.keys = before.memory.effects.keys)
    (ownerAfter : ∃ native, after.memory.heap.lookup owner = some native ∧
      native.type = Owner.viewType safety ∧ native.writable = true)
    (headerAfter : readHeader after.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType newData rows.length, .scalar (.int false 64 newCapacity)))
    (boundedAfter : rows.length ≤ newCapacity)
    (storageAfter : newCapacity ≠ 0 → Backing.Release.Owned allocator newData newCapacity after ∧
      Memory.Vector allocator after.heap newData.allocation rows ∧
      DescriptorRelation.Prefix after.memory newData.allocation rows) :
    Facts safety allocator owner newData newCapacity { before with memory := after } rows := by
  obtain ⟨ownerCell, ownerFound, ownerTyped, _⟩ := facts.ownerLive
  have itemFrame (row : Storage.Cell) (member : row ∈ rows) :
      after.memory.heap.lookup row.itemAddress = before.memory.memory.heap.lookup row.itemAddress ∧
      after.heap row.itemAddress = before.memory.heap row.itemAddress := by
    obtain ⟨cell, found, typed, _⟩ := facts.items row member
    have apartOwner := before.memory.memory.heap.lookup_ne_of_type_ne _ _ cell ownerCell found ownerFound
      (by simp [typed, ownerTyped, AssemblyItem.viewType, Owner.viewType])
    have apartStorage (positive : capacity ≠ 0) : row.itemAddress ≠ data.allocation := by
      intro same
      have stored := (facts.resident row member).1
      rw [same, (facts.storage positive).2.1] at stored
      cases stored
    have apartNormalized (nonempty : owned.items ≠ []) : row.itemAddress ≠ owned.address := by
      intro same
      have stored := (facts.resident row member).1
      rw [same, live.resolve_left nonempty] at stored
      cases stored
    have kept := retained _ cell found apartOwner apartStorage apartNormalized
    exact ⟨kept.1.trans found.symm, kept.2⟩
  have argumentsKept (slice : ArgumentSlice) (present : SliceValid allocator before.memory.heap slice)
      (apart : owned.items ≠ [] → slice.items ≠ [] → slice.address ≠ owned.address) :
      SliceValid allocator after.heap slice := by
    by_cases empty : slice.items = []
    · exact Or.inl empty
    · have stored := present.resolve_left empty
      obtain ⟨⟨native, found, typed, _⟩, _⟩ := facts.valid.related allocator slice.address slice.items empty stored
      have apartOwner := before.memory.memory.heap.lookup_ne_of_type_ne _ _ native ownerCell found ownerFound
        (by simp [typed, ownerTyped, Owner.viewType])
      have apartStorage (positive : capacity ≠ 0) : slice.address ≠ data.allocation := by
        intro same
        rw [same, (facts.storage positive).2.1] at stored
        cases stored
      exact Or.inr ((retained _ native found apartOwner apartStorage (fun nonempty => apart nonempty empty)).2.trans stored)
  refine ⟨valid, facts.projected, facts.linked.trans (congrArg OwnedKeys.view keys).symm,
    ownerAfter, headerAfter, boundedAfter, storageAfter, ?_, ?_, ?_, keys ▸ facts.unique, keys ▸ facts.apart, ?_⟩
  · intro row member
    exact ⟨(itemFrame row member).2.trans (facts.resident row member).1,
      argumentsKept _ (facts.resident row member).2 (fun nonempty nonemptyRow => (privateOperands nonempty row member nonemptyRow).symm)⟩
  · intro row member
    obtain ⟨cell, found, typed, reads⟩ := facts.items row member
    exact ⟨cell, (itemFrame row member).1.trans found, typed,
      AssemblyItem.Query.frame _ _ row (itemFrame row member).1 reads⟩
  · intro key old found
    rw [keys] at found
    exact argumentsKept _ (facts.live key old found)
      (fun nonempty nonemptyKey same => privateKey key old found nonemptyKey ⟨nonempty, same⟩)
  · intro row member
    exact (facts.data row member).frame (itemFrame row member).1

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
