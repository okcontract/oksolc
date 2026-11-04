/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionOuterCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open RepresentativeArray

/-- Native representative mutations preserve separately owned pointees. Each
changed registry slot was absent or representative storage initially. This
single footprint covers first/spare writes and relocation's old/new backing;
callers derive both frames from the same execution. Empty sentinels need no
allocation or separation, and nonempty payload bytes retain their actual reads. -/
theorem representative_pointees (allocator container object : Nat) (targets : List Nat)
    (runtimeSafety : Bool) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (stored : AssemblyClone.NativeFields.ItemValue) (middle before after : Session σ)
    (installed : AssemblyClone.NativeFields.Installed allocator object stored middle before)
    (ownerFound : before.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (target : ∀ id ∈ targets, before.heap id = none ∨ ∃ old, Memory.Vector allocator before.heap id old)
    (registry : ∀ id, id ∉ targets → after.heap id = before.heap id)
    (frame : ∀ id, id ≠ container → id ∉ targets → after.memory.heap.lookup id = before.memory.heap.lookup id) :
    AssemblyItem.Owned allocator object after ∧
    AssemblyClone.NativeFields.Represents after.memory ⟨object, 0⟩ stored ∧
    (∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice after) ∧
    (∀ argumentAllocator slice, Memory.SliceValid argumentAllocator before.heap slice →
      Memory.SliceValid argumentAllocator after.heap slice) ∧
    (∀ payload, stored.verbatim = some payload → AssemblyClone.Physical.Reads after.memory payload.data) := by
  obtain ⟨⟨item, itemStored⟩, itemCell, itemFound, itemTyped, itemWritable, itemPersistent⟩ := installed.owned
  have itemOwnerApart := before.memory.heap.lookup_ne_of_type_ne object container itemCell ownerCell itemFound ownerFound
    (by simp [itemTyped, ownerTyped, AssemblyItem.viewType, Owner.viewType])
  have itemBackingApart : object ∉ targets := by
    intro member
    rcases target object member with absent | ⟨old, registered⟩
    · rw [absent] at itemStored; cases itemStored
    · rw [registered] at itemStored; cases itemStored
  have itemFrame := frame object itemOwnerApart itemBackingApart
  have itemOwned : AssemblyItem.Owned allocator object after := by
    refine ⟨⟨item, ?_⟩, itemCell, itemFrame.trans itemFound, itemTyped, itemWritable, itemPersistent⟩
    rw [registry object itemBackingApart]
    exact itemStored
  have payloadOwned : ∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice after := by
    intro slice selected
    rcases installed.payload slice selected with empty | owned
    · exact Or.inl empty
    · obtain ⟨payloadStored, payloadCell, payloadFound, payloadTyped, payloadWritable, payloadPersistent, offset⟩ := owned
      have ownerApart := before.memory.heap.lookup_ne_of_type_ne slice.address container payloadCell ownerCell payloadFound ownerFound
        (by simp [payloadTyped, ownerTyped, Owner.viewType])
      have backingApart : slice.address ∉ targets := by
        intro member
        rcases target slice.address member with absent | ⟨old, registered⟩
        · rw [absent] at payloadStored; cases payloadStored
        · rw [registered] at payloadStored; cases payloadStored
      refine Or.inr ⟨?_, payloadCell, (frame slice.address ownerApart backingApart).trans payloadFound,
        payloadTyped, payloadWritable, payloadPersistent, offset⟩
      rw [registry slice.address backingApart]
      exact payloadStored
  have argumentFrame : ∀ argumentAllocator slice, Memory.SliceValid argumentAllocator before.heap slice →
      Memory.SliceValid argumentAllocator after.heap slice := by
    intro argumentAllocator slice live
    rcases live with empty | stored
    · exact Or.inl empty
    · have apart : slice.address ∉ targets := by
        intro member
        rcases target slice.address member with absent | ⟨old, registered⟩
        · rw [absent] at stored; cases stored
        · rw [registered] at stored; cases stored
      apply Or.inr
      rw [registry slice.address apart]
      exact stored
  refine ⟨itemOwned, AssemblyClone.NativeFields.Represents.frame installed.reads itemFrame, payloadOwned, argumentFrame, ?_⟩
  intro payload selected
  by_cases empty : payload.data.contents = []
  · intro value index present; simp [empty] at present
  · have selectedSlice : AssemblyClone.Physical.payload stored = some (AssemblyClone.Physical.descriptor payload.data) := by
      simp only [AssemblyClone.Physical.payload, selected, Option.map_some]
    have nonempty : (AssemblyClone.Physical.descriptor payload.data).length ≠ 0 := by
      intro zero
      exact empty (List.eq_nil_of_length_eq_zero zero)
    obtain ⟨payloadStored, payloadCell, payloadFound, payloadTyped, _, _, _⟩ := (installed.payload _ selectedSlice).resolve_left nonempty
    change before.heap payload.data.address = some ⟨allocator, .bytes payload.data.contents.length⟩ at payloadStored
    have ownerApart := before.memory.heap.lookup_ne_of_type_ne payload.data.address container payloadCell ownerCell payloadFound ownerFound
      (by simp [payloadTyped, ownerTyped, Owner.viewType])
    have backingApart : payload.data.address ∉ targets := by
      intro member
      rcases target payload.data.address member with absent | ⟨old, registered⟩
      · rw [absent] at payloadStored; cases payloadStored
      · rw [registered] at payloadStored; cases payloadStored
    exact (installed.contents payload selected).frame before.memory after.memory payload.data (frame _ ownerApart backingApart)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
