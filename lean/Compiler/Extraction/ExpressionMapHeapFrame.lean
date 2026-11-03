/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapWyhash
import Compiler.Extraction.InternerNativeGraphFrame

namespace Compiler.Extraction.ExpressionMap.HeapFrame
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets

variable {before after : State}

theorem loads (same : after.heap = before.heap) : load after = load before := by
  funext pointer
  simp only [load, access, same]

theorem elements (same : after.heap = before.heap) : elementPointer after = elementPointer before := by
  funext pointer index
  simp only [elementPointer, offsetPointer, pointerCast, access, same]

theorem fields (same : after.heap = before.heap) : fieldPointer after = fieldPointer before := by
  funext pointer offset
  simp only [fieldPointer, access, same]

theorem metadata (same : after.heap = before.heap) : Metadata.readByte after = Metadata.readByte before := by
  funext bucket index
  simp only [Metadata.readByte, loads same]

theorem used (same : after.heap = before.heap) : Table.Used after bucket index ↔ Table.Used before bucket index :=
  Table.used_frame (congrFun (congrFun (metadata same) bucket) index)

theorem count (same : after.heap = before.heap) : Table.count capacity bucket after = Table.count capacity bucket before := by
  unfold Table.count
  congr 1
  funext index
  simp only [Table.occupied, Metadata.observe, loads same]

theorem entry (same : after.heap = before.heap) (view : Table.EntryView capacity bucket index before key incoming) :
    Table.EntryView capacity bucket index after key incoming := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro slot
    simpa only [KeyFields.read, KeyFields.entryPointer, loads same, elements same, fields same] using view.stored.keys slot
  · simpa only [Values.read, Values.entryPointer, loads same, elements same] using view.stored.value
  · simpa only [Represents, loads same] using view.contents
  · simpa only [Memory.Arguments.Owned, same] using view.owned

theorem invariant (same : after.heap = before.heap) (valid : after.valid = true)
    (inv : Probe.Invariant hashes place safety receiver bucket capacity available before table) :
    Probe.Invariant hashes place safety receiver bucket capacity available after table := by
  have layout : Insertion.Layout place safety receiver bucket capacity after := by
    refine ⟨valid, ?_, ?_, ?_, ?_⟩
    · simpa only [same] using inv.binding.layout.receiverLive
    · simpa only [same] using inv.binding.layout.bucketLive
    · simpa only [loads same] using inv.binding.layout.metadata
    · simpa only [loads same] using inv.binding.layout.headers
  refine ⟨⟨layout, ?_, ?_, ?_, ?_, ?_⟩, inv.power, ?_, ⟨?_⟩, ?_, ?_⟩
  · simpa only [metadata same] using inv.binding.metadata
  · simpa only [loads same, count same] using inv.binding.size
  · intro i inside occupied
    obtain ⟨key, incoming, present, view⟩ := inv.binding.slots i inside ((used same).mp occupied)
    exact ⟨key, incoming, present, entry same view⟩
  · intro key incoming present
    obtain ⟨i, inside, occupied, view⟩ := inv.binding.entries key incoming present
    exact ⟨i, inside, (used same).mpr occupied, entry same view⟩
  · intro i j key incoming ib jb iu ju iv jv
    exact inv.binding.unique i j key incoming ib jb ((used same).mp iu) ((used same).mp ju)
      (entry same.symm iv) (entry same.symm jv)
  · simpa only [Probe.Canonical, metadata same] using inv.canonical
  · intro key incoming present
    obtain ⟨distance, bound, view, read, prior⟩ := inv.routing.entries key incoming present
    exact ⟨distance, bound, entry same view, by simpa only [metadata same] using read,
      by simpa only [Probe.NonFree, metadata same] using prior⟩
  · simpa only [loads same] using inv.availableRead
  · simpa only [count same] using inv.budget

end Compiler.Extraction.ExpressionMap.HeapFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Extraction.Storage Compiler.Extraction.Cache

/-- Install a returned native state without rewinding either allocation cursor.
Logical ownership and graph fields are unchanged by a private local scope. -/
def withMemory (before : World (Publication.Effects σ)) (memory : Compiler.ZigAir.Memory.State) : World (Publication.Effects σ) :=
  { before with memory := { before.memory with memory } }

theorem Facts.same_heap {data : Compiler.ZigAir.Memory.Address} (facts : Facts safety allocator owner data capacity before rows)
    (after : Compiler.ZigAir.Memory.State) (valid : after.valid = true) (same : after.heap = before.memory.memory.heap) :
    Facts safety allocator owner data capacity (withMemory before after) rows := by
  apply facts.frame (after := withMemory before after) (Valid.memory_frame before.memory after facts.valid valid
    (same ▸ Compiler.ZigAir.Memory.Heap.RetainsShape.refl _) (by intro _ _ _ _; rw [same]))
    facts.projected rfl rfl
  · intro id cell found _
    simpa only [withMemory, same] using found
  · intro id block found
    exact found

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
