/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapSlotFrame

namespace Compiler.Extraction.ExpressionMap.Table
open Compiler.ZigAir.Memory Buckets Insertion
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

/-- Native observations of an existing owned-key entry. The argument contents
and live allocation are the existing word-array relations, not a second heap.
Empty slices need no live sentinel. -/
structure EntryView (capacity : BitVec 32) (bucket index : Nat) (state : State) (key : Key) (entry : OwnedKeys.Entry) : Prop where
  stored : Entry.Stored capacity bucket index key ⟨entry.address, 0⟩ entry.id state
  contents : Represents state (Memory.Arguments.view (OwnedKeys.slice key entry)) key.arguments
  owned : key.arguments ≠ [] → Memory.Arguments.Owned state entry.address key.arguments.length

/-- Equal pointer/length fields alone cannot identify a key. Actual argument
reads close the equality before a native slot can determine its logical entry. -/
theorem EntryView.unique (a : EntryView capacity bucket index state ka ea) (b : EntryView capacity bucket index state kb eb) :
    ka = kb ∧ ea = eb := by
  have field (slot : KeyFields.Slot) : KeyFields.value ka ⟨ea.address, 0⟩ slot = KeyFields.value kb ⟨eb.address, 0⟩ slot :=
    Except.ok.inj ((a.stored.keys slot).symm.trans (b.stored.keys slot))
  have kind : ka.kind = kb.kind := BitVec.eq_of_toNat_eq (Int.ofNat.inj (by simpa [KeyFields.value] using field .kind))
  have instruction : ka.instruction = kb.instruction := BitVec.eq_of_toNat_eq (Int.ofNat.inj (by simpa [KeyFields.value] using field .instruction))
  have data : ka.data = kb.data := BitVec.eq_of_toNat_eq (Int.ofNat.inj (by simpa [KeyFields.value] using field .data))
  have sequence : ka.sequence = kb.sequence := BitVec.eq_of_toNat_eq (Int.ofNat.inj (by simpa [KeyFields.value] using field .sequence))
  have descriptor : ea.address = eb.address ∧ ka.arguments.length = kb.arguments.length := by
    simpa [KeyFields.value] using field .arguments
  have identifier : ea.id = eb.id := BitVec.eq_of_toNat_eq (Int.ofNat.inj (by simpa [number] using Except.ok.inj (a.stored.value.symm.trans b.stored.value)))
  have arguments : ka.arguments = kb.arguments := by
    apply List.ext_getElem descriptor.2
    intro i ha hb
    have first := a.contents.2 i ha
    have second := b.contents.2 i hb
    have same : (Memory.Arguments.view (OwnedKeys.slice ka ea)).pointer i =
        (Memory.Arguments.view (OwnedKeys.slice kb eb)).pointer i := by
      simp [Memory.Arguments.view, OwnedKeys.slice, View.pointer, View.address, descriptor.1]
    rw [same] at first
    exact BitVec.eq_of_toNat_eq (Int.ofNat.inj (by simpa [number] using Except.ok.inj (first.symm.trans second)))
  constructor
  · cases ka; cases kb; simp_all
  · cases ea; cases eb; simp_all

/-- Original logical liveness supplies native argument contents through the
existing registry relation; the entry fields must still come from actual reads. -/
theorem EntryView.of_live (valid : Memory.Arguments.Normalization.Valid session)
    (live : Memory.SliceValid allocator session.heap (OwnedKeys.slice key entry))
    (stored : Entry.Stored capacity bucket index key ⟨entry.address, 0⟩ entry.id session.memory) :
    EntryView capacity bucket index session.memory key entry := by
  by_cases empty : key.arguments = []
  · refine ⟨stored, ?_, fun impossible => False.elim (impossible empty)⟩
    simp [Represents, Memory.Arguments.view, OwnedKeys.slice, empty]
  · have related := valid.related allocator entry.address key.arguments empty (live.resolve_left empty)
    exact ⟨stored, related.2, fun _ => related.1⟩

/-- Every old argument allocation is separated by its existing native type
from both receiver and bucket. Publication therefore retains its contents. -/
theorem EntryView.frame (id : BitVec 32) (view : EntryView capacity bucket other before oldKey oldEntry)
    (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (layout : Layout place safety receiver bucket capacity before) (inside : index < capacity.toNat)
    (otherInside : other < capacity.toNat) (apart : other ≠ index) :
    EntryView capacity bucket other after oldKey oldEntry := by
  have stored := post.stored_other layout inside other otherInside apart oldKey ⟨oldEntry.address, 0⟩ oldEntry.id view.stored
  by_cases empty : oldKey.arguments = []
  · refine ⟨stored, ?_, fun impossible => False.elim (impossible empty)⟩
    simp [Represents, Memory.Arguments.view, OwnedKeys.slice, empty]
  · obtain ⟨cell, found, typed, writable, stack⟩ := view.owned empty
    obtain ⟨r, rf, rt, _⟩ := layout.receiverLive
    obtain ⟨b, bf, bt, _⟩ := layout.bucketLive
    have ra : oldEntry.address ≠ receiver := before.heap.lookup_ne_of_type_ne _ _ cell r found rf (by
      cases place <;> simp [typed, rt, Initialization.Placement.type, RepresentativeArray.Owner.viewType, allocationType])
    have ba : oldEntry.address ≠ bucket := before.heap.lookup_ne_of_type_ne _ _ cell b found bf (by simp [typed, bt, storageType])
    have frame := post.foreign oldEntry.address ra ba
    exact ⟨stored, Memory.Arguments.Normalization.represented_frame _ _ view.contents frame,
      fun _ => ⟨cell, frame.trans found, typed, writable, stack⟩⟩

end Compiler.Extraction.ExpressionMap.Table
