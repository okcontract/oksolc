/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCounter
import Compiler.Extraction.ExpressionMapMetadataWrite
import Compiler.Extraction.ExpressionMapEntryReset

namespace Compiler.Extraction.ExpressionMap.Insertion
open Compiler.ZigAir.Memory Initialization Buckets RepresentativeArray

/-- Original native storage admission. The receiver's actual metadata pointer
and all private header reads bind the bucket; no selected entry pointer, store
success or logical table transition is assumed. -/
structure Layout (place : Placement) (safety : Bool) (receiver bucket : Nat) (capacity : BitVec 32) (state : State) : Prop where
  valid : state.valid = true
  receiverLive : ∃ cell, state.heap.lookup receiver = some cell ∧ cell.type = place.type safety ∧ cell.writable = true
  bucketLive : ∃ cell, state.heap.lookup bucket = some cell ∧ cell.type = storageType capacity.toNat ∧ cell.writable = true
  metadata : load state (Counter.field place safety receiver .metadata) = .ok (Receiver.value bucket)
  headers : ∀ slot : Header.Slot, load state (slot.pointer capacity bucket) = .ok (slot.value capacity bucket)

variable {place : Placement} {safety : Bool} {receiver bucket : Nat} {capacity : BitVec 32} {before after : State}

theorem Layout.apart (layout : Layout place safety receiver bucket capacity before) : bucket ≠ receiver := by
  obtain ⟨r, rf, rt, _⟩ := layout.receiverLive
  obtain ⟨b, bf, bt, _⟩ := layout.bucketLive
  apply before.heap.lookup_ne_of_type_ne bucket receiver b r bf rf
  cases place <;> simp [bt, rt, Placement.type, storageType, Owner.viewType, allocationType]

theorem Layout.counter (layout : Layout place safety receiver bucket capacity before) (slot : Slot) (value : Value)
    (post : Counter.Stored place safety receiver slot value before after) (apart : Slot.metadata ≠ slot) :
    Layout place safety receiver bucket capacity after := by
  have frame := post.native_frame
  obtain ⟨r, rf, rt, rw⟩ := layout.receiverLive
  obtain ⟨r', rf', shape⟩ := frame.2.1 receiver r rf
  obtain ⟨b, bf, bt, bw⟩ := layout.bucketLive
  have kept := frame.2.2.1 bucket layout.apart
  refine ⟨frame.1, ⟨r', rf', shape.2.1.trans rt, shape.2.2.1.trans rw⟩,
    ⟨b, kept.trans bf, bt, bw⟩, (post.others .metadata apart).trans layout.metadata, ?_⟩
  intro header
  exact (load_eq_of_lookup before after true false (header.value capacity bucket).type
    ⟨bucket, header.offset⟩ kept).trans (layout.headers header)

theorem Layout.bucket_frame (layout : Layout place safety receiver bucket capacity before)
    (valid : after.valid = true) (shape : before.heap.RetainsShape after.heap)
    (frame : ∀ other, other ≠ bucket → after.heap.lookup other = before.heap.lookup other)
    (headers : ∀ slot : Header.Slot, load after (slot.pointer capacity bucket) = load before (slot.pointer capacity bucket)) :
    Layout place safety receiver bucket capacity after := by
  obtain ⟨r, rf, rt, rw⟩ := layout.receiverLive
  obtain ⟨b, bf, bt, bw⟩ := layout.bucketLive
  obtain ⟨b', bf', bs⟩ := shape bucket b bf
  have kept := frame receiver (Ne.symm layout.apart)
  exact ⟨valid, ⟨r, kept.trans rf, rt, rw⟩, ⟨b', bf', bs.2.1.trans bt, bs.2.2.1.trans bw⟩,
    (load_eq_of_lookup before after true false Slot.metadata.value.type
      ⟨receiver, place.offset safety + Slot.metadata.offset safety⟩ kept).trans layout.metadata,
    fun slot => (headers slot).trans (layout.headers slot)⟩

theorem Layout.marked (layout : Layout place safety receiver bucket capacity before)
    (post : Metadata.Marked bucket index fp before after) : Layout place safety receiver bucket capacity after :=
  layout.bucket_frame post.valid post.shape post.frame (post.headers capacity)

theorem Layout.reset (layout : Layout place safety receiver bucket capacity before)
    (post : Entry.Reset capacity bucket index before middle after) : Layout place safety receiver bucket capacity after :=
  layout.bucket_frame post.native_frame.1 post.native_frame.2.1 post.native_frame.2.2.1 post.headers

theorem Layout.assigned (layout : Layout place safety receiver bucket capacity before)
    (id : BitVec 32) (post : Entry.Completed capacity bucket index key arguments id before keyed after) : Layout place safety receiver bucket capacity after :=
  layout.bucket_frame post.native_frame.1 post.native_frame.2.1 post.native_frame.2.2.1 post.headers

/-- Foreign allocation frames preserve the original map counters across every
bucket mutation, even when the bucket's initialized leaves change. -/
theorem Layout.counter_frame (layout : Layout place safety receiver bucket capacity before)
    (frame : ∀ other, other ≠ bucket → after.heap.lookup other = before.heap.lookup other) (slot : Slot) :
    load after (Counter.field place safety receiver slot) = load before (Counter.field place safety receiver slot) :=
  load_eq_of_lookup before after true false slot.value.type
    ⟨receiver, place.offset safety + slot.offset safety⟩ (frame receiver (Ne.symm layout.apart))

theorem Layout.bucket_read_frame (layout : Layout place safety receiver bucket capacity before)
    (frame : ∀ other, other ≠ receiver → after.heap.lookup other = before.heap.lookup other)
    (writable many : Bool) (child : Ty) (offset : Nat) :
    load after (.pointer (.pointer writable many child) ⟨bucket, offset⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, offset⟩) :=
  load_eq_of_lookup before after writable many child ⟨bucket, offset⟩ (frame bucket layout.apart)

/-- The existing complete initialization supplies the original storage input;
no receiver, initialized header or metadata pointer is added to its fixture. -/
theorem Layout.of_ready (ready : Local.EmptyReady safety receiver bucket capacity base before) :
    Layout .localMap safety receiver bucket capacity before := by
  obtain ⟨cell, found, typed, writable⟩ := ready.receiverLive
  obtain ⟨backing, located, _, shaped, permitted, _⟩ := ready.bucketLive
  have selected := Receiver.root_pointer safety before receiver cell false ready.valid found typed
  have metadata := ready.metadata
  simp only [Receiver.read, selected, bind, Except.bind] at metadata
  exact ⟨ready.valid, ⟨cell, found, typed, writable⟩, ⟨backing, located, shaped, permitted⟩,
    by simpa only [Counter.field, Placement.offset, Nat.zero_add, Slot.offset, Slot.value, Compiler.ZigAir.Memory.load] using metadata,
    ready.headers⟩

end Compiler.Extraction.ExpressionMap.Insertion
