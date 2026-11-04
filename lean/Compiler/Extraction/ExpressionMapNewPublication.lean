/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapNewSlot

namespace Compiler.Extraction.ExpressionMap.Insertion
open Compiler.ZigAir.Memory Initialization Buckets
open Compiler.ZigAir.Memory.WordArray (number)
open Compiler.Extraction.Cache (Key)

/-- The selected new-slot route through getOrPutContext and publishOwned.
The first key assignment belongs to getOrPutContext; publication then writes
both key and ID through those same returned pointers. -/
def publish (place : Placement) (safety : Bool) (receiver : Nat) (capacity : BitVec 32)
    (bucket index : Nat) (fp : BitVec 7) (key : Key) (arguments : Address) (id : BitVec 32) (before : State) :
    Except Fault Unit × State :=
  match prepare place safety receiver capacity bucket index fp before with
  | (.error fault, counted) => (.error fault, counted)
  | (.ok entry, counted) =>
    if entry.foundExisting then (.error .unsupported, counted) else
    match KeyFields.writes entry.keyPointer key arguments KeyFields.order counted with
    | (.error fault, installed) => (.error fault, installed)
    | (.ok (), installed) => Entry.writePointers entry.keyPointer entry.valuePointer key arguments id installed

theorem publish_steps (place : Placement) (safety : Bool) (receiver : Nat) (capacity : BitVec 32)
    (bucket index : Nat) (fp : BitVec 7) (key : Key) (arguments : Address) (id : BitVec 32)
    (before counted installed after : State)
    (prepared : prepare place safety receiver capacity bucket index fp before = (.ok (selected capacity bucket index), counted))
    (keyed : KeyFields.writes (selected capacity bucket index).keyPointer key arguments KeyFields.order counted = (.ok (), installed))
    (stored : Entry.writePointers (selected capacity bucket index).keyPointer (selected capacity bucket index).valuePointer
      key arguments id installed = (.ok (), after)) :
    publish place safety receiver capacity bucket index fp key arguments id before = (.ok (), after) := by
  simp only [selected] at keyed stored
  simp only [publish, prepared, selected, Bool.false_eq_true, ↓reduceIte, keyed, stored]

/-- Every native intermediate state is tied to the existing operation proofs.
The logical owned-key table and probing relation are separate obligations. -/
structure Published (place : Placement) (safety : Bool) (receiver bucket index : Nat) (capacity : BitVec 32)
    (fp : BitVec 7) (available size : BitVec 32) (key : Key) (arguments : Address) (id : BitVec 32)
    (before after : State) : Prop where
  stages : ∃ down marked middle erased counted installed keyed,
    Prepared place safety receiver bucket index capacity fp available size before down marked middle erased counted ∧
    KeyFields.Written capacity.toNat bucket index key arguments KeyFields.order counted installed ∧
    Entry.Completed capacity bucket index key arguments id installed keyed after
  layout : Layout place safety receiver bucket capacity after
  stored : Entry.Stored capacity bucket index key arguments id after
  availableRead : load after (Counter.field place safety receiver .available) = .ok (number (available - 1#32))
  sizeRead : load after (Counter.field place safety receiver .size) = .ok (number (size + 1#32))
  metadata : Metadata.observe after bucket index = .ok (false, true)
  availableExact : (available - 1#32).toNat + 1 = available.toNat
  sizeExact : (size + 1#32).toNat = size.toNat + 1

theorem publish_verified (place : Placement) (safety : Bool) (receiver : Nat) (capacity : BitVec 32)
    (bucket index : Nat) (fp : BitVec 7) (before : State) (layout : Layout place safety receiver bucket capacity before)
    (available size : BitVec 32) (bits : BitVec 8) (inside : index < capacity.toNat)
    (availableRead : load before (Counter.field place safety receiver .available) = .ok (number available))
    (sizeRead : load before (Counter.field place safety receiver .size) = .ok (number size))
    (metadataRead : Metadata.readByte before bucket index = .ok bits)
    (room : 0 < available.toNat) (bounded : size.toNat + 1 < 2 ^ 32)
    (key : Key) (arguments : Address) (id : BitVec 32) (length : key.arguments.length < addressLimit) :
    ∃ after, publish place safety receiver capacity bucket index fp key arguments id before = (.ok (), after) ∧
      Published place safety receiver bucket index capacity fp available size key arguments id before after := by
  obtain ⟨down, marked, middle, erased, counted, prepared, preparation⟩ := prepare_verified place safety receiver capacity
    bucket index fp before layout available size bits inside availableRead sizeRead metadataRead room bounded
  obtain ⟨cell, found, typed, writable⟩ := preparation.layout.bucketLive
  obtain ⟨installed, keyRun, keyPost, _⟩ := KeyFields.assign_verified capacity bucket index key arguments counted cell
    inside preparation.layout.valid found typed writable length (preparation.layout.headers .keys)
  have pointer := KeyFields.entry_pointer counted capacity bucket index cell inside preparation.layout.valid found typed
    (preparation.layout.headers .keys)
  have keyed := keyRun
  simp only [KeyFields.assign, pointer] at keyed
  have installedLayout := preparation.layout.bucket_frame keyPost.valid keyPost.shape keyPost.frame
    (keyPost.header capacity.isLt capacity)
  obtain ⟨installedCell, installedFound, installedType, installedWritable⟩ := installedLayout.bucketLive
  obtain ⟨keyedAgain, after, stored, post⟩ := Entry.write_pointers_verified capacity bucket index key arguments id installed
    installedCell inside installedLayout.valid installedFound installedType installedWritable length installedLayout.headers
  refine ⟨after, publish_steps place safety receiver capacity bucket index fp key arguments id before counted installed after
    prepared keyed stored, ⟨down, marked, middle, erased, counted, installed, keyedAgain, preparation, keyPost, post⟩,
    installedLayout.assigned id post, post.stored installedCell inside installedFound installedType installedLayout.headers, ?_, ?_, ?_,
    Counter.next_exact .available available room, Counter.next_exact .size size bounded⟩
  · exact (installedLayout.counter_frame post.native_frame.2.2.1 .available).trans
      ((preparation.layout.counter_frame keyPost.frame .available).trans preparation.availableRead)
  · exact (installedLayout.counter_frame post.native_frame.2.2.1 .size).trans
      ((preparation.layout.counter_frame keyPost.frame .size).trans preparation.sizeRead)
  · have geometry := Buckets.geometry capacity.toNat capacity.isLt
    have apart : KeyFields.Outside capacity.toNat index Metadata.byte (24 + index) := by
      simp only [KeyFields.Outside, Metadata.byte, Ty.readOffsets, List.mem_singleton]
      intro position same
      subst position
      left
      omega
    have retained := keyPost.outside true false Metadata.byte (24 + index) apart
    have read : load installed (Metadata.pointer bucket index) = .ok (Metadata.value (Metadata.occupied fp)) :=
      retained.trans preparation.metadataRead
    rw [post.metadata_frame index inside]
    simp only [Metadata.observe, read, Metadata.value, bind, Except.bind, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, (Metadata.packed_exact 0 fp).2.2.2.1, (Metadata.packed_exact 0 fp).2.2.2.2]

theorem Published.cursors (id : BitVec 32)
    (post : Published place safety receiver bucket index capacity fp available size key arguments id before after) :
    after.nextId = before.nextId ∧ after.nextAddress = before.nextAddress := by
  obtain ⟨down, marked, middle, erased, counted, installed, keyed, preparation, keys, pair⟩ := post.stages
  have a := preparation.availableStore.native_frame
  have b := preparation.occupied.nextId
  have c := preparation.occupied.nextAddress
  have d := preparation.reset.native_frame
  have e := preparation.sizeStore.native_frame
  have f := keys.nextId
  have g := keys.nextAddress
  have h := pair.native_frame
  constructor <;> omega

end Compiler.Extraction.ExpressionMap.Insertion
