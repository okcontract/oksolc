/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapNewMemory

namespace Compiler.Extraction.ExpressionMap.Insertion
open Compiler.ZigAir.Memory Initialization Buckets
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

variable {place : Placement} {safety : Bool} {receiver bucket index : Nat} {capacity : BitVec 32}
  {fp : BitVec 7} {available size : BitVec 32} {key : Key} {arguments : Address} {id : BitVec 32} {before after : State}

/-- Compose the actual selected-slot effects once. Reads outside its metadata,
key and value footprints survive even if they originally rejected. -/
theorem Published.outside (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (layout : Layout place safety receiver bucket capacity before) (writable many : Bool) (child : Ty) (offset : Nat)
    (metadataApart : ∀ p ∈ child.readOffsets offset, p ≠ 24 + index)
    (keyApart : KeyFields.Outside capacity.toNat index child offset)
    (valueApart : ∀ p ∈ child.readOffsets offset,
      p < valuesOffset capacity.toNat + index * 4 ∨ valuesOffset capacity.toNat + index * 4 + 4 ≤ p) :
    load after (.pointer (.pointer writable many child) ⟨bucket, offset⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, offset⟩) := by
  obtain ⟨down, marked, middle, erased, counted, installed, keyed, prepared, firstKey, pair⟩ := post.stages
  have downLayout := layout.counter .available _ prepared.availableStore (by decide)
  have markedLayout := downLayout.marked prepared.occupied
  have erasedLayout := markedLayout.reset prepared.reset
  exact (pair.outside writable many child offset keyApart (by
    intro p member; have := valueApart p member; omega)).trans
    ((firstKey.outside writable many child offset keyApart).trans
    ((erasedLayout.bucket_read_frame prepared.sizeStore.native_frame.2.2.1 writable many child offset).trans
    ((prepared.reset.outside writable many child offset keyApart valueApart).trans
    ((prepared.occupied.outside writable many child offset metadataApart).trans
      (layout.bucket_read_frame prepared.availableStore.native_frame.2.2.1 writable many child offset)))))

theorem Published.foreign (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (other : Nat) (receiverApart : other ≠ receiver) (bucketApart : other ≠ bucket) :
    after.heap.lookup other = before.heap.lookup other := by
  obtain ⟨down, marked, middle, erased, counted, installed, keyed, prepared, firstKey, pair⟩ := post.stages
  exact (pair.native_frame.2.2.1 other bucketApart).trans ((firstKey.frame other bucketApart).trans
    ((prepared.sizeStore.native_frame.2.2.1 other receiverApart).trans
    ((prepared.reset.native_frame.2.2.1 other bucketApart).trans
    ((prepared.occupied.frame other bucketApart).trans
      (prepared.availableStore.native_frame.2.2.1 other receiverApart)))))

theorem Published.metadata_other (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (layout : Layout place safety receiver bucket capacity before) (other : Nat)
    (inside : other < capacity.toNat) (apart : other ≠ index) :
    Metadata.readByte after bucket other = Metadata.readByte before bucket other := by
  apply Metadata.read_byte_frame
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  apply post.outside layout true false Metadata.byte (24 + other)
  all_goals simp only [KeyFields.Outside, Metadata.byte, Ty.readOffsets, List.mem_singleton]
  all_goals intro p same; subst p; omega

/-- The old and new native selectors consume their own actual headers. The
frame covers all fields of another entry, including both slice leaves. -/
theorem Published.stored_other (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (layout : Layout place safety receiver bucket capacity before) (inside : index < capacity.toNat)
    (other : Nat) (otherInside : other < capacity.toNat) (apart : other ≠ index)
    (oldKey : Key) (oldArguments : Address) (oldId : BitVec 32)
    (stored : Entry.Stored capacity bucket other oldKey oldArguments oldId before) :
    Entry.Stored capacity bucket other oldKey oldArguments oldId after := by
  obtain ⟨cell, found, typed, _⟩ := layout.bucketLive
  obtain ⟨finalCell, finalFound, finalType, _⟩ := post.layout.bucketLive
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  constructor
  · intro slot
    rw [KeyFields.read_eq capacity bucket other slot after finalCell oldKey oldArguments otherInside post.layout.valid
      finalFound finalType (post.layout.headers .keys)]
    have old := stored.keys slot
    rw [KeyFields.read_eq capacity bucket other slot before cell oldKey oldArguments otherInside layout.valid
      found typed (layout.headers .keys)] at old
    apply Eq.trans _ old
    apply post.outside layout true false (KeyFields.value oldKey oldArguments slot).type
      (keysOffset capacity.toNat + other * 64 + KeyFields.offset slot)
    all_goals cases slot <;> simp [KeyFields.Outside, KeyFields.value, KeyFields.offset, Value.type,
      Compiler.ZigAir.Scalar.Value.type, Ty.readOffsets] <;> omega
  · rw [Values.read_eq after capacity bucket other finalCell otherInside post.layout.valid finalFound finalType (post.layout.headers .values)]
    have old := stored.value
    rw [Values.read_eq before capacity bucket other cell otherInside layout.valid found typed (layout.headers .values)] at old
    apply Eq.trans _ old
    apply post.outside layout true false word (valuesOffset capacity.toNat + other * 4)
    all_goals simp only [KeyFields.Outside, Ty.readOffsets, List.mem_singleton]
    all_goals intro p same; subst p; omega

end Compiler.Extraction.ExpressionMap.Insertion
