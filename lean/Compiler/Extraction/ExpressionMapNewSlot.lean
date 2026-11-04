/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapInsertionLayout

namespace Compiler.Extraction.ExpressionMap.Insertion
open Compiler.ZigAir.Memory Initialization Buckets
open Compiler.ZigAir.Memory.WordArray (number)

structure Result where
  keyPointer : Value
  valuePointer : Value
  foundExisting : Bool
  deriving DecidableEq

def selected (capacity : BitVec 32) (bucket index : Nat) : Result :=
  ⟨.pointer (.pointer true false keyType) (KeyFields.address capacity.toNat bucket index),
    Values.pointer capacity.toNat bucket index, false⟩

/-- Complete new-slot suffix of getOrPutAssumeCapacityAdapted, after probing
has selected its index. Keep all native stores, both undefined assignments and
the two returned pointers in their original order. -/
def prepare (place : Placement) (safety : Bool) (receiver : Nat) (capacity : BitVec 32)
    (bucket index : Nat) (fp : BitVec 7) (before : State) : Except Fault Result × State :=
  match Counter.adjust place safety receiver .available before with
  | (.error fault, down) => (.error fault, down)
  | (.ok (), down) => match Metadata.mark bucket index fp down with
    | (.error fault, marked) => (.error fault, marked)
    | (.ok (), marked) => match KeyFields.entryPointer marked capacity bucket index with
      | .error fault => (.error fault, marked)
      | .ok keyPointer => match Values.entryPointer marked capacity bucket index with
        | .error fault => (.error fault, marked)
        | .ok valuePointer => match Entry.reset keyPointer valuePointer marked with
          | (.error fault, erased) => (.error fault, erased)
          | (.ok (), erased) => match Counter.adjust place safety receiver .size erased with
            | (.error fault, counted) => (.error fault, counted)
            | (.ok (), counted) => (.ok ⟨keyPointer, valuePointer, false⟩, counted)

theorem prepare_steps (place : Placement) (safety : Bool) (receiver : Nat) (capacity : BitVec 32)
    (bucket index : Nat) (fp : BitVec 7) (before down marked erased counted : State) (keyPointer valuePointer : Value)
    (available : Counter.adjust place safety receiver .available before = (.ok (), down))
    (metadata : Metadata.mark bucket index fp down = (.ok (), marked))
    (keys : KeyFields.entryPointer marked capacity bucket index = .ok keyPointer)
    (values : Values.entryPointer marked capacity bucket index = .ok valuePointer)
    (reset : Entry.reset keyPointer valuePointer marked = (.ok (), erased))
    (size : Counter.adjust place safety receiver .size erased = (.ok (), counted)) :
    prepare place safety receiver capacity bucket index fp before = (.ok ⟨keyPointer, valuePointer, false⟩, counted) := by
  simp only [prepare, available, metadata, keys, values, reset, size]

structure Prepared (place : Placement) (safety : Bool) (receiver bucket index : Nat) (capacity : BitVec 32)
    (fp : BitVec 7) (available size : BitVec 32) (before down marked middle erased after : State) : Prop where
  availableStore : Counter.Stored place safety receiver .available (number (available - 1#32)) before down
  occupied : Metadata.Marked bucket index fp down marked
  reset : Entry.Reset capacity bucket index marked middle erased
  sizeStore : Counter.Stored place safety receiver .size (number (size + 1#32)) erased after
  layout : Layout place safety receiver bucket capacity after
  availableRead : load after (Counter.field place safety receiver .available) = .ok (number (available - 1#32))
  sizeRead : load after (Counter.field place safety receiver .size) = .ok (number (size + 1#32))
  metadataRead : load after (Metadata.pointer bucket index) = .ok (Metadata.value (Metadata.occupied fp))

theorem prepare_verified (place : Placement) (safety : Bool) (receiver : Nat) (capacity : BitVec 32)
    (bucket index : Nat) (fp : BitVec 7) (before : State) (layout : Layout place safety receiver bucket capacity before)
    (available size : BitVec 32) (bits : BitVec 8) (inside : index < capacity.toNat)
    (availableRead : load before (Counter.field place safety receiver .available) = .ok (number available))
    (sizeRead : load before (Counter.field place safety receiver .size) = .ok (number size))
    (metadataRead : Metadata.readByte before bucket index = .ok bits)
    (room : 0 < available.toNat) (bounded : size.toNat + 1 < 2 ^ 32) :
    ∃ down marked middle erased after,
      prepare place safety receiver capacity bucket index fp before = (.ok (selected capacity bucket index), after) ∧
      Prepared place safety receiver bucket index capacity fp available size before down marked middle erased after := by
  obtain ⟨receiverCell, receiverFound, receiverType, receiverWritable⟩ := layout.receiverLive
  obtain ⟨down, decremented, downPost⟩ := Counter.adjust_verified place safety receiver .available available before receiverCell
    layout.valid receiverFound receiverType receiverWritable availableRead room
  have downLayout := layout.counter .available _ downPost (by decide)
  obtain ⟨bucketCell, bucketFound, bucketType, bucketWritable⟩ := downLayout.bucketLive
  have oldMetadata := (Metadata.read_byte_frame before down bucket index
    (layout.bucket_read_frame downPost.native_frame.2.2.1 true false Metadata.byte (24 + index))).trans metadataRead
  obtain ⟨marked, filled, markPost⟩ := Metadata.mark_verified capacity bucket index fp down bucketCell bits inside
    downLayout.valid bucketFound bucketType bucketWritable oldMetadata
  have markedLayout := downLayout.marked markPost
  obtain ⟨markedCell, markedFound, markedType, markedWritable⟩ := markedLayout.bucketLive
  have keyPointer := KeyFields.entry_pointer marked capacity bucket index markedCell inside markedLayout.valid
    markedFound markedType (markedLayout.headers .keys)
  have valuePointer := Values.entry_pointer marked capacity bucket index markedCell inside markedLayout.valid
    markedFound markedType (markedLayout.headers .values)
  obtain ⟨middle, erased, reset, resetPost⟩ := Entry.reset_verified capacity bucket index marked markedCell inside
    markedLayout.valid markedFound markedType markedWritable
  have erasedLayout := markedLayout.reset resetPost
  have readSize := (markedLayout.counter_frame resetPost.native_frame.2.2.1 .size).trans
    ((downLayout.counter_frame markPost.frame .size).trans ((downPost.others .size (by decide)).trans sizeRead))
  obtain ⟨erasedCell, erasedFound, erasedType, erasedWritable⟩ := erasedLayout.receiverLive
  obtain ⟨after, incremented, upPost⟩ := Counter.adjust_verified place safety receiver .size size erased erasedCell
    erasedLayout.valid erasedFound erasedType erasedWritable readSize bounded
  refine ⟨down, marked, middle, erased, after,
    prepare_steps place safety receiver capacity bucket index fp before down marked erased after _ _
      decremented filled keyPointer valuePointer reset incremented,
    downPost, markPost, resetPost, upPost, erasedLayout.counter .size _ upPost (by decide), ?_, upPost.read, ?_⟩
  · exact (upPost.others .available (by decide)).trans ((markedLayout.counter_frame resetPost.native_frame.2.2.1 .available).trans
      ((downLayout.counter_frame markPost.frame .available).trans downPost.read))
  · exact (erasedLayout.bucket_read_frame upPost.native_frame.2.2.1 true false Metadata.byte (24 + index)).trans
      ((resetPost.metadata index inside).trans markPost.read)

end Compiler.Extraction.ExpressionMap.Insertion
