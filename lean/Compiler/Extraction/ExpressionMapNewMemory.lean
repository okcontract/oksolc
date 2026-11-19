/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapNewPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open ExpressionMap

/-- Counter stores reuse the existing embedded-owner and standalone-map frames.
The receiver identity is explicit for the embedded placement. -/
theorem Facts.counter_stored {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : ExpressionMap.Initialization.Placement) (receiver : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
    (found : before.memory.memory.heap.lookup receiver = some cell) (typed : cell.type = place.type safety)
    (embedded : place = .embedded → receiver = owner)
    (slot : ExpressionMap.Initialization.Slot) (value : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (post : Counter.Stored place safety receiver slot value before.memory.memory memory) :
    Facts safety allocator owner data capacity { before with memory := { before.memory with memory } } rows := by
  have frame := post.native_frame
  cases place with
  | embedded =>
    have same := embedded rfl
    subst receiver
    exact facts.map_frame memory ⟨frame.1, frame.2.1, post.header cell found typed,
      frame.2.2.2.1, frame.2.2.2.2, frame.2.2.1⟩
  | localMap => exact facts.local_map_frame receiver cell found typed memory frame.1 frame.2.1 frame.2.2.1

/-- Transport every actual intermediate memory through the existing native
facts. No post-state query relation or unchanged typed-memory premise is supplied. -/
theorem Facts.new_publication_frame {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : ExpressionMap.Initialization.Placement) (receiver bucket index : Nat) (bucketCapacity : BitVec 32)
    (embedded : place = .embedded → receiver = owner)
    (layout : Insertion.Layout place safety receiver bucket bucketCapacity before.memory.memory)
    (fp : BitVec 7) (available size : BitVec 32) (key : Key) (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId)
    (memory : Compiler.ZigAir.Memory.State)
    (post : Insertion.Published place safety receiver bucket index bucketCapacity fp available size key arguments id before.memory.memory memory) :
    Facts safety allocator owner data capacity { before with memory := { before.memory with memory } } rows := by
  obtain ⟨down, marked, middle, erased, counted, installed, keyed, preparation, keyPost, pair⟩ := post.stages
  obtain ⟨receiverCell, receiverFound, receiverType, _⟩ := layout.receiverLive
  have downFacts := facts.counter_stored place receiver receiverCell receiverFound receiverType embedded .available _ down preparation.availableStore
  have downLayout := layout.counter .available _ preparation.availableStore (by decide)
  obtain ⟨bucketCell, bucketFound, bucketType, _⟩ := downLayout.bucketLive
  have markedFacts := downFacts.private_map_frame (.buckets bucketCapacity.toNat) bucket bucketCell bucketFound bucketType marked
    preparation.occupied.valid preparation.occupied.shape preparation.occupied.frame
  have markedLayout := downLayout.marked preparation.occupied
  obtain ⟨markedCell, markedFound, markedType, _⟩ := markedLayout.bucketLive
  have resetFrame := preparation.reset.native_frame
  have erasedFacts := markedFacts.private_map_frame (.buckets bucketCapacity.toNat) bucket markedCell markedFound markedType erased
    resetFrame.1 resetFrame.2.1 resetFrame.2.2.1
  have erasedLayout := markedLayout.reset preparation.reset
  obtain ⟨erasedCell, erasedFound, erasedType, _⟩ := erasedLayout.receiverLive
  have countedFacts := erasedFacts.counter_stored place receiver erasedCell erasedFound erasedType embedded .size _ counted preparation.sizeStore
  obtain ⟨countedCell, countedFound, countedType, _⟩ := preparation.layout.bucketLive
  have installedFacts := countedFacts.private_map_frame (.buckets bucketCapacity.toNat) bucket countedCell countedFound countedType installed
    keyPost.valid keyPost.shape keyPost.frame
  obtain ⟨installedCell, installedFound, shape⟩ := keyPost.shape bucket countedCell countedFound
  have finalFrame := pair.native_frame
  exact installedFacts.private_map_frame (.buckets bucketCapacity.toNat) bucket installedCell installedFound
    (shape.2.1.trans countedType) memory finalFrame.1 finalFrame.2.1 finalFrame.2.2.1

def publishNewSlot (place : ExpressionMap.Initialization.Placement) (safety : Bool) (receiver : Nat)
    (bucketCapacity : BitVec 32) (bucket index : Nat) (fp : BitVec 7) (key : Key)
    (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId) (before : World (Publication.Effects σ)) :
    Except Compiler.ZigAir.Memory.Fault Unit × World (Publication.Effects σ) :=
  let (result, memory) := Insertion.publish place safety receiver bucketCapacity bucket index fp key arguments id before.memory.memory
  (result, { before with memory := { before.memory with memory } })

theorem publishNewSlot_prefix (place : ExpressionMap.Initialization.Placement) (safety : Bool) (receiver : Nat)
    (bucketCapacity : BitVec 32) (bucket index : Nat) (fp : BitVec 7) (key : Key)
    (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId) (before : World (Publication.Effects σ))
    (result : Except Compiler.ZigAir.Memory.Fault Unit) (memory : Compiler.ZigAir.Memory.State)
    (ran : Insertion.publish place safety receiver bucketCapacity bucket index fp key arguments id before.memory.memory = (result, memory)) :
    publishNewSlot place safety receiver bucketCapacity bucket index fp key arguments id before =
      (result, { before with memory := { before.memory with memory } }) := by simp only [publishNewSlot, ran]

theorem Facts.publish_new_slot {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : ExpressionMap.Initialization.Placement) (receiver : Nat) (bucketCapacity : BitVec 32) (bucket index : Nat)
    (embedded : place = .embedded → receiver = owner)
    (layout : Insertion.Layout place safety receiver bucket bucketCapacity before.memory.memory)
    (fp : BitVec 7) (available size : BitVec 32) (bits : BitVec 8) (inside : index < bucketCapacity.toNat)
    (availableRead : Compiler.ZigAir.Memory.load before.memory.memory (Counter.field place safety receiver .available) = .ok (number available))
    (sizeRead : Compiler.ZigAir.Memory.load before.memory.memory (Counter.field place safety receiver .size) = .ok (number size))
    (metadataRead : Metadata.readByte before.memory.memory bucket index = .ok bits)
    (room : 0 < available.toNat) (bounded : size.toNat + 1 < 2 ^ 32)
    (key : Key) (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId) (length : key.arguments.length < Compiler.ZigAir.Memory.addressLimit) :
    ∃ after, publishNewSlot place safety receiver bucketCapacity bucket index fp key arguments id before = (.ok (), after) ∧
      Facts safety allocator owner data capacity after rows ∧
      Insertion.Published place safety receiver bucket index bucketCapacity fp available size key arguments id before.memory.memory after.memory.memory ∧
      after.memory.effects = before.memory.effects := by
  obtain ⟨memory, ran, post⟩ := Insertion.publish_verified place safety receiver bucketCapacity bucket index fp before.memory.memory layout
    available size bits inside availableRead sizeRead metadataRead room bounded key arguments id length
  exact ⟨{ before with memory := { before.memory with memory } },
    publishNewSlot_prefix place safety receiver bucketCapacity bucket index fp key arguments id before (.ok ()) memory ran,
    facts.new_publication_frame place receiver bucket index bucketCapacity embedded layout fp available size key arguments id memory post, post, rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
