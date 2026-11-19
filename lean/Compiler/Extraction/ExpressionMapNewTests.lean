/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapNewMemory
import Compiler.Extraction.ExpressionMapEntryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapNewTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets ExpressionMap
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)

/-- The existing original owner/allocator fixture now consumes preparation and
the entire selected new-slot route, for arbitrary keys, IDs, fingerprints and
slots. Hashing and probe selection are still separate original-input obligations. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) (index : Fin 8) (fp : BitVec 7)
    (key : Key) (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId)
    (length : key.arguments.length < Compiler.ZigAir.Memory.addressLimit) :
    ∃ prepared after, prepareGrowth .embedded safety 3 1 (MapAllocationTests.host (some 1024)) (owned safety) =
        (.ok (.prepared 8 ⟨5, 0⟩), prepared) ∧
      publishNewSlot .localMap safety 4 8 5 index.val fp key arguments id prepared = (.ok (), after) ∧
      Facts safety 7 3 sentinel 0 after [] ∧
      Insertion.Published .localMap safety 4 5 index.val 8 fp 6 0 key arguments id prepared.memory.memory after.memory.memory ∧
      after.memory.effects.allocator = 597 ∧ after.memory.memory.nextId = 6 := by
  obtain ⟨prepared, preparation, facts, ready, cursor, reached, _⟩ := MapCapacityTests.from_initialized_owner safety meaning
  have layout := Insertion.Layout.of_ready ready
  have available : Compiler.ZigAir.Memory.load prepared.memory.memory (Counter.field .localMap safety 4 .available) = .ok (number 6) := by
    simpa only [Counter.field, Initialization.Placement.offset, Nat.zero_add, Local.field] using ready.available
  have size : Compiler.ZigAir.Memory.load prepared.memory.memory (Counter.field .localMap safety 4 .size) = .ok (number 0) := by
    simpa only [Counter.field, Initialization.Placement.offset, Nat.zero_add, Local.field] using ready.size
  obtain ⟨after, ran, facts, post, effects⟩ := facts.publish_new_slot .localMap 4 8 5 index.val (by intro impossible; cases impossible)
    layout fp 6 0 0 index.isLt available size (Metadata.read_byte_free _ 5 index (ready.slots index index.isLt))
    (by decide) (by decide) key arguments id length
  exact ⟨prepared, after, preparation, ran, facts, post,
    (congrArg Publication.Effects.allocator effects).trans reached, (post.cursors id).1.trans cursor⟩

open Compiler.ZigAir.Memory
open MapKeyTests (sample arguments)

def allocated : Compiler.ZigAir.Memory.State :=
  let buckets := (Metadata.fill 1 8 0 MapKeyTests.before).2
  { buckets with
    heap := (2, ⟨8192, ExpressionMap.allocationType true, [], true, false⟩) :: buckets.heap,
    nextId := 3, nextAddress := 8216 }

def initialized : Compiler.ZigAir.Memory.State :=
  let defaults := (Local.writes true 2 (Local.slots true) allocated).2
  let metadata := (Counter.write .localMap true defaults 2 .metadata (Receiver.value 1)).toOption.getD defaults
  (Counter.write .localMap true metadata 2 .available (number 6)).toOption.getD metadata

/-- Seed stale leaves in a free slot to check the actual undefined assignments;
this raw fixture is separate from the original-owner composition above. -/
def before : Compiler.ZigAir.Memory.State := (Entry.assign 8 1 2 sample arguments 37 initialized).2

def prepared : Compiler.ZigAir.Memory.State := (Insertion.prepare .localMap true 2 8 1 2 93 before).2
def after : Compiler.ZigAir.Memory.State := (Insertion.publish .localMap true 2 8 1 2 93 sample arguments MapEntryTests.assignedId before).2

theorem stale_value : Values.read before 8 1 2 = .ok (number 37) := by decide +kernel

theorem prepared_pointers : (Insertion.prepare .localMap true 2 8 1 2 93 before).1 = .ok (Insertion.selected 8 1 2) := by decide +kernel

theorem erased_key : KeyFields.read 8 1 2 .data prepared = .error .uninitialized := by decide +kernel

theorem erased_value : Values.read prepared 8 1 2 = .error .uninitialized := by decide +kernel

theorem prepared_counters : load prepared (Counter.field .localMap true 2 .available) = .ok (number 5) ∧
    load prepared (Counter.field .localMap true 2 .size) = .ok (number 1) := by constructor <;> decide +kernel

theorem prepared_metadata : Metadata.readByte prepared 1 2 = .ok 221 := by decide +kernel

theorem published : (Insertion.publish .localMap true 2 8 1 2 93 sample arguments MapEntryTests.assignedId before).1 = .ok () := by decide +kernel

theorem readback : Entry.Stored 8 1 2 sample arguments MapEntryTests.assignedId after := by
  constructor
  · intro slot; cases slot <;> decide +kernel
  · decide +kernel

theorem final_counters : load after (Counter.field .localMap true 2 .available) = .ok (number 5) ∧
    load after (Counter.field .localMap true 2 .size) = .ok (number 1) := by constructor <;> decide +kernel

theorem final_metadata : Metadata.observe after 1 2 = .ok (false, true) := by decide +kernel

theorem neighbor_metadata : Metadata.readByte after 1 3 = .ok 0 := by decide +kernel

def exhausted : Compiler.ZigAir.Memory.State :=
  (Counter.write .localMap true before 2 .available (number 0)).toOption.getD before

theorem underflow_rejected : Insertion.publish .localMap true 2 8 1 2 93 sample arguments MapEntryTests.assignedId exhausted =
    (.error (.scalar .safetyPanic), exhausted) := by
  have rejected := Counter.adjust_rejected .localMap true 2 .available 0 exhausted (by decide +kernel) (by simp [Counter.Field.Admitted])
  simp only [Insertion.publish, Insertion.prepare, rejected]
  rfl

def readonly : Compiler.ZigAir.Memory.State := { before with heap := (before.heap.replace 1
  ({ (before.heap.lookup 1).getD ⟨4096, storageType 8, [], false, false⟩ with writable := false })) }

def downReadonly : Compiler.ZigAir.Memory.State := (Counter.adjust .localMap true 2 .available readonly).2

theorem metadata_rejection_prefix : Insertion.publish .localMap true 2 8 1 2 93 sample arguments MapEntryTests.assignedId readonly =
    (.error .readOnly, downReadonly) := by
  have down : Counter.adjust .localMap true 2 .available readonly = (.ok (), downReadonly) := by decide +kernel
  have rejected : Metadata.mark 1 2 93 downReadonly = (.error .readOnly, downReadonly) := by decide +kernel
  simp only [Insertion.publish, Insertion.prepare, down, rejected]

theorem rejected_metadata_keeps_decrement : load downReadonly (Counter.field .localMap true 2 .available) = .ok (number 5) ∧
    Metadata.readByte downReadonly 1 2 = .ok 0 := by constructor <;> decide +kernel

def overflow : Compiler.ZigAir.Memory.State :=
  (Counter.write .localMap true before 2 .size (number 4294967295)).toOption.getD before

def overflowPrefix : Compiler.ZigAir.Memory.State :=
  let down := (Counter.adjust .localMap true 2 .available overflow).2
  let marked := (Metadata.mark 1 2 93 down).2
  (Entry.reset (Insertion.selected 8 1 2).keyPointer (Insertion.selected 8 1 2).valuePointer marked).2

theorem size_rejection_prefix : Insertion.publish .localMap true 2 8 1 2 93 sample arguments MapEntryTests.assignedId overflow =
    (.error (.scalar .safetyPanic), overflowPrefix) := by
  let down := (Counter.adjust .localMap true 2 .available overflow).2
  let marked := (Metadata.mark 1 2 93 down).2
  have decreased : Counter.adjust .localMap true 2 .available overflow = (.ok (), down) := by decide +kernel
  have occupied : Metadata.mark 1 2 93 down = (.ok (), marked) := by decide +kernel
  have keys : KeyFields.entryPointer marked 8 1 2 = .ok (Insertion.selected 8 1 2).keyPointer := by decide +kernel
  have values : Values.entryPointer marked 8 1 2 = .ok (Insertion.selected 8 1 2).valuePointer := by decide +kernel
  have reset : Entry.reset (Insertion.selected 8 1 2).keyPointer (Insertion.selected 8 1 2).valuePointer marked =
      (.ok (), overflowPrefix) := by decide +kernel
  have rejected : Counter.adjust .localMap true 2 .size overflowPrefix =
      (.error (.scalar .safetyPanic), overflowPrefix) := by decide +kernel
  simp only [Insertion.publish, Insertion.prepare, decreased, occupied, keys, values, reset, rejected]

theorem rejected_size_keeps_erasure : Values.read overflowPrefix 8 1 2 = .error .uninitialized ∧
    KeyFields.read 8 1 2 .data overflowPrefix = .error .uninitialized ∧ Metadata.readByte overflowPrefix 1 2 = .ok 221 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapNewTests
