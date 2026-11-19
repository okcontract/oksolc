/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapEntryMemory
import Compiler.Extraction.ExpressionMapKeyTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapEntryTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)

/-- The original initialized-owner fixture exercises the entire assignment
pair for arbitrary keys, IDs and in-range slots. Metadata is deliberately still
free: this is the assignment tail, not a getOrPut/insertion certificate. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) (index : Fin 8)
    (key : Key) (arguments : Compiler.ZigAir.Memory.Address) (id : NodeId)
    (length : key.arguments.length < Compiler.ZigAir.Memory.addressLimit) :
    ∃ prepared after, prepareGrowth .embedded safety 3 1 (MapAllocationTests.host (some 1024)) (owned safety) =
        (.ok (.prepared 8 ⟨5, 0⟩), prepared) ∧
      assignEntry 8 5 index.val key arguments id prepared = (.ok (), after) ∧
      Facts safety 7 3 sentinel 0 after [] ∧ Entry.Stored 8 5 index.val key arguments id after.memory.memory ∧
      (∀ slot : Fin 8, Metadata.observe after.memory.memory 5 slot = .ok (true, false)) ∧
      after.memory.effects.allocator = 597 ∧ after.memory.memory.nextId = 6 := by
  obtain ⟨prepared, preparation, facts, ready, cursor, reached, _⟩ := MapCapacityTests.from_initialized_owner safety meaning
  obtain ⟨cell, found, _, typed, writable, _⟩ := ready.bucketLive
  obtain ⟨after, ran, facts, stored, metadata, effects, nextId, _⟩ := facts.assign_entry 8 5 index.val cell index.isLt
    found typed writable key arguments id length ready.headers
  exact ⟨prepared, after, preparation, ran, facts, stored,
    fun slot => (metadata slot slot.isLt).trans (ready.slots slot slot.isLt),
    (congrArg Publication.Effects.allocator effects).trans reached, nextId.trans cursor⟩

open Compiler.ZigAir.Memory
open MapKeyTests (sample arguments before)

def assignedId : BitVec 32 := 4275878552

def after : Compiler.ZigAir.Memory.State := (Entry.assign 8 1 2 sample arguments assignedId before).2

def cell : Compiler.ZigAir.Memory.Allocation := (before.heap.lookup 1).getD ⟨4096, storageType 8, [], true, false⟩

theorem completed : ∃ keyed, Entry.Completed 8 1 2 sample arguments assignedId before keyed after := by
  obtain ⟨keyed, reached, ran, post⟩ := Entry.assign_verified 8 1 2 sample arguments assignedId before cell
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)
    (by intro slot; cases slot <;> decide +kernel)
  have same : reached = after := (congrArg Prod.snd ran).symm
  subst reached
  exact ⟨keyed, post⟩

theorem assigned : (Entry.assign 8 1 2 sample arguments assignedId before).1 = .ok () := by decide +kernel

theorem readback : Entry.Stored 8 1 2 sample arguments assignedId after := by
  obtain ⟨keyed, post⟩ := completed
  exact post.stored cell (by decide) (by decide +kernel) (by decide +kernel)
    (by intro slot; cases slot <;> decide +kernel)

theorem native_value_readback : Values.read after 8 1 2 = .ok (.scalar (.int false 32 4275878552)) :=
  readback.value

theorem const_slice_readback : KeyFields.read 8 1 2 .arguments after =
    .ok (.slice (.slice false (.scalar (.int false 32))) ⟨91, 4⟩ 3) :=
  (readback.keys .arguments).trans (congrArg Except.ok MapKeyTests.sample_values.2.2.2.1)

theorem neighbor_values (other : Nat) (apart : other ≠ 2) :
    load after (Values.pointer 8 1 other) = load before (Values.pointer 8 1 other) := by
  obtain ⟨keyed, post⟩ := completed
  exact post.other_values (by decide) other apart

theorem metadata_retained (slot : Fin 8) : Metadata.observe after 1 slot = Metadata.observe before 1 slot := by
  obtain ⟨keyed, post⟩ := completed
  exact post.metadata_frame slot slot.isLt

theorem header_retained (slot : Header.Slot) : load after (slot.pointer 8 1) = .ok (slot.value 8 1) := by
  obtain ⟨keyed, post⟩ := completed
  exact (post.headers slot).trans (by cases slot <;> decide +kernel)

def redirect (state : Compiler.ZigAir.Memory.State) : Compiler.ZigAir.Memory.State :=
  (store state (Header.Slot.values.pointer 8 1) (.pointer (.pointer true true word) ⟨2, 0⟩)).toOption.getD state

def missingValues : Compiler.ZigAir.Memory.State := redirect before

theorem selection_failure_before_writes : Entry.assign 8 1 2 sample arguments assignedId missingValues =
    (.error .unallocated, missingValues) :=
  Entry.selection_rejected 8 1 2 sample arguments assignedId missingValues
    (.pointer (.pointer true false keyType) ⟨1, 160⟩) .unallocated (by decide +kernel) (by decide +kernel)

def readonlyValues : Compiler.ZigAir.Memory.State := redirect { before with
  heap := (2, ⟨8192, .array 3 word, [(8, number 37)], false, false⟩) :: before.heap,
  nextId := 3, nextAddress := 8204 }

def keyed : Compiler.ZigAir.Memory.State := (KeyFields.assign 8 1 2 sample arguments readonlyValues).2

theorem partial_prefix : Entry.assign 8 1 2 sample arguments assignedId readonlyValues = (.error .readOnly, keyed) :=
  Entry.value_rejected 8 1 2 sample arguments assignedId readonlyValues keyed
    (.pointer (.pointer true false keyType) ⟨1, 160⟩) (.pointer (.pointer true false word) ⟨2, 8⟩) .readOnly
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem partial_key_readback (slot : KeyFields.Slot) :
    KeyFields.read 8 1 2 slot (Entry.assign 8 1 2 sample arguments assignedId readonlyValues).2 =
      .ok (KeyFields.value sample arguments slot) := by
  rw [partial_prefix]
  cases slot <;> decide +kernel

theorem partial_value_retained : Values.read (Entry.assign 8 1 2 sample arguments assignedId readonlyValues).2 8 1 2 =
    .ok (number 37) := by rw [partial_prefix]; decide +kernel

theorem readonly_keys_rejected : Entry.assign 8 1 2 sample arguments assignedId MapKeyTests.readonly =
    (.error .readOnly, MapKeyTests.readonly) := by decide +kernel

theorem out_of_bounds_rejected : Entry.assign 8 1 8 sample arguments assignedId before =
    (.error .memoryValidity, before) := by decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapEntryTests
