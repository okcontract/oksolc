/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKeyMemory
import Compiler.Extraction.ExpressionMapCapacityTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapKeyTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)

/-- Exercise key storage with the original initialized-owner fixture and an
arbitrary valid key/slot. This is not a hash-table insertion certificate. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) (index : Fin 8)
    (key : Key) (arguments : Compiler.ZigAir.Memory.Address)
    (length : key.arguments.length < Compiler.ZigAir.Memory.addressLimit) :
    ∃ prepared after, prepareGrowth .embedded safety 3 1 (MapAllocationTests.host (some 1024)) (owned safety) =
        (.ok (.prepared 8 ⟨5, 0⟩), prepared) ∧
      assignKey 8 5 index.val key arguments prepared = (.ok (), after) ∧
      Facts safety 7 3 sentinel 0 after [] ∧
      (∀ slot, KeyFields.read 8 5 index.val slot after.memory.memory = .ok (KeyFields.value key arguments slot)) ∧
      after.memory.effects.allocator = 597 := by
  obtain ⟨prepared, preparation, facts, ready, _, reached, _⟩ := MapCapacityTests.from_initialized_owner safety meaning
  obtain ⟨cell, found, _, typed, writable, _⟩ := ready.bucketLive
  obtain ⟨after, ran, facts, _, reads, effects⟩ := facts.assign_key 8 5 index.val cell index.isLt found typed writable
    key arguments length (ready.headers .keys)
  exact ⟨prepared, after, preparation, ran, facts, reads, (congrArg Publication.Effects.allocator effects).trans reached⟩

open Compiler.ZigAir.Memory

def sample : Key := ⟨2, 171, 11 * 2^192 + 7 * 2^128 + 5 * 2^64 + 3, [5, 17, 4294967295], 305419896⟩
def arguments : Address := ⟨91, 4⟩

theorem sample_values :
    KeyFields.value sample arguments .kind = .scalar (.int false 32 2) ∧
    KeyFields.value sample arguments .instruction = .scalar (.int false 8 171) ∧
    KeyFields.value sample arguments .data = .scalar (.int false 256 (11 * 2^192 + 7 * 2^128 + 5 * 2^64 + 3)) ∧
    KeyFields.value sample arguments .arguments = .slice (.slice false (.scalar (.int false 32))) ⟨91, 4⟩ 3 ∧
    KeyFields.value sample arguments .sequence = .scalar (.int false 32 305419896) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

def before : Compiler.ZigAir.Memory.State := (Header.run 8 1 BucketStorageTests.fresh).2
def after : Compiler.ZigAir.Memory.State := (KeyFields.assign 8 1 2 sample arguments before).2

theorem assigned : (KeyFields.assign 8 1 2 sample arguments before).1 = .ok () := by decide +kernel

theorem readback (slot : KeyFields.Slot) :
    KeyFields.read 8 1 2 slot after = .ok (KeyFields.value sample arguments slot) := by
  cases slot <;> decide +kernel

theorem const_slice_readback : KeyFields.read 8 1 2 .arguments after =
    .ok (.slice (.slice false (.scalar (.int false 32))) ⟨91, 4⟩ 3) := by
  exact (readback .arguments).trans (congrArg Except.ok sample_values.2.2.2.1)

theorem native_fields_readback :
    KeyFields.read 8 1 2 .kind after = .ok (.scalar (.int false 32 2)) ∧
    KeyFields.read 8 1 2 .instruction after = .ok (.scalar (.int false 8 171)) ∧
    KeyFields.read 8 1 2 .data after = .ok (.scalar (.int false 256 (11 * 2^192 + 7 * 2^128 + 5 * 2^64 + 3))) ∧
    KeyFields.read 8 1 2 .sequence after = .ok (.scalar (.int false 32 305419896)) := by
  exact ⟨(readback .kind).trans (congrArg Except.ok sample_values.1),
    (readback .instruction).trans (congrArg Except.ok sample_values.2.1),
    (readback .data).trans (congrArg Except.ok sample_values.2.2.1),
    (readback .sequence).trans (congrArg Except.ok sample_values.2.2.2.2)⟩

theorem neighbors_uninitialized (slot : KeyFields.Slot) :
    KeyFields.read 8 1 1 slot after = .error .uninitialized ∧
    KeyFields.read 8 1 3 slot after = .error .uninitialized := by
  cases slot <;> decide +kernel

theorem header_retained (slot : Header.Slot) :
    load after (slot.pointer 8 1) = .ok (slot.value 8 1) := by
  cases slot <;> decide +kernel

def readonly : Compiler.ZigAir.Memory.State :=
  { before with heap := before.heap.map (fun entry => (entry.1, { entry.2 with writable := false })) }

theorem readonly_rejected : KeyFields.assign 8 1 2 sample arguments readonly = (.error .readOnly, readonly) := by
  decide +kernel

def rebound : Compiler.ZigAir.Memory.State :=
  (store before (Header.Slot.keys.pointer 8 1) (.pointer (.pointer true true keyType) ⟨1, 544⟩)).toOption.getD before

theorem rebound_header_rejected : KeyFields.assign 8 1 0 sample arguments rebound = (.error .memoryValidity, rebound) := by
  decide +kernel

theorem out_of_bounds_rejected :
    KeyFields.assign 8 1 8 sample arguments before = (.error .memoryValidity, before) := by decide +kernel

theorem missing_header_rejected :
    KeyFields.assign 8 1 0 sample arguments BucketStorageTests.fresh = (.error .uninitialized, BucketStorageTests.fresh) := by
  decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapKeyTests
