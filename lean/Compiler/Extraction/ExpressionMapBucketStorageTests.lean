/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketHeaderReservation
import Compiler.Extraction.ExpressionMapBucketReservationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.BucketStorageTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open ConstructorItem
open NativeRecursion.Tests (program)
open RecursiveBorrowedTests (rows)

attribute [local irreducible] program

theorem recursive_header (safety : Bool) (depth : Nat) (capacity : BitVec 32)
    (positive : 0 < capacity.toNat) (base : Nat)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator Nat) (effects : Nat)
    (response : allocate (sourceRequest capacity).toNat 16 (program safety (depth + 2)).2.memory.effects.allocator = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits (program safety (depth + 2)).2.memory.memory
      ⟨bytes capacity.toNat, 16⟩ base) :
    let before := (program safety (depth + 2)).2
    ∃ after, reserveHeader capacity allocate before = (.ok (some ⟨before.memory.memory.nextId, 0⟩), after) ∧
      Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 after (rows safety) ∧
      (∀ slot : Header.Slot, Compiler.ZigAir.Memory.load after.memory.memory
        (slot.pointer capacity before.memory.memory.nextId) = .ok (slot.value capacity before.memory.memory.nextId)) ∧
      (∀ id opcode, Operation.run after.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
        Operation.run before.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode) ∧
      (∀ id, Constant.value after.memory.memory (Owner.headerAddress ⟨6, 0⟩) id =
        Constant.value before.memory.memory (Owner.headerAddress ⟨6, 0⟩) id) := by
  have initial := Tests.recursive_after safety depth
  obtain ⟨after, ran, facts, reads, _⟩ := initial.reserve_header capacity positive base allocate effects response fits
  exact ⟨after, ran, facts, reads,
    fun id opcode => (facts.operations id opcode).trans (initial.operations id opcode).symm,
    fun id => (facts.constants id).trans (initial.constants id).symm⟩

open Compiler.ZigAir.Memory

def fresh : Compiler.ZigAir.Memory.State := ⟨[(1, ⟨4096, storageType 8, [], true, false⟩)], 2, 4672⟩

theorem uninitialized_header :
    load fresh (Header.Slot.capacity.pointer 8 1) = .error .uninitialized := by decide +kernel

theorem initialized_header : ∃ after, Header.run 8 1 fresh = (.ok (), after) ∧
    ∀ slot : Header.Slot, load after (slot.pointer 8 1) = .ok (slot.value 8 1) := by
  obtain ⟨after, ran, _, _, reads, _⟩ := Header.run_verified fresh 1 _ 8 (by decide)
    (by decide +kernel) (by rfl) rfl rfl
  exact ⟨after, ran, reads⟩

theorem captured_header_values :
    load (Header.run 8 1 fresh).2 (Header.Slot.values.pointer 8 1) =
      .ok (.pointer (.pointer true true (.scalar (.int false 32))) ⟨1, 544⟩) ∧
    load (Header.run 8 1 fresh).2 (Header.Slot.keys.pointer 8 1) =
      .ok (.pointer (.pointer true true keyType) ⟨1, 32⟩) ∧
    load (Header.run 8 1 fresh).2 (Header.Slot.capacity.pointer 8 1) = .ok (.scalar (.int false 32 8)) := by
  decide +kernel

def wrongCapacity : Compiler.ZigAir.Memory.State := ⟨[(1, ⟨4096,
  .aggregate "invalid-buckets" ⟨576, 16⟩ [(0, .object (.aggregate "invalid-header" ⟨24, 8⟩
    [(0, .object (.pointer true true (.scalar (.int false 32)))),
     (8, .object (.pointer true true keyType)), (16, .scalar (.int false 16))])),
    (24, .object (.array 8 ExpressionMap.Buckets.metadataType)),
    (32, .object (.array 8 keyType)), (544, .object (.array 8 (.scalar (.int false 32))))],
  [], true, false⟩)], 2, 4672⟩

theorem rejected_capacity_retains_writes :
    (Header.run 8 1 wrongCapacity).1 = .error .unsupported ∧
    load (Header.run 8 1 wrongCapacity).2 (Header.Slot.values.pointer 8 1) = .ok (Header.Slot.values.value 8 1) ∧
    load (Header.run 8 1 wrongCapacity).2 (Header.Slot.keys.pointer 8 1) = .ok (Header.Slot.keys.value 8 1) := by
  decide +kernel

theorem zero_capacity_not_admitted : (storageType 0).layout = none := by decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.BucketStorageTests
