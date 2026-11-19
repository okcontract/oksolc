/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphPrivateRegions
import Compiler.Extraction.InternerNativeGraphMapWriteTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.PrivateRegionTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ExpressionMap.Initialization
open ConstructorItem
open NativeRecursion.Tests (program)
open RecursiveBorrowedTests (rows)

attribute [local irreducible] program

/-- Reuse the completed recursive program. Every host outcome preserves all
representative queries and existing ownership, for any admitted or rejected
region type. No final frame or successful allocation is supplied. -/
theorem recursive_reservation (safety : Bool) (depth : Nat) (type : Compiler.ZigAir.Memory.Ty)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator Nat) :
    let before := (program safety (depth + 2)).2
    let after := (PrivateRegion.reserve type allocate before).2
    Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 after (rows safety) ∧
      (∀ id opcode, Operation.run after.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
        Operation.run before.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode) ∧
      (∀ id, Constant.value after.memory.memory (Owner.headerAddress ⟨6, 0⟩) id =
        Constant.value before.memory.memory (Owner.headerAddress ⟨6, 0⟩) id) := by
  intro before after
  have initial := Tests.recursive_after safety depth
  have facts := initial.reserve_private type allocate
  exact ⟨facts, fun id opcode => (facts.operations id opcode).trans (initial.operations id opcode).symm,
    fun id => (facts.constants id).trans (initial.constants id).symm⟩

/-- Map-field stores immediately consume the reservation frame, including its
changed allocation cursor and effects. This composition does not initialize
buckets, link a metadata pointer to them, or establish a valid native map. -/
theorem recursive_fields (safety : Bool) (depth : Nat) (type : Compiler.ZigAir.Memory.Ty)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator Nat)
    (slot : Slot) (value : Compiler.ZigAir.Memory.Value)
    (typed : value.type = slot.value.type) (valid : value.valid = true) (active : slot.Active safety) :
    let after := (PrivateRegion.reserve type allocate (program safety (depth + 2)).2).2
    ∃ memory, writeValue safety after.memory.memory ⟨6, 0⟩ slot value = .ok memory ∧
      WrittenValue safety after.memory.memory memory 6 slot value ∧
      Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
        { after with memory := { after.memory with memory } } (rows safety) := by
  exact (recursive_reservation safety depth type allocate).1.write_map slot value typed valid active

open GraphInit.Ownership.Tests (owned)

-- A generic private region exercises reservation mechanics only. These bytes
-- are not a captured hash-map bucket layout or initialized bucket contents.
def type : Compiler.ZigAir.Memory.Ty := .array 16 (.scalar (.int false 64))

def host (base : Option Nat) : Compiler.ZigAir.Memory.RegionAllocation.Allocator Nat :=
  fun bytes alignment effects => (base, effects + bytes + alignment)

def observed (base : Option Nat) :=
  let (result, after) := PrivateRegion.reserve type (host base) (owned true)
  (result, after.memory.memory.nextId, after.memory.memory.nextAddress, after.memory.effects.allocator,
    after.memory.memory.heap.lookup 4)

theorem successful_region : observed (some 256) =
    (.ok (some ⟨4, 0⟩), 5, 384, 141, some ⟨256, type, [], true, false⟩) := by decide +kernel

theorem failed_region : observed none = (.ok none, 4, 128, 141, none) := by decide +kernel

theorem overlap_rejected : observed (some 56) = (.error .memoryValidity, 4, 128, 141, none) := by decide +kernel

theorem unaligned_rejected : observed (some 257) = (.error .memoryValidity, 4, 128, 141, none) := by decide +kernel

theorem empty_skips_host :
    let after := PrivateRegion.reserve (.array 0 (.scalar (.int false 64))) (host (some 256)) (owned true)
    (after.1, after.2.memory.memory.nextId, after.2.memory.effects.allocator, after.2.memory.memory.heap.lookup 4) =
      (.ok (some ⟨4, 0⟩), 4, 5, none) := by decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.PrivateRegionTests
