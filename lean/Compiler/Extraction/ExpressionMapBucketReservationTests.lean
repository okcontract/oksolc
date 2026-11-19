/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketReservation
import Compiler.Extraction.InternerNativeGraphPrivateRegionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.BucketReservationTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem
open NativeRecursion.Tests (program)
open RecursiveBorrowedTests (rows)

attribute [local irreducible] program

/-- The captured allocation recipe instantiates the general reservation proof
on the completed recursive graph, for all u32 capacities and allocator outcomes. -/
theorem recursive_reservation (safety : Bool) (depth : Nat) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator Nat) :
    let before := (program safety (depth + 2)).2
    let after := (reserveBuckets capacity allocate before).2
    Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 after (rows safety) ∧
      (∀ id opcode, Operation.run after.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
        Operation.run before.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode) ∧
      (∀ id, Constant.value after.memory.memory (Owner.headerAddress ⟨6, 0⟩) id =
        Constant.value before.memory.memory (Owner.headerAddress ⟨6, 0⟩) id) :=
  PrivateRegionTests.recursive_reservation safety depth (ExpressionMap.Buckets.allocationType capacity.toNat) allocate

/-- Published field values still require their own type/validity guards. This
does not assert a header or bucket has been initialized by reservation. -/
theorem recursive_fields (safety : Bool) (depth : Nat) (capacity : BitVec 32)
    (allocate : Compiler.ZigAir.Memory.RegionAllocation.Allocator Nat)
    (slot : ExpressionMap.Initialization.Slot) (value : Compiler.ZigAir.Memory.Value)
    (typed : value.type = slot.value.type) (valid : value.valid = true) (active : slot.Active safety) :
    let after := (reserveBuckets capacity allocate (program safety (depth + 2)).2).2
    ∃ memory, ExpressionMap.Initialization.writeValue safety after.memory.memory ⟨6, 0⟩ slot value = .ok memory ∧
      ExpressionMap.Initialization.WrittenValue safety after.memory.memory memory 6 slot value ∧
      Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
        { after with memory := { after.memory with memory } } (rows safety) :=
  PrivateRegionTests.recursive_fields safety depth (ExpressionMap.Buckets.allocationType capacity.toNat) allocate slot value typed valid active

theorem captured_requests :
    ([8, 16, 32, 128].map ExpressionMap.Buckets.bytes) = [576, 1136, 2240, 8864] ∧
    (([8, 16, 32, 128] : List (BitVec 32)).map
      (fun capacity => (ExpressionMap.Buckets.sourceRequest capacity).toNat)) = [576, 1136, 2240, 8864] := by
  decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.BucketReservationTests
