/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashBytes
import Compiler.ZigAir.AggregateAirTests
import Compiler.ZigAir.SliceBytesAirTests

namespace Compiler.Extraction.ExpressionMap.HashBytes.Tests
open Compiler.ZigAir.Memory Compiler.Extraction.Cache
open Buckets

def key : Key := ⟨0x12345678, 0xab, 2 ^ 255 + 0x1234, [], 0x98765432⟩
def state : State :=
  ⟨[(0, ⟨4096, keyType, HashKey.cells key ⟨999, 0⟩, true, true⟩)], 1, 4160⟩

theorem initialized_views : (inputs state 0).1 = .ok (HashInput.encode key) := by decide +kernel

theorem empty_helper_allocation_history :
    (inputs state 0).2.heap = state.heap ∧ (inputs state 0).2.nextId = 2 ∧
    (inputs state 0).2.nextAddress = 4176 := by decide +kernel

theorem slice_result_bytes :
    HashSlice.read Compiler.ZigAir.SliceBytesAir.Tests.caller
      (.value (.slice (.slice false (.scalar (.int false 8))) ⟨0, 4⟩ 8)) =
        .ok [0x78, 0x56, 0x34, 0x12, 0xef, 0xcd, 0xab, 0x90] := by decide +kernel

theorem slice_result_requires_initialized_words :
    HashSlice.read { Compiler.ZigAir.SliceBytesAir.Tests.caller with
      heap := [(0, ⟨16, .array 3 WordArray.word, [], false, false⟩)] }
      (.value (.slice (.slice false (.scalar (.int false 8))) ⟨0, 4⟩ 8)) = .error .uninitialized := by decide +kernel

theorem little_endian_lanes :
    ScalarBytes.readAt state ⟨0, 0⟩ = .ok 0x34 ∧
    ScalarBytes.readAt state ⟨0, 1⟩ = .ok 0x12 ∧
    ScalarBytes.readAt state ⟨0, 31⟩ = .ok 0x80 ∧
    ScalarBytes.readAt state ⟨0, 51⟩ = .ok 0x12 ∧
    ScalarBytes.readAt state ⟨0, 56⟩ = .ok 0xab := by decide +kernel

theorem padding_and_pointer_rejected :
    ScalarBytes.readAt state ⟨0, 57⟩ = .error .unsupported ∧
    ScalarBytes.readAt state ⟨0, 32⟩ = .error .unsupported ∧
    ScalarBytes.readAt state ⟨0, 64⟩ = .error .memoryValidity := by decide +kernel

theorem stale_and_uninitialized_rejected :
    ScalarBytes.readAt state ⟨1, 0⟩ = .error .unallocated ∧
    read { state with heap := [(0, ⟨4096, keyType, [], true, true⟩)] } 0 .data =
      .error .uninitialized := by decide +kernel

theorem readonly_view :
    read { state with heap := [(0, ⟨4096, keyType, HashKey.cells key ⟨999, 0⟩, false, true⟩)] } 0 .data =
      .ok (Field.image .data key) := by decide +kernel

theorem byte_extent_enforced : ScalarBytes.read state (Field.data.slice 0) 32 = .error .sourceBounds := by decide +kernel

theorem cast_permissions_and_geometry :
    let source := Value.pointer (.pointer false false (.scalar (.int false 256))) ⟨0, 0⟩
    ScalarBytes.arrayCast state true 16 32 source = .error .readOnly ∧
    ScalarBytes.arrayCast state false 32 32 source = .error .unsupported ∧
    ScalarBytes.arrayCast state false 16 31 source = .error .unsupported := by decide +kernel

theorem key_allocation_failure :
    let before : State := ⟨[], 0, addressLimit - 64⟩
    HashKey.create before key ⟨999, 0⟩ = (.error .outOfMemory, before) := by decide +kernel

end Compiler.Extraction.ExpressionMap.HashBytes.Tests
