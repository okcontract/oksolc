/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapWyhash
import Compiler.Extraction.WyhashBufferTests
import Compiler.Extraction.WyhashHashVectors

set_option maxRecDepth 4096

namespace Compiler.Extraction.WyhashHash.Tests
open Compiler.ZigAir.Memory WyhashLocal WyhashUpdate

theorem captured_results : vectors.zipIdx.all (fun ((sizes, expected), index) =>
    decide (run 0 (chunks index 0 sizes) = .ok expected)) = true := by decide +kernel

/-- Exactly 48 remaining bytes belong to finalization. No source or state word
is touched, even when both objects are completely uninitialized. -/
theorem exact_block_no_reads : loop [] ⟨.array 48 ByteSlice.byte, 0, 48⟩ 0 [] = .ok ([], 0) := by
  rw [loop]
  rfl

theorem overflow_before_reads :
    loop [] ⟨.array 1 ByteSlice.byte, 0, 1⟩ (addressLimit - 48) [] = .error .memoryValidity := by
  rw [loop]
  rfl

theorem short_input_explicit : run 0 [[1, 2, 3]] = .error .unsupported := by decide +kernel

theorem missing_input_rejected :
    update [] (ByteSlice.imageView [1]) (initialCells (seedState 0)) = .error .uninitialized := by decide +kernel

theorem wrong_input_type_rejected :
    update [(0, word 1)] (ByteSlice.imageView [1]) (initialCells (seedState 0)) = .error .malformed := by decide +kernel

end Compiler.Extraction.WyhashHash.Tests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapWyhashTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap
open MapTableTests (prepared empty_custody)

/-- The original native argument-read fixture now feeds the complete local
hasher. No hash value, buffer initialization or successful update is supplied. -/
theorem observed_source_consumed :
    (do let inputs ← HashInput.read MapTableTests.native MapKeyTests.sample ⟨3, 0, 3⟩
        WyhashHash.run 0 inputs) = .ok (WyhashHash.digest (HashInput.encode MapKeyTests.sample)) :=
  WyhashLocal.bind_result _ _ _ _ MapHashInputTests.native_bytes (HashInput.wyhash_verified _ (by decide))

/-- Reuse the same initialized owner for arbitrary empty-argument keys and IDs.
The complete local hash selects publication and the subsequent lookup. -/
theorem initialized_publication_lookup (safety : Bool) (meaning : Meaning) (key : Key)
    (empty : key.arguments = []) (id : NodeId) :
    ∃ after index first,
      Search.insertionWithLocalWyhash .localMap safety (prepared safety).memory.memory 4 key (view ⟨0, []⟩) = .ok (.miss index first) ∧
      publishFromReceiver .localMap safety 4 index first (WyhashHash.digest (HashInput.encode key)) key ⟨0, []⟩ id (prepared safety) = (.ok (), after) ∧
      Facts safety 7 3 GraphInit.OwnerMemory.Tests.sentinel 0 after [] ∧
      Search.withLocalWyhash .localMap safety after.memory.memory 4 key (view ⟨0, []⟩) = .ok (some id) := by
  obtain ⟨facts, inv, keys⟩ := MapProbeTests.initialized_owner (WyhashHash.digest ∘ HashInput.encode) safety meaning
  obtain ⟨outcome, probed, post⟩ := facts.probe_local_wyhash_then_publish .localMap 4 5 8 6
    (by intro impossible; cases impossible) inv (by decide) key ⟨0, []⟩ id empty (empty_custody _)
  cases outcome with
  | hit index =>
    obtain ⟨_, entry, present, _⟩ := post
    rw [keys] at present
    cases present
  | miss index first =>
    obtain ⟨after, published, afterFacts, afterInv, afterKeys, _⟩ := post
    refine ⟨after, index, first, probed, published, afterFacts, ?_⟩
    rw [afterFacts.lookup_from_local_wyhash .localMap 4 5 8 5 afterInv key ⟨0, []⟩ empty (empty_custody _), afterKeys]
    simp [OwnedKeys.store]

theorem empty_skips_hash (safety : Bool) (key : Key) :
    Search.withLocalWyhash .embedded safety (GraphInit.Ownership.Tests.owned safety).memory.memory 3 key ⟨999, 0, 1⟩ = .ok none := by
  have zero : Search.readCount .embedded safety (GraphInit.Ownership.Tests.owned safety).memory.memory 3 = .ok 0 := by cases safety <;> decide +kernel
  simp only [Search.withLocalWyhash, zero, bind, Except.bind, ↓reduceIte]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapWyhashTests
