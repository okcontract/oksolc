/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashInputMemory
import Compiler.Extraction.ExpressionMapSearchTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapHashInputTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap
open MapTableTests (firstKey empty_custody)

/-- Existing collision fixtures exercise composition independently of Wyhash.
This deliberately constant digest does not claim to be the native hash. -/
def collisionDigest (_ : List (List (BitVec 8))) : BitVec 64 := MapProbeTests.collision firstKey

theorem existing_lookup (safety : Bool) (meaning : Meaning) :
    Search.withInputDigest .localMap safety (MapProbeTests.second safety).memory.memory 4 collisionDigest firstKey (view ⟨0, []⟩) = .ok (some 37) := by
  obtain ⟨facts, inv, first, _⟩ := MapProbeTests.repeated_from_initialized_owner safety meaning
  have result := (facts.lookup_from_hash_input collisionDigest .localMap 4 5 8 4 inv firstKey ⟨0, []⟩ rfl (empty_custody _)).2
  rw [result]
  exact (facts.lookup_hashed MapProbeTests.collision .localMap 4 5 8 4 inv firstKey ⟨0, []⟩ rfl (empty_custody _)).symm.trans first

theorem existing_publication (safety : Bool) (meaning : Meaning) :
    ∃ after,
      publishFromReceiver .localMap safety 4 1 8 (collisionDigest (HashInput.encode MapSearchTests.thirdKey)) MapSearchTests.thirdKey ⟨0, []⟩ 71 (MapProbeTests.second safety) = (.ok (), after) ∧
      Facts safety 7 3 GraphInit.OwnerMemory.Tests.sentinel 0 after [] := by
  obtain ⟨facts, inv, _, _⟩ := MapProbeTests.repeated_from_initialized_owner safety meaning
  obtain ⟨_, outcome, ran, post⟩ := facts.probe_hash_input_then_publish collisionDigest .localMap 4 5 8 4
    (by intro impossible; cases impossible) inv (by decide) MapSearchTests.thirdKey ⟨0, []⟩ 71 rfl (empty_custody _)
  have inputs := (facts.hash_input MapSearchTests.thirdKey ⟨0, []⟩ rfl (empty_custody _)).1
  rw [Search.insertion_with_input_digest_eq inputs] at ran
  have selected : outcome = .miss 1 8 := Except.ok.inj (ran.symm.trans (MapSearchTests.third_probe safety))
  subst outcome
  obtain ⟨after, published, afterFacts, _⟩ := post
  exact ⟨after, published, afterFacts⟩

theorem word_bytes : HashInput.word 0x12345678 = [0x78, 0x56, 0x34, 0x12] := by decide +kernel

theorem scalar_boundaries : HashInput.data (2^255 + 2^128 + 1) =
    [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128] := by decide +kernel

theorem argument_bytes : HashInput.arguments [5, 17, 4294967295] =
    [5, 0, 0, 0, 17, 0, 0, 0, 255, 255, 255, 255] := by decide +kernel

theorem native_bytes :
    HashInput.read MapTableTests.native MapKeyTests.sample ⟨3, 0, 3⟩ = .ok (HashInput.encode MapKeyTests.sample) :=
  HashInput.read_verified _ _ _ MapTableTests.argument_view.contents (by decide)

theorem copied_bytes :
    HashInput.read MapCandidateTests.copied MapKeyTests.sample ⟨4, 0, 3⟩ = .ok (HashInput.encode MapKeyTests.sample) := by decide +kernel

theorem changed_bytes :
    HashInput.read MapCandidateTests.changed MapKeyTests.sample ⟨4, 0, 3⟩ ≠ .ok (HashInput.encode MapKeyTests.sample) := by decide +kernel

theorem uninitialized_rejected :
    HashInput.read MapCandidateTests.missing MapKeyTests.sample ⟨4, 0, 3⟩ = .error .uninitialized := by decide +kernel

theorem lookup_uninitialized_rejected :
    Search.withInputDigest .localMap true MapCandidateTests.missing 2 collisionDigest MapKeyTests.sample ⟨4, 0, 3⟩ = .error .uninitialized := by
  exact Search.with_input_digest_rejected (size := 1) (by decide +kernel) (by decide) uninitialized_rejected

theorem oversized_rejected :
    HashInput.read MapTableTests.native MapKeyTests.sample ⟨3, 0, Compiler.ZigAir.Memory.addressLimit⟩ = .error .memoryValidity := by decide +kernel

theorem empty_skips_hash_inputs (safety : Bool) (digest : List (List (BitVec 8)) → BitVec 64) (key : Key) :
    Search.withInputDigest .embedded safety (GraphInit.Ownership.Tests.owned safety).memory.memory 3 digest key ⟨999, 0, 1⟩ = .ok none := by
  have zero : Search.readCount .embedded safety (GraphInit.Ownership.Tests.owned safety).memory.memory 3 = .ok 0 := by cases safety <;> decide +kernel
  simp only [Search.withInputDigest, zero, bind, Except.bind, ↓reduceIte]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapHashInputTests
