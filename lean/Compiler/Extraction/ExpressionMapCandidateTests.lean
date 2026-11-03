/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCandidateMemory
import Compiler.Extraction.ExpressionMapTableTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapCandidateTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open ExpressionMap ExpressionMap.Buckets MapTableTests

theorem after_repeated_publication (safety : Bool) (meaning : Meaning) :
    ∃ world : World (Publication.Effects Nat), Facts safety 7 3 GraphInit.OwnerMemory.Tests.sentinel 0 world [] ∧
      ∃ bits result, Metadata.readByte world.memory.memory 5 2 = .ok bits ∧
        Candidate.run world.memory.memory 8 5 2 8 93 firstKey (view ⟨0, []⟩) = .ok result ∧
        Candidate.Correct world.memory.memory 8 5 2 8 93 firstKey world.memory.effects.keys bits result := by
  obtain ⟨_, world, _, _, facts, binding, _⟩ := repeated_from_initialized_owner safety meaning
  exact ⟨world, facts, facts.lookup_candidate .localMap 4 8 5 2 8 binding (by decide) 93 firstKey ⟨0, []⟩ rfl (empty_custody _)⟩

def copied : Compiler.ZigAir.Memory.State :=
  { native with heap := (4, { arguments with base := 9024 }) :: native.heap, nextId := 5, nextAddress := 9036 }

theorem copied_hit : Candidate.run copied 8 1 2 8 93 MapKeyTests.sample ⟨4, 0, 3⟩ = .ok (.hit 37) := by decide +kernel
theorem alias_hit : Candidate.run native 8 1 2 8 93 MapKeyTests.sample ⟨3, 0, 3⟩ = .ok (.hit 37) := by decide +kernel
theorem wrong_scalar_skipped : Candidate.run native 8 1 2 8 93 { MapKeyTests.sample with sequence := 0 } ⟨3, 0, 3⟩ = .ok .next := by decide +kernel
theorem wrong_fingerprint_skipped : Candidate.run native 8 1 2 8 94 MapKeyTests.sample ⟨3, 0, 3⟩ = .ok .next := by decide +kernel
theorem exhausted_stopped : Candidate.run native 8 1 2 0 93 MapKeyTests.sample ⟨3, 0, 3⟩ = .ok .stop := by decide +kernel
theorem free_stopped : Candidate.run native 8 1 3 8 93 MapKeyTests.sample ⟨3, 0, 3⟩ = .ok .stop := by decide +kernel

def changed : Compiler.ZigAir.Memory.State :=
  { copied with heap := copied.heap.replace 4 { arguments with base := 9024, cells := [(0, number 5), (4, number 18), (8, number 4294967295)] } }
theorem changed_argument_skipped : Candidate.run changed 8 1 2 8 93
    { MapKeyTests.sample with arguments := [5, 18, 4294967295] } ⟨4, 0, 3⟩ = .ok .next := by decide +kernel
theorem short_argument_skipped : Candidate.run copied 8 1 2 8 93
    { MapKeyTests.sample with arguments := [5, 17] } ⟨4, 0, 2⟩ = .ok .next := by decide +kernel

def missing : Compiler.ZigAir.Memory.State :=
  { copied with heap := copied.heap.replace 4 { arguments with base := 9024, cells := [(0, number 5)] } }
theorem uninitialized_rejected : Candidate.run missing 8 1 2 8 93 MapKeyTests.sample ⟨4, 0, 3⟩ = .error .uninitialized := by decide +kernel
theorem oversized_rejected : ArgumentScan.run native ⟨3, 0, addressLimit⟩ ⟨3, 0, addressLimit⟩ = .error .memoryValidity := by decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapCandidateTests
