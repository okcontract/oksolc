/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapReady
import Compiler.Extraction.ExpressionMapMetadataTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapReadyTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)

/-- The same owner fixture consumes complete pre-rehash initialization, without
supplying a prepared map, initialized storage, or a chosen final graph. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) :
    ∃ after, readyBuckets safety 8 (MapAllocationTests.host (some 1024)) (owned safety) =
        (.ok (some ⟨5, 0⟩), after) ∧ Facts safety 7 3 sentinel 0 after [] ∧
      after.memory.memory.nextId = 6 ∧ after.memory.effects.allocator = 597 ∧
      ExpressionMap.Local.EmptyReady safety 4 5 8 1024 after.memory.memory ∧
      (∀ key, ExpressionMap.Local.getEmpty safety after.memory.memory 4 key = .ok none) ∧
      Compiler.ZigAir.Memory.load after.memory.memory (ExpressionMap.Local.field safety 4 .available) =
        .ok (.scalar (.int false 32 6)) ∧ Metadata.observe after.memory.memory 5 7 = .ok (true, false) := by
  obtain ⟨after, ran, facts, cursor, effects, ready⟩ :=
    (Tests.initialized_from_execution safety meaning).ready_buckets (MapLocalTests.room safety) 8 (by decide) 1024
      (MapAllocationTests.host (some 1024)) 597 (by cases safety <;> decide +kernel)
      (Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ (Tests.initialized_from_execution safety meaning).valid.memory
        (by decide) (by decide) (by decide) (by cases safety <;> decide +kernel))
      (by cases safety <;> decide +kernel)
  exact ⟨after, ran, facts, cursor, effects, ready, ready.lookup, ready.available, ready.slots 7 (by decide)⟩

theorem oom_keeps_prefix (safety : Bool) (meaning : Meaning) :
    ∃ declared, declareMap safety (owned safety) = (.ok ⟨4, 0⟩, declared) ∧
      readyBuckets safety 8 (MapAllocationTests.host none) (owned safety) = (.ok none,
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } }) ∧
      Facts safety 7 3 sentinel 0
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } } [] := by
  obtain ⟨declared, declaration, ran, facts⟩ := MapMetadataTests.oom_keeps_defaults safety meaning
  exact ⟨declared, declaration, readyBuckets_oom safety 8 (MapAllocationTests.host none) (owned safety) _ ran, facts⟩

theorem exhausted_keeps_input (safety : Bool) :
    let before : World (Publication.Effects Nat) := { owned safety with memory := { (owned safety).memory with
      memory := { (owned safety).memory.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 8 } } }
    readyBuckets safety 8 (MapAllocationTests.host (some 1024)) before = (.error .outOfMemory, before) := by
  simp only [readyBuckets, MapMetadataTests.exhausted_keeps_input safety]

theorem source_word_boundaries :
    (ExpressionMap.Local.Availability.word 0).toNat = 0 ∧
    (ExpressionMap.Local.Availability.word 7).toNat = 5 ∧
    (ExpressionMap.Local.Availability.word 8).toNat = 6 ∧
    (ExpressionMap.Local.Availability.word 4294967295).toNat = 3435973836 := by decide +kernel

/-- Reading the assigned field observes the actual store, including when its
previous bytes were uninitialized. An execution fault cannot satisfy this. -/
theorem assigned_count_readback (safety : Bool) :
    let before : Compiler.ZigAir.Memory.State :=
      ⟨[(1, ⟨4096, ExpressionMap.allocationType safety, [], true, true⟩)], 2, 4128⟩
    ((ExpressionMap.Local.Availability.assign safety 1 8 before).toOption.bind fun after =>
      (Compiler.ZigAir.Memory.load after (ExpressionMap.Local.field safety 1 .available)).toOption) =
        some (.scalar (.int false 32 6)) := by
  cases safety <;> decide +kernel

/-- Selector and write faults remain distinct; neither supplies a default count. -/
theorem readonly_rejected (safety : Bool) :
    let before : Compiler.ZigAir.Memory.State :=
      ⟨[(1, ⟨4096, ExpressionMap.allocationType safety, [], false, true⟩)], 2, 4128⟩
    ExpressionMap.Local.Availability.assign safety 1 8 before = .error .readOnly := by
  cases safety <;> decide +kernel

theorem missing_receiver_rejected (safety : Bool) :
    ExpressionMap.Local.Availability.assign safety 4 8 (owned safety).memory.memory = .error .unallocated := by
  cases safety <;> decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapReadyTests
