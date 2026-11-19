/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapMetadataInitialization
import Compiler.Extraction.ExpressionMapLocalLockTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapMetadataTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)

/-- The new statement consumes the same original owner and original allocator;
metadata initialization is not added as a fixture or a theorem premise. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) :
    ∃ after, clearBuckets safety 8 (MapAllocationTests.host (some 1024)) (owned safety) =
        (.ok (some ⟨5, 0⟩), after) ∧ Facts safety 7 3 sentinel 0 after [] ∧
      after.memory.memory.nextId = 6 ∧ after.memory.effects.allocator = 597 ∧
      (∀ index, index < 8 → Metadata.observe after.memory.memory 5 index = .ok (true, false)) ∧
      (safety = true → Compiler.ZigAir.Memory.load after.memory.memory
        (ExpressionMap.Local.field safety 4 .lock) = .ok ExpressionMap.Local.exclusive) := by
  obtain ⟨after, ran, facts, _, _, cursor, effects, _, locked, reads, _⟩ :=
    (Tests.initialized_from_execution safety meaning).clear_buckets (MapLocalTests.room safety) 8 (by decide) 1024
      (MapAllocationTests.host (some 1024)) 597 (by cases safety <;> decide +kernel)
      (Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ (Tests.initialized_from_execution safety meaning).valid.memory
        (by decide) (by decide) (by decide) (by cases safety <;> decide +kernel))
      (by cases safety <;> decide +kernel)
  exact ⟨after, ran, facts, cursor, effects, reads, locked⟩

theorem oom_keeps_defaults (safety : Bool) (meaning : Meaning) :
    ∃ declared, declareMap safety (owned safety) = (.ok ⟨4, 0⟩, declared) ∧
      clearBuckets safety 8 (MapAllocationTests.host none) (owned safety) = (.ok none,
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } }) ∧
      Facts safety 7 3 sentinel 0
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } } [] := by
  obtain ⟨declared, declaration, ran, facts, _⟩ := MapLockTests.oom_keeps_defaults safety meaning
  exact ⟨declared, declaration, clearBuckets_oom safety 8 (MapAllocationTests.host none) (owned safety) _ ran, facts⟩

theorem exhausted_keeps_input (safety : Bool) :
    let before : World (Publication.Effects Nat) := { owned safety with memory := { (owned safety).memory with
      memory := { (owned safety).memory.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 8 } } }
    clearBuckets safety 8 (MapAllocationTests.host (some 1024)) before = (.error .outOfMemory, before) := by
  simp only [clearBuckets, MapLockTests.exhausted_keeps_input safety]

open Compiler.ZigAir.Memory

theorem initially_uninitialized : Metadata.observe BucketStorageTests.fresh 1 0 = .error .uninitialized := by decide +kernel

/-- Clear the last metadata byte, then reach opaque key storage. A rejected
write must preserve that actual store and the separately initialized header. -/
theorem partial_rejection :
    let before := (Header.run 8 1 BucketStorageTests.fresh).2
    let result := Metadata.fill 1 2 7 before
    result.1 = .error .unsupported ∧
      Metadata.observe result.2 1 7 = .ok (true, false) ∧
      load result.2 (Header.Slot.capacity.pointer 8 1) = .ok (Header.Slot.capacity.value 8 1) := by
  decide +kernel

theorem readonly_rejected :
    let before : Compiler.ZigAir.Memory.State := ⟨[(1, ⟨4096, storageType 8, [], false, false⟩)], 2, 4672⟩
    Metadata.fill 1 8 0 before = (.error .readOnly, before) := by decide +kernel

theorem wrong_extent_rejected :
    Metadata.byteArray BucketStorageTests.fresh 7 ⟨1, 24⟩ = .error .unsupported := by decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapMetadataTests
