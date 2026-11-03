/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapLocalLock
import Compiler.Extraction.ExpressionMapLocalAllocationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapLockTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)
open ExpressionMap.Local

/-- Reuse the original initialized-owner execution and general composition.
No concrete allocated heap or assumed unlocked local enters this fixture. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) :
    ∃ after, lockBuckets safety 8 (MapAllocationTests.host (some 1024)) (owned safety) =
        (.ok (some ⟨5, 0⟩), after) ∧
      Facts safety 7 3 sentinel 0 after [] ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨4, 0⟩ = .ok (ExpressionMap.Receiver.value 5) ∧
      after.memory.memory.nextId = 6 ∧ after.memory.effects.allocator = 597 ∧
      (∀ slot : ExpressionMap.Initialization.Slot, slot ≠ .metadata → slot ≠ .lock →
        Compiler.ZigAir.Memory.load after.memory.memory (field safety 4 slot) = .ok slot.value) ∧
      (safety = true → Compiler.ZigAir.Memory.load after.memory.memory (field safety 4 .lock) =
        .ok (.scalar (.int false 64 18446744073709551615))) := by
  obtain ⟨after, ran, facts, read, _, cursor, effects, defaults, locked, _⟩ :=
    (Tests.initialized_from_execution safety meaning).lock_buckets (MapLocalTests.room safety) 8 (by decide) 1024
      (MapAllocationTests.host (some 1024)) 597 (by cases safety <;> decide +kernel)
      (Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ (Tests.initialized_from_execution safety meaning).valid.memory
        (by decide) (by decide) (by decide) (by cases safety <;> decide +kernel))
      (by cases safety <;> decide +kernel)
  exact ⟨after, ran, facts, read, cursor, effects, defaults, locked⟩

theorem oom_keeps_defaults (safety : Bool) (meaning : Meaning) :
    ∃ declared, declareMap safety (owned safety) = (.ok ⟨4, 0⟩, declared) ∧
      lockBuckets safety 8 (MapAllocationTests.host none) (owned safety) = (.ok none,
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } }) ∧
      Facts safety 7 3 sentinel 0
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } } [] ∧
      (∀ slot, slot.Active safety → Compiler.ZigAir.Memory.load declared.memory.memory (field safety 4 slot) = .ok slot.value) := by
  obtain ⟨declared, declaration, ran, facts, reads⟩ := MapLocalTests.oom_prefix safety meaning
  exact ⟨declared, declaration, lockBuckets_oom safety 8 (MapAllocationTests.host none) (owned safety) _ ran, facts, reads⟩

theorem exhausted_keeps_input (safety : Bool) :
    let before : World (Publication.Effects Nat) := { owned safety with memory := { (owned safety).memory with
      memory := { (owned safety).memory.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 8 } } }
    lockBuckets safety 8 (MapAllocationTests.host (some 1024)) before = (.error .outOfMemory, before) := by
  simp only [lockBuckets, MapLocalTests.exhausted_keeps_input safety]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapLockTests
