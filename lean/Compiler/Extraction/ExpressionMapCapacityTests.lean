/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCapacityMemory
import Compiler.Extraction.ExpressionMapReadyTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapCapacityTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray ExpressionMap.Buckets
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)
open ExpressionMap.Capacity

theorem observed_from_initialization (safety : Bool) (meaning : Meaning) :
    Observed .embedded safety (owned safety).memory.memory 3 0 0 :=
  (GraphInit.Ownership.Tests.initial_ownership_from_execution safety meaning).capacity_observed

/-- The same owner fixture now supplies a requested count, not a chosen bucket
capacity or successful capacity guard. All native preparation is consumed. -/
theorem from_initialized_owner (safety : Bool) (meaning : Meaning) :
    ∃ after, prepareGrowth .embedded safety 3 1 (MapAllocationTests.host (some 1024)) (owned safety) =
        (.ok (.prepared 8 ⟨5, 0⟩), after) ∧ Facts safety 7 3 sentinel 0 after [] ∧
      ExpressionMap.Local.EmptyReady safety 4 5 8 1024 after.memory.memory ∧
      after.memory.memory.nextId = 6 ∧ after.memory.effects.allocator = 597 ∧
      (∀ key, ExpressionMap.Local.getEmpty safety after.memory.memory 4 key = .ok none) := by
  have selected : target 0 0 1 = 8 := by decide +kernel
  obtain ⟨after, ran, facts, ready, _, _, _, cursor, reached⟩ :=
    (Tests.initialized_from_execution safety meaning).prepare_growth .embedded 3 0 0 1
      (observed_from_initialization safety meaning) (by decide) (by decide) (by decide)
      (MapLocalTests.room safety) 1024 (MapAllocationTests.host (some 1024)) 597
      (by rw [selected]; cases safety <;> decide +kernel)
      (by
        rw [selected]
        exact Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _
          (Tests.initialized_from_execution safety meaning).valid.memory (by decide) (by decide) (by decide)
          (by cases safety <;> decide +kernel))
      (by rw [selected]; cases safety <;> decide +kernel)
  rw [selected] at ran ready
  exact ⟨after, ran, facts, ready, cursor, reached, ready.lookup⟩

theorem no_growth_retains_input (safety : Bool) (meaning : Meaning) :
    prepareGrowth .embedded safety 3 0 (MapAllocationTests.host (some 1024)) (owned safety) = (.ok .enough, owned safety) :=
  prepareGrowth_enough .embedded safety 3 0 0 _ _ (observed_from_initialization safety meaning).availableRead (by decide)

theorem oom_keeps_prefix (safety : Bool) (meaning : Meaning) :
    ∃ declared, declareMap safety (owned safety) = (.ok ⟨4, 0⟩, declared) ∧
      prepareGrowth .embedded safety 3 1 (MapAllocationTests.host none) (owned safety) = (.ok .outOfMemory,
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } }) ∧
      Facts safety 7 3 sentinel 0
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } } [] := by
  obtain ⟨declared, declaration, ran, facts⟩ := MapReadyTests.oom_keeps_prefix safety meaning
  have selected := (observed_from_initialization safety meaning).select_growth 1 (by decide) (by decide) (by decide)
  have target : target 0 0 1 = 8 := by decide +kernel
  refine ⟨declared, declaration, ?_, facts⟩
  have selection := selected.1
  rw [target] at selection
  exact prepareGrowth_prefix .embedded safety 3 1 _ _ 8 _ _ selection ran

/-- The allocated temporary receiver supplies its nonnull metadata/header reads.
No-growth skips allocation; the next larger request selects sixteen slots. -/
theorem allocated_capacity_reads (safety : Bool) (meaning : Meaning) :
    ∃ after, readyBuckets safety 8 (MapAllocationTests.host (some 1024)) (owned safety) = (.ok (some ⟨5, 0⟩), after) ∧
      selectMemory .localMap safety after.memory.memory 4 6 = .ok none ∧
      selectMemory .localMap safety after.memory.memory 4 7 = .ok (some 16) := by
  obtain ⟨after, ran, _, _, _, ready, _⟩ := MapReadyTests.from_initialized_owner safety meaning
  have observed := ready_observed ready (by decide)
  refine ⟨after, ran, select_memory_room .localMap safety _ 4 6 6 observed.availableRead (by decide), ?_⟩
  exact (observed.select_growth 7 (by decide) (by decide) (by decide)).1

theorem native_word_boundaries (safety : Bool) :
    forSize safety 0 = .ok 1 ∧ forSize safety 6 = .ok 8 ∧ forSize safety 7 = .ok 16 ∧
    forSize safety 13 = .ok 32 ∧ forSize safety 1717986918 = .ok 2147483648 ∧
    forSize safety 1717986919 = .error (rejected safety) ∧
    forSize safety 4294967295 = .error (rejected safety) := by
  cases safety <;> decide +kernel

theorem invalid_countdown_and_sum (safety : Bool) :
    select safety 8 7 8 = .error (rejected safety) ∧
    select safety 2147483648 0 4294967295 = .error (rejected safety) := by
  cases safety <;> decide +kernel

theorem selection_boundaries (safety : Bool) :
    select safety 0 0 0 = .ok none ∧ select safety 0 0 1 = .ok (some 8) ∧
    select safety 8 6 6 = .ok none ∧ select safety 8 6 7 = .ok (some 16) ∧
    select safety 8 0 1 = .ok (some 16) ∧ select safety 16 12 13 = .ok (some 32) ∧
    select safety 2147483648 0 1 = .error (rejected safety) := by
  cases safety <;> decide +kernel

theorem missing_receiver_rejected (safety : Bool) :
    prepareGrowth .embedded safety 4 1 (MapAllocationTests.host (some 1024)) (owned safety) =
      (.error .unallocated, owned safety) := by
  apply prepareGrowth_rejected
  cases safety <;> decide +kernel

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapCapacityTests
