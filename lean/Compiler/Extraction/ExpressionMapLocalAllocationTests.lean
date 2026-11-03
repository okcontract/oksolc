/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapLocalAllocation
import Compiler.Extraction.ExpressionMapAllocationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapLocalTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open GraphInit.Ownership.Tests (owned)
open GraphInit.OwnerMemory.Tests (sentinel)
open ExpressionMap.Local

/-- The existing owner-initialization execution is the input. No extra map cell
is inserted into the fixture; declareMap supplies its own stack allocation. -/
theorem room (safety : Bool) : Room safety (owned safety).memory.memory := by
  unfold Room
  cases safety <;> decide +kernel

theorem declared_defaults (safety : Bool) :
    let declared := declareMap safety (owned safety)
    declared.1 = .ok ⟨4, 0⟩ ∧
      (∀ slot, slot.Active safety → Compiler.ZigAir.Memory.load declared.2.memory.memory
        (field safety 4 slot) = .ok slot.value) ∧
      declared.2.memory.memory.nextId = 5 := by
  obtain ⟨after, _, ran, _, _, _, _, _, _, _, reads, _, cursor, _⟩ :=
    declare_verified safety (owned safety).memory.memory (by cases safety <;> decide +kernel) (room safety)
  have id : (owned safety).memory.memory.nextId = 4 := by cases safety <;> rfl
  rw [id] at ran reads cursor
  dsimp only [declareMap]
  rw [ran]
  exact ⟨rfl, reads, cursor⟩

def execute (safety : Bool) (base : Option Nat) :=
  prepareBuckets safety 8 (MapAllocationTests.host base) (owned safety)

theorem from_initialized_owner (safety : Bool) (meaning : Meaning) :
    ∃ after, execute safety (some 1024) = (.ok (some ⟨5, 0⟩), after) ∧
      Facts safety 7 3 sentinel 0 after [] ∧
      ExpressionMap.Receiver.read safety after.memory.memory ⟨4, 0⟩ = .ok (ExpressionMap.Receiver.value 5) := by
  obtain ⟨after, ran, facts, reads, _⟩ := (Tests.initialized_from_execution safety meaning).prepare_buckets
    (room safety) 8 (by decide) 1024 (MapAllocationTests.host (some 1024)) 597
    (by cases safety <;> decide +kernel)
    (Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ (Tests.initialized_from_execution safety meaning).valid.memory
      (by decide) (by decide) (by decide) (by cases safety <;> decide +kernel))
    (by cases safety <;> decide +kernel)
  exact ⟨after, ran, facts, reads⟩

theorem captured_prefix (safety : Bool) :
    let after := (execute safety (some 1024)).2
    (execute safety (some 1024)).1 = .ok (some ⟨5, 0⟩) ∧
      after.memory.memory.nextId = 6 ∧ after.memory.effects.allocator = 597 ∧
      (∀ slot, slot.Active safety → slot ≠ .metadata → Compiler.ZigAir.Memory.load after.memory.memory
        (field safety 4 slot) = .ok slot.value) ∧
      ExpressionMap.Initialization.observeEmpty safety after.memory.memory ⟨3, 0⟩ = .ok () := by
  -- Check the complete observation once per layout, then project the fields.
  -- Separate decide proofs would replay the same concrete allocation repeatedly.
  have checked :
      let after := (execute safety (some 1024)).2
      (execute safety (some 1024)).1 = .ok (some ⟨5, 0⟩) ∧
        after.memory.memory.nextId = 6 ∧ after.memory.effects.allocator = 597 ∧
        (slots safety).all (fun slot => decide (slot = .metadata ∨ Compiler.ZigAir.Memory.load after.memory.memory
          (field safety 4 slot) = .ok slot.value)) = true ∧
        ExpressionMap.Initialization.observeEmpty safety after.memory.memory ⟨3, 0⟩ = .ok () := by
    cases safety <;> decide +kernel
  obtain ⟨ran, cursor, effects, defaults, owner⟩ := checked
  refine ⟨ran, cursor, effects, ?_, owner⟩
  intro slot active different
  have member : slot ∈ slots safety := by
    cases safety <;> cases slot <;> simp_all [slots, ExpressionMap.Initialization.Slot.Active]
  have observed := (List.all_eq_true.mp defaults) slot member
  exact (of_decide_eq_true observed).resolve_left different

theorem oom_prefix (safety : Bool) (meaning : Meaning) :
    ∃ declared, declareMap safety (owned safety) = (.ok ⟨4, 0⟩, declared) ∧
      execute safety none = (.ok none,
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } }) ∧
      Facts safety 7 3 sentinel 0
        { declared with memory := { declared.memory with effects := { declared.memory.effects with allocator := 597 } } } [] ∧
      (∀ slot, slot.Active safety → Compiler.ZigAir.Memory.load declared.memory.memory (field safety 4 slot) = .ok slot.value) := by
  exact (Tests.initialized_from_execution safety meaning).prepare_buckets_oom (room safety) 8 (by decide)
    (MapAllocationTests.host none) 597 (by cases safety <;> decide +kernel)

theorem exhausted_keeps_input (safety : Bool) :
    let before : World (Publication.Effects Nat) := { owned safety with memory := { (owned safety).memory with
      memory := { (owned safety).memory.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 8 } } }
    prepareBuckets safety 8 (MapAllocationTests.host (some 1024)) before = (.error .outOfMemory, before) := by
  dsimp only
  apply prepareBuckets_exhausted
  · cases safety <;> decide +kernel
  · unfold Room; cases safety <;> decide +kernel

/-- A fresh heap region may lie below the stack cursor. The declaration proof
requires separation from live objects, not increasing allocator addresses. -/
theorem region_below_cursor (safety : Bool) :
    Compiler.ZigAir.Memory.RegionAllocation.Fits
      (declare safety ⟨[], 0, 4096⟩).2 ⟨576, 16⟩ 1024 := by
  apply declare_region safety ⟨[], 0, 4096⟩ (by decide)
    (by unfold Room; cases safety <;> decide) ⟨576, 16⟩ 1024
  · exact ⟨by decide, by decide, by decide, by simp⟩
  · exact Or.inl (by decide)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.MapLocalTests
