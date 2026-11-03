/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayWrites
import Compiler.Extraction.RepresentativeArrayFieldTests

namespace Compiler.Extraction.RepresentativeArray.WriteTests
open Compiler.ZigAir.Memory

def execute (state : State := FieldTests.before) (lifetime : Nat := 2) (index : Nat := 1)
    (length : Nat := 2) (id sequence : Int := 1) : Except Fault State :=
  initializeFields state lifetime index ⟨0, 0⟩ ⟨1, 4⟩ length id sequence

theorem actual_four_store_execution : execute FieldTests.before 2 1 2 1 29 = .ok FieldTests.after := by decide

/-- The destination's second descriptor starts uninitialized. The theorem
derives actual stores, validity, shape and all readonly fields from that state. -/
theorem initialization_without_store_premises :
    ∃ after, execute FieldTests.before 2 1 2 1 29 = .ok after ∧ after.valid = true ∧
      FieldTests.before.heap.RetainsShape after.heap ∧
      Expression.readFields after false ⟨2, 32⟩ = .ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence] :=
  initializeFields_verified FieldTests.before 2 3 1 FieldTests.data ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29
    FieldTests.initial_valid (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)

theorem source_bound_initialization :
    ∃ after, execute FieldTests.before 2 1 2 1 29 = .ok after ∧ representativeFields after ⟨3, 0⟩ 1 =
      .ok (.ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence]) :=
  representativeFields_after_initialization FieldTests.before ⟨3, 0⟩ 2 3 2 FieldTests.data 1 ⟨0, 0⟩ ⟨1, 4⟩ 2 29
    FieldTests.initial_valid (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide) (by decide)

theorem actual_source_bound_readback : representativeFields FieldTests.after ⟨3, 0⟩ 1 =
    .ok (.ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence]) := by
  obtain ⟨after, executed, observed⟩ := source_bound_initialization
  have same : after = FieldTests.after := Except.ok.inj (executed.symm.trans actual_four_store_execution)
  exact same ▸ observed

theorem spare_slot_still_needs_source_length :
    (do let after ← execute FieldTests.before 2 2 2 2 29
        representativeFields after ⟨3, 0⟩ 2) = .ok (.error .invalidId) := by decide

theorem array_extent_rejects_initialization : execute FieldTests.before 2 3 2 3 29 = .error .memoryValidity := by decide

def readonly : State := { FieldTests.before with heap := FieldTests.before.heap.replace 2 { FieldTests.data with writable := false } }

theorem readonly_backing_rejects_initialization : readonly.valid = true ∧ execute readonly 2 1 2 1 29 = .error .readOnly := by decide

theorem stale_lifetime_rejects_initialization : execute Tests.reused 2 1 2 1 29 = .error .unallocated := by decide

theorem wrong_allocation_kind_rejects_initialization : execute FieldTests.before 1 1 2 1 29 = .error .memoryValidity := by decide

theorem invalid_slice_length_rejects_initialization : execute FieldTests.before 2 1 addressLimit 1 29 = .error .malformed := by decide

theorem invalid_id_rejects_initialization : execute FieldTests.before 2 1 2 (-1) 29 = .error .malformed ∧
    execute FieldTests.before 2 1 2 (2 ^ 32) 29 = .error .malformed := by decide

theorem invalid_sequence_rejects_initialization : execute FieldTests.before 2 1 2 1 (-1) = .error .malformed ∧
    execute FieldTests.before 2 1 2 1 (2 ^ 32) = .error .malformed := by decide

theorem exact_offset_borrow_and_older_fields :
    (do let after ← execute FieldTests.before 2 1 2 1 29
        let result ← representativeFields after ⟨3, 0⟩ 1
        let .ok [_, view, _, _] := result | .error .malformed
        let first ← sliceElementPointer after view 0
        let second ← sliceElementPointer after view 1
        .ok [← load after first, ← load after second]) =
      .ok [.scalar (.int false 32 99), .scalar (.int false 32 1)] ∧
    (do let after ← execute FieldTests.before 2 1 2 1 29
        Expression.readFields after false ⟨2, 0⟩) =
      .ok [Expression.Tests.item, Expression.Tests.arguments, Expression.Tests.id, Expression.Tests.sequence] := by decide

end Compiler.Extraction.RepresentativeArray.WriteTests
