/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationPreparedMemory
import Compiler.Extraction.NormalizationPreparedTests
import Compiler.Extraction.InsertionSortCopiedTests
import Compiler.Extraction.ScopedSemanticTests

namespace Compiler.Extraction.Cache.NormalizationOwnership.PreparedMemoryTests
open Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.ZigAir

/-- This fixture uses typed stack reservation as a bounded resource oracle for
an external allocation callback. It does not model native allocator lifetime,
freeing, or successful duplicate copying. The observed prepared path fails that
allocation, so no successful owned-buffer refinement is inferred. -/
def reservation : Primitives Memory.State where
  allocate := fun _ before => match Memory.allocate before (.array 3 word) with
    | .error _ => (false, before)
    | .ok (_, after) => (true, after)
  release := fun _ before => before

def source := Memory.WordCopy.Tests.source
def target (_ : State) (_ : Memory.State) := Memory.WordCopy.Tests.target
def before : Memory.State := { Memory.WordCopy.Tests.caller with nextAddress := Memory.addressLimit - 24 }
def prepared : Memory.State := (Copied.run 160 before source (target {} before)).2
def run (budget : Nat) := normalizationOwnershipCode.runPrepared true 3 3 (copiedPrimitives budget source target reservation) .transfer before

theorem before_valid : before.valid = true := by decide +kernel
theorem target_writable : Writable before (target {} before) := Memory.WordCopy.Tests.writable_target
theorem source_represented : Represents before source [3, 1, 2] := Memory.WordCopy.Tests.represented_source

theorem initial_allocation_would_succeed : (reservation.allocate .duplicate before).1 = true := by rfl'
theorem original_projection_transfers : (normalizationOwnershipCode.runWith true 3 3 reservation .transfer before).1.1 = .transferred := by rfl'
theorem prepared_allocation_failure : run 160 =
    (.ok (.allocationFailure, { origin := .scratch, dead := true }), prepared) := by rfl'
theorem prepared_counters : prepared.nextId = 5 ∧ prepared.nextAddress = Memory.addressLimit - 8 := ⟨by rfl', by rfl'⟩
theorem prepared_values : Memory.WordCopy.Tests.observations prepared =
    [3, 1, 2, 3735928559, 1, 2, 3, 3131961357, 99].map (fun value => .ok (number value)) := by rfl'

theorem zero_budget_keeps_copy : run 0 =
    (.error (.incomplete, { origin := .scratch }), (Memory.WordCopy.copy before source (target {} before)).2) := by rfl'
def exhausted : Memory.State := { before with nextAddress := Memory.addressLimit - 8 }
theorem private_exhaustion_is_semantic_fault :
    normalizationOwnershipCode.runPrepared true 3 3 (copiedPrimitives 160 source target reservation) .transfer exhausted =
      (.error (.memory .outOfMemory, { origin := .scratch }), (Memory.WordCopy.copy exhausted source (target {} exhausted)).2) := by rfl'

theorem whole_scope_settles : ∃ result after,
    Captured.Settles run (result, after) ∧ PreparedSafe result :=
  copied_run_settles true 3 source target reservation .transfer before before { origin := .scratch } [3, 1, 2]
    rfl (by decide) before_valid target_writable source_represented rfl (by decide)

theorem all_budgets_ownership_safe (budget : Nat) : PreparedSafe (run budget).1 :=
  copied_ownership_safe budget true 3 source target reservation .transfer before

end Compiler.Extraction.Cache.NormalizationOwnership.PreparedMemoryTests
