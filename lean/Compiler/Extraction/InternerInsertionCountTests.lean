/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionCount
import Compiler.Extraction.RepresentativeOwnerFieldTests
import Compiler.Extraction.StoragePreparationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CountTests
open Compiler.Extraction.Storage RepresentativeArray

/-- Header-only boundary fixtures use actual typed field stores. A large length
does not certify a correspondingly large backing, row graph or allocation. -/
def written (safety : Bool) (length : Nat) (capacity : Int) :=
  Owner.FieldTests.execute safety (Owner.FieldTests.before safety true true) ⟨3, 0⟩ ⟨2, 0⟩ length capacity
def observed (safety : Bool) (length : Nat) (capacity : Int) := do
  let state ← written safety length capacity
  headerCount state 3

theorem native_boundary_reads (safety : Bool) :
    observed safety 0 3 = .ok 0 ∧
    observed safety (2 ^ 32 - 2) 3 = .ok (2 ^ 32 - 2) ∧
    observed safety (2 ^ 32 - 1) 3 = .ok (2 ^ 32 - 1) ∧
    observed safety (2 ^ 32) 3 = .ok (2 ^ 32) := by
  cases safety <;> decide +kernel

theorem capacity_boundary : roomForCount 0 = true ∧ roomForCount (2 ^ 32 - 2) = true ∧
    roomForCount (2 ^ 32 - 1) = false ∧ roomForCount (2 ^ 32) = false := by decide

/-- The source checks items.len. Reserved capacity is neither its input nor a
prerequisite for reading that input. Whole-container admission remains separate. -/
theorem capacity_field_not_read (safety : Bool) :
    observed safety 0 (2 ^ 32 - 1) = .ok 0 ∧
    headerCount (Owner.FieldTests.withItems safety true) 3 = .ok 2 := by
  cases safety <;> decide +kernel

theorem mismatch_rejects (safety : Bool) :
    checkedCount (Owner.FieldTests.after safety true) 3 [] = .error (.mismatch 2 0) := by
  cases safety <;> decide +kernel

theorem unreadable_rejects (safety : Bool) :
    checkedCount (Owner.FieldTests.before safety true true) 3 [] = .error (.memory .uninitialized) ∧
    checkedCount (Owner.FieldTests.after safety true) 4 [] = .error (.memory .unallocated) := by
  cases safety <;> decide +kernel

/-- Any attempt or wrong cleanup would fail the fixture. Only the actual source
normalized defer appends to this trace, in both determinism settings. -/
def calls : Storage.Operations (List Storage.Release) Unit :=
  ⟨fun _ _ trace => (.error (), trace), fun release _ trace =>
    if release = .normalized then (.ok (), trace ++ [release]) else (.error (), trace)⟩

theorem only_normalized_cleanup (deterministic : Bool) :
    Storage.insertProgram.execute ⟨deterministic, false, fun _ => false⟩ calls {} [] =
      ((.ok (some .capacityFailure), Storage.Release.normalized.run Storage.normalizedOwnership), [.normalized]) :=
  Storage.insert_capacity_failure calls deterministic [] [.normalized] (fun _ => rfl)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.CountTests
