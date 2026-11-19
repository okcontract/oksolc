/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOwner
import Compiler.Extraction.RepresentativeArrayBorrowFrameTests

namespace Compiler.Extraction.RepresentativeArray.Owner.Tests
open Compiler.ZigAir.Memory

def cell (runtimeSafety writable stack : Bool) : Allocation := ⟨8, allocationType runtimeSafety, [], writable, stack⟩
def memory (runtimeSafety writable stack : Bool) : State :=
  ⟨[(0, cell runtimeSafety writable stack)], 1, 8 + (layout runtimeSafety).bytes⟩

theorem initial_valid (runtimeSafety writable stack : Bool) : (memory runtimeSafety writable stack).valid = true := by
  cases runtimeSafety <;> cases writable <;> cases stack <;> decide

theorem header_from_declared_owner (runtimeSafety writable stack : Bool) :
    access (memory runtimeSafety writable stack) (headerAddress ⟨0, 0⟩) representativesLayout false = .ok (cell runtimeSafety writable stack) :=
  root_header_region runtimeSafety (memory runtimeSafety writable stack) 0 (cell runtimeSafety writable stack) false (initial_valid runtimeSafety writable stack)
    rfl rfl (by simp)

theorem writable_header_from_declared_owner (runtimeSafety stack : Bool) :
    access (memory runtimeSafety true stack) (headerAddress ⟨0, 0⟩) representativesLayout true = .ok (cell runtimeSafety true stack) :=
  root_header_region runtimeSafety (memory runtimeSafety true stack) 0 (cell runtimeSafety true stack) true (initial_valid runtimeSafety true stack) rfl rfl (by simp [cell])

theorem readonly_permission_is_not_upgraded (runtimeSafety : Bool) :
    access (memory runtimeSafety false true) (headerAddress ⟨0, 0⟩) representativesLayout true = .error .readOnly := by cases runtimeSafety <;> decide

def arrayCell (runtimeSafety : Bool) : Allocation := ⟨8, .array 2 (allocationType runtimeSafety), [], true, true⟩
def arrayMemory (runtimeSafety : Bool) : State := ⟨[(3, arrayCell runtimeSafety)], 4, 8 + 2 * (layout runtimeSafety).bytes⟩

theorem nonzero_owner_offset_retains_parent (runtimeSafety : Bool) :
    (arrayMemory runtimeSafety).valid = true ∧
      headerAddress ⟨3, (layout runtimeSafety).bytes⟩ = ⟨3, (layout runtimeSafety).bytes + 16⟩ ∧
      access (arrayMemory runtimeSafety) (headerAddress ⟨3, (layout runtimeSafety).bytes⟩)
        representativesLayout true = .ok (arrayCell runtimeSafety) :=
  ⟨by cases runtimeSafety <;> decide, rfl,
    header_region_access runtimeSafety (arrayMemory runtimeSafety) ⟨3, (layout runtimeSafety).bytes⟩
      (arrayCell runtimeSafety) true (by cases runtimeSafety <;> decide)⟩

theorem geometry_does_not_admit_nested_header_fields (runtimeSafety : Bool) :
    fieldPointer (memory runtimeSafety true true) (.pointer (.pointer true false (allocationType runtimeSafety)) ⟨0, 0⟩) representativesOffset = .error .unsupported ∧
      readHeader (memory runtimeSafety true true) (headerAddress ⟨0, 0⟩) = .error .unsupported := by cases runtimeSafety <;> decide

theorem nominal_header_extent_is_not_complete_admission (runtimeSafety : Bool) :
    recordView (memory runtimeSafety true true) RepresentativeArray.allocationType
      (.pointer (.pointer false false (.record "std.ArrayList(src/libevmasm/expression_classes.zig::Expression)" representativesLayout))
        (headerAddress ⟨0, 0⟩)) = .error .unsupported := by cases runtimeSafety <;> decide

theorem header_region_is_not_initialized_storage (runtimeSafety : Bool) :
    load (memory runtimeSafety true true) (.pointer (.pointer false false usize) ⟨0, representativesOffset + capacityOffset⟩) = .error .unsupported := by cases runtimeSafety <;> decide

theorem interior_owner_pointer_is_checked (runtimeSafety : Bool) :
    access (memory runtimeSafety true true) ⟨0, 8⟩ (layout runtimeSafety) false = .error .memoryValidity := by cases runtimeSafety <;> decide

theorem standalone_header_does_not_supply_whole_owner (runtimeSafety : Bool) :
    access ⟨[(0, ⟨8, RepresentativeArray.allocationType, [], true, true⟩)], 1, 32⟩
      ⟨0, 0⟩ (layout runtimeSafety) false = .error .memoryValidity := by cases runtimeSafety <;> decide

def overlapping (runtimeSafety : Bool) : State :=
  ⟨[(1, ⟨24, RepresentativeArray.allocationType, [], true, true⟩), (0, cell runtimeSafety true true)], 2, 8 + (layout runtimeSafety).bytes⟩

theorem embedded_header_is_not_a_separate_allocation (runtimeSafety : Bool) :
    (overlapping runtimeSafety).valid = false := by cases runtimeSafety <;> decide

theorem malformed_physical_regions_reject (runtimeSafety : Bool) :
    access ⟨[(0, { cell runtimeSafety true true with base := 0 })], 1, 64⟩ ⟨0, 0⟩ (layout runtimeSafety) false = .error .memoryValidity ∧
    access ⟨[(0, { cell runtimeSafety true true with base := 9 })], 1, 65⟩ ⟨0, 0⟩ (layout runtimeSafety) false = .error .memoryValidity ∧
    access ⟨[(0, { cell runtimeSafety true true with base := addressLimit - 48 })], 1, addressLimit⟩
      ⟨0, 0⟩ (layout runtimeSafety) false = .error .memoryValidity := by cases runtimeSafety <;> decide

theorem stale_owner_lifetime_rejects (runtimeSafety : Bool) :
    access (memory runtimeSafety true true) (headerAddress ⟨1, 0⟩) representativesLayout false = .error .unallocated := by cases runtimeSafety <;> decide

theorem stack_cleanup_invalidates_embedded_header (runtimeSafety : Bool) :
    access (cleanup 0 (memory runtimeSafety true true)) (headerAddress ⟨0, 0⟩) representativesLayout false = .error .unallocated ∧
      (cleanup 0 (memory runtimeSafety true true)).nextId = 1 ∧ (cleanup 0 (memory runtimeSafety true true)).nextAddress = 8 + (layout runtimeSafety).bytes := by cases runtimeSafety <;> decide

end Compiler.Extraction.RepresentativeArray.Owner.Tests
