/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemorySliceInvocation

namespace Compiler.ZigAir.MemorySliceInvocation.Tests
open Memory MemoryAir Memory.WordArray GeneratedMemory
open MemoryFill (size)

deriving instance DecidableEq for Except

def words : List (BitVec 32) := [0, 4294967295, 305419896, 3735928559, 2147483648, 1, 3131961357, 2147483647]
def cell : Allocation := ⟨16, .array 8 word, words.zipIdx.map (fun (value, index) => (index * 4, number value)), true, false⟩
def caller : State := ⟨[(0, cell)], 1, 48⟩
def view (first length : Nat) : View := ⟨0, first, length⟩
def observe (first length index : Nat) : Except Fault Value × State :=
  fn_slice_element.run (arguments (view first length) index) caller

theorem valid_caller : caller.valid = true := by decide +kernel
theorem case_0 : observe 0 1 0 =
    (.ok (.pointer (.pointer true false word) ⟨0, 0⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem case_1 : observe 0 8 0 =
    (.ok (.pointer (.pointer true false word) ⟨0, 0⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem case_2 : observe 0 8 7 =
    (.ok (.pointer (.pointer true false word) ⟨0, 28⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem case_3 : observe 1 2 0 =
    (.ok (.pointer (.pointer true false word) ⟨0, 4⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem case_4 : observe 1 2 1 =
    (.ok (.pointer (.pointer true false word) ⟨0, 8⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem case_5 : observe 3 4 2 =
    (.ok (.pointer (.pointer true false word) ⟨0, 20⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem case_6 : observe 6 2 1 =
    (.ok (.pointer (.pointer true false word) ⟨0, 28⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem case_7 : observe 7 1 0 =
    (.ok (.pointer (.pointer true false word) ⟨0, 28⟩), ⟨caller.heap, 3, 72⟩) := by decide +kernel

theorem exact_slice_bound : observe 1 2 2 = (.error .sourceBounds, ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem empty_slice : observe 1 0 0 = (.error .sourceBounds, ⟨caller.heap, 3, 72⟩) := by decide +kernel
theorem allocation_extent : observe 1 8 0 = (.error .memoryValidity, ⟨caller.heap, 2, 56⟩) := by decide +kernel

def exhausted (remaining : Nat) : State := { caller with nextAddress := addressLimit - remaining }
theorem valid_first_exhausted : (exhausted 8).valid = true := by decide +kernel
theorem valid_second_exhausted : (exhausted 24).valid = true := by decide +kernel
theorem first_allocation_exhausted : fn_slice_element.run (arguments (view 1 2) 1) (exhausted 8) =
    (.error .outOfMemory, exhausted 8) := by decide +kernel
theorem second_allocation_exhausted : fn_slice_element.run (arguments (view 1 2) 1) (exhausted 24) =
    (.error .outOfMemory, ⟨caller.heap, 2, addressLimit - 16⟩) := by decide +kernel

def uninitialized : State := { caller with heap := [(0, { cell with cells := [] })] }
theorem uninitialized_address : fn_slice_element.run (arguments (view 1 2) 1) uninitialized =
    (.ok ((view 1 2).pointer 1), ⟨uninitialized.heap, 3, 72⟩) := by decide +kernel

theorem dead_slice : sliceElementPointer {} (view 1 2).slice 0 = .error .unallocated := by decide +kernel
theorem oversized_slice : sliceElementPointer caller (.slice (.slice true word) ⟨0, 0⟩ addressLimit) 0 =
    .error .malformed := by decide +kernel
theorem zero_sized_child : sliceElementPointer caller (.slice (.slice true (.scalar .unit)) ⟨0, 0⟩ 1) 0 =
    .error .unsupported := by decide +kernel

theorem total_invocation_witness : ∃ result after,
    fn_slice_element.run (arguments (view 1 2) 1) caller = (result, after) ∧ after.valid = true ∧ after.heap = caller.heap ∧
      (result = .ok ((view 1 2).pointer 1) ∨ result = .error .outOfMemory) := by
  exact run_preserves caller (view 1 2) 1 valid_caller
    ⟨8, cell, rfl, rfl, rfl, by decide⟩ (by decide)

end Compiler.ZigAir.MemorySliceInvocation.Tests
