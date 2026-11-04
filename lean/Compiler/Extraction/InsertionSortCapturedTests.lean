/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortCapturedResults
import Compiler.ZigAir.MemoryWordSwapRegionTests

namespace Compiler.Extraction.InsertionSort.CapturedTests
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open HeapTests (caller view observations expected)

def observe (budget : Nat) (items : List NodeId) : Except Heap.Fault Unit × List (Except Compiler.ZigAir.Memory.Fault Value) :=
  let (result, after) := Captured.run budget (caller items) (view items)
  (result, observations after items.length)

theorem empty : observe 160 [] = expected [] := by rfl'
theorem singleton : observe 160 [7] = expected [7] := by rfl'
theorem ordered : observe 160 [0, 1, 2, 3] = expected [0, 1, 2, 3] := by rfl'
theorem reversed : observe 160 [3, 2, 1, 0] = expected [0, 1, 2, 3] := by rfl'
theorem duplicates : observe 160 [2, 1, 2, 0, 1] = expected [0, 1, 1, 2, 2] := by rfl'
theorem unsigned : observe 160 [4294967295, 0, 2147483648, 1] = expected [0, 1, 2147483648, 4294967295] := by rfl'
theorem equal : observe 160 [9, 9, 9] = expected [9, 9, 9] := by rfl'
theorem alternating : observe 160 [5, 1, 4, 2, 3, 0] = expected [0, 1, 2, 3, 4, 5] := by rfl'

theorem allocations_advance :
    let after := (Captured.run 160 (caller [3, 2, 1]) (view [3, 2, 1])).2
    after.nextId = 5 ∧ after.nextAddress = 80 ∧ after.heap.map Prod.fst = [0, 1] := ⟨by rfl', by rfl', by rfl'⟩

def oneSwapRoom : State := { caller [3, 2, 1] with nextAddress := addressLimit - 16 }
def oneSwapAfter : State := (Captured.exchange 160 (view [3, 2, 1]) oneSwapRoom 1 0).2

theorem one_swap_room_valid : oneSwapRoom.valid = true := by decide +kernel
theorem later_exhaustion_retains_prefix : Captured.run 160 oneSwapRoom (view [3, 2, 1]) =
    (.error (.memory .outOfMemory), oneSwapAfter) := by rfl'
theorem exhausted_prefix_observations : observations oneSwapAfter 3 =
    (expected [2, 3, 1]).2 ∧ oneSwapAfter.nextId = 3 ∧ oneSwapAfter.nextAddress = addressLimit - 8 := ⟨by rfl', by rfl', by rfl'⟩

def partialState : State := (Captured.exchange 23 (view [3735928559, 305419896]) (caller [3735928559, 305419896]) 1 0).2
theorem suspension_retains_prefix : Captured.run 23 (caller [3735928559, 305419896]) (view [3735928559, 305419896]) =
    (.error .incomplete, partialState) := by rfl'
theorem suspension_keeps_partial_write : observations partialState 2 = (expected [3735928559, 305420015]).2 ∧
    partialState.heap.map Prod.fst = [2, 0, 1] := ⟨by rfl', by rfl'⟩
theorem zero_budget_is_incomplete : Captured.run 0 (caller [2, 1]) (view [2, 1]) =
    (.error .incomplete, caller [2, 1]) := by rfl'
theorem width_rejects : Captured.run 160 {} ⟨0, 0, addressLimit⟩ = (.error .indexWidth, {}) := by rfl'
theorem empty_skips_reads : Captured.run 0 {} ⟨0, 0, 0⟩ = (.ok (), {}) := by rfl'
theorem alias_rejects : Captured.exchange 160 (view [1, 2]) (caller [1, 2]) 0 0 =
    (.error (.memory .memoryValidity), caller [1, 2]) := by rfl'
theorem outside_view_rejects : Captured.exchange 160 (view [1, 2]) (caller [1, 2]) 0 2 =
    (.error (.memory .sourceBounds), caller [1, 2]) := by rfl'

theorem total_witness :
    ∃ result after values, Captured.Settles (fun budget => Captured.run budget (MemoryTests.caller 3 1) MemoryTests.view)
        (result, after) ∧
      Heap.Related MemoryTests.view after values ∧ values.Perm [3, 1] ∧ HeapFrame MemoryTests.view (MemoryTests.caller 3 1) after ∧
      ((result = .ok () ∧ values = sortIds [3, 1]) ∨ result = .error (.memory .outOfMemory)) :=
  Captured.run_refines _ _ _ ⟨MemoryTests.valid_caller, MemoryTests.writable_caller, MemoryTests.represented_caller⟩

theorem every_success (budget : Nat) (after : State)
    (done : Captured.run budget (MemoryTests.caller 3 1) MemoryTests.view = (.ok (), after)) :
    Heap.Related MemoryTests.view after (sortIds [3, 1]) ∧ HeapFrame MemoryTests.view (MemoryTests.caller 3 1) after := by
  rcases Captured.run_result budget MemoryTests.view (MemoryTests.caller 3 1) after [3, 1] (.ok ())
      ⟨MemoryTests.valid_caller, MemoryTests.writable_caller, MemoryTests.represented_caller⟩ done with
    incomplete | ⟨values, related, _, frame, effect⟩
  · cases incomplete
  · rcases effect with ⟨_, rfl⟩ | failed
    · exact ⟨related, frame⟩
    · cases failed

end Compiler.Extraction.InsertionSort.CapturedTests
