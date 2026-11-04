/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortHeapProofs
import Compiler.Extraction.InsertionSortMemoryTests

namespace Compiler.Extraction.InsertionSort.HeapTests
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

def caller (items : List NodeId) : State :=
  let words := [3735928559] ++ items ++ [3131961357]
  let cell : Allocation := ⟨16, .array words.length word,
    words.zipIdx.map (fun (value, index) => (index * 4, number value)), true, false⟩
  let other := 32 + words.length * 4
  ⟨[(0, cell), (1, ⟨other, word, [(0, number 99)], true, false⟩)], 2, other + 4⟩

def view (items : List NodeId) : View := ⟨0, 1, items.length⟩

def observations (state : State) (length : Nat) : List (Except Compiler.ZigAir.Memory.Fault Value) :=
  ((List.range (length + 2)).map (fun index => load state (.pointer (.pointer true false word) ⟨0, index * 4⟩))) ++
    [load state (.pointer (.pointer true false word) ⟨1, 0⟩)]

def sortObservation (items : List NodeId) : Except Heap.Fault Unit × List (Except Compiler.ZigAir.Memory.Fault Value) :=
  let (result, after) := Heap.run (caller items) (view items)
  (result, observations after items.length)

def expected (items : List NodeId) : Except Heap.Fault Unit × List (Except Compiler.ZigAir.Memory.Fault Value) :=
  (.ok (), ([3735928559] ++ items ++ [3131961357, 99]).map (fun value => .ok (number value)))

theorem empty : sortObservation [] = expected [] := by decide +kernel
theorem singleton : sortObservation [7] = expected [7] := by decide +kernel
theorem ordered : sortObservation [0, 1, 2, 3] = expected [0, 1, 2, 3] := by decide +kernel
theorem reversed : sortObservation [3, 2, 1, 0] = expected [0, 1, 2, 3] := by decide +kernel
theorem duplicates : sortObservation [2, 1, 2, 0, 1] = expected [0, 1, 1, 2, 2] := by decide +kernel
theorem unsigned : sortObservation [4294967295, 0, 2147483648, 1] = expected [0, 1, 2147483648, 4294967295] := by decide +kernel
theorem equal : sortObservation [9, 9, 9] = expected [9, 9, 9] := by decide +kernel
theorem alternating : sortObservation [5, 1, 4, 2, 3, 0] = expected [0, 1, 2, 3, 4, 5] := by decide +kernel

/-- The universal theorem's preconditions have a concrete inhabitant. -/
theorem full_run_witness :
    ∃ after, Heap.run (MemoryTests.caller 3 1) MemoryTests.view = (.ok (), after) ∧
      Heap.Related MemoryTests.view after (sortIds [3, 1]) ∧ Frame MemoryTests.view (MemoryTests.caller 3 1) after :=
  Heap.run_refines _ _ _ ⟨MemoryTests.valid_caller, MemoryTests.writable_caller, MemoryTests.represented_caller⟩

theorem readonly_rejects : Heap.run MemoryTests.readonly MemoryTests.view =
    (.error (.memory .readOnly), MemoryTests.readonly) := by decide +kernel
theorem dead_rejects : Heap.run {} MemoryTests.view = (.error (.memory .unallocated), {}) := by decide +kernel
theorem width_rejects : Heap.run {} ⟨0, 0, addressLimit⟩ = (.error .indexWidth, {}) := by decide +kernel
theorem empty_skips_reads : Heap.run {} ⟨0, 0, 0⟩ = (.ok (), {}) := by decide +kernel

/-- A later uninitialized read preserves the earlier completed exchange. -/
def partialCaller : State :=
  ⟨[(0, ⟨16, .array 3 word, [(0, number 3), (4, number 2)], true, false⟩)], 1, 28⟩
def partialAfter : State :=
  (WordArray.exchange partialCaller ⟨0, 0, 3⟩ 1 0).2

theorem partial_valid : partialCaller.valid = true := by decide +kernel
theorem partial_keeps_exchange : Heap.run partialCaller ⟨0, 0, 3⟩ =
    (.error (.memory .uninitialized), partialAfter) := by decide +kernel
theorem partial_values :
    [load partialAfter (.pointer (.pointer true false word) ⟨0, 0⟩),
     load partialAfter (.pointer (.pointer true false word) ⟨0, 4⟩)] =
      [.ok (number 2), .ok (number 3)] := by decide +kernel

theorem exhausted_keeps_exchange :
    passesUsing (Heap.operations ⟨0, 0, 3⟩) 1 3 1 partialCaller =
      (.error .incomplete, partialAfter) := by decide +kernel

end Compiler.Extraction.InsertionSort.HeapTests
