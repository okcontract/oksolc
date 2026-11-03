/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortCopied
import Compiler.Extraction.InsertionSortCapturedTests
import Compiler.ZigAir.MemoryWordCopyTests

namespace Compiler.Extraction.InsertionSort.CopiedTests
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

/-- Separate readonly source and uninitialized destination, each with sentinels.
The unrelated allocation is a model-only framing observation. -/
def caller (items : List NodeId) : State :=
  let words := [3735928559] ++ items ++ [3131961357]
  let targetBase := 32 + words.length * 4
  let otherBase := targetBase + words.length * 4 + 16
  ⟨[(0, ⟨16, .array words.length word, words.zipIdx.map (fun (value, index) => (index * 4, number value)), false, false⟩),
    (1, ⟨targetBase, .array words.length word, [(0, number 3735928559), ((items.length + 1) * 4, number 3131961357)], true, false⟩),
    (2, ⟨otherBase, word, [(0, number 99)], true, false⟩)], 3, otherBase + 4⟩
def source (items : List NodeId) : View := ⟨0, 1, items.length⟩
def target (items : List NodeId) : View := ⟨1, 1, items.length⟩
def observations (state : State) (length : Nat) : List (Except Compiler.ZigAir.Memory.Fault Value) :=
  [0, 1].flatMap (fun allocation => (List.range (length + 2)).map (fun index => load state ((⟨allocation, 0, length + 2⟩ : View).pointer index))) ++
  [load state (.pointer (.pointer true false word) ⟨2, 0⟩)]
def observe (budget : Nat) (items : List NodeId) : Except Heap.Fault Unit × List (Except Compiler.ZigAir.Memory.Fault Value) :=
  let (result, after) := Copied.run budget (caller items) (source items) (target items)
  (result, observations after items.length)
def expected (items sorted : List NodeId) : Except Heap.Fault Unit × List (Except Compiler.ZigAir.Memory.Fault Value) :=
  (.ok (), ([3735928559] ++ items ++ [3131961357, 3735928559] ++ sorted ++ [3131961357, 99]).map (fun value => .ok (number value)))

theorem empty : observe 160 [] = expected [] [] := by rfl'
theorem singleton : observe 160 [7] = expected [7] [7] := by rfl'
theorem ordered : observe 160 [0, 1, 2, 3] = expected [0, 1, 2, 3] [0, 1, 2, 3] := by rfl'
theorem reversed : observe 160 [3, 2, 1, 0] = expected [3, 2, 1, 0] [0, 1, 2, 3] := by rfl'
theorem duplicates : observe 160 [2, 1, 2, 0, 1] = expected [2, 1, 2, 0, 1] [0, 1, 1, 2, 2] := by rfl'
theorem unsigned : observe 160 [4294967295, 0, 2147483648, 1] = expected [4294967295, 0, 2147483648, 1] [0, 1, 2147483648, 4294967295] := by rfl'
theorem equal : observe 160 [9, 9, 9] = expected [9, 9, 9] [9, 9, 9] := by rfl'
theorem alternating : observe 160 [5, 1, 4, 2, 3, 0] = expected [5, 1, 4, 2, 3, 0] [0, 1, 2, 3, 4, 5] := by rfl'

open WordCopy.Tests (valid_caller writable_target represented_source)

theorem total_witness :
    ∃ result after values, Captured.Settles (fun budget => Copied.run budget WordCopy.Tests.caller WordCopy.Tests.source WordCopy.Tests.target)
        (result, after) ∧
      Heap.Related WordCopy.Tests.target after values ∧ values.Perm [3, 1, 2] ∧ Represents after WordCopy.Tests.source [3, 1, 2] ∧
      HeapFrame WordCopy.Tests.target WordCopy.Tests.caller after ∧
      ((result = .ok () ∧ values = sortIds [3, 1, 2]) ∨ result = .error (.memory .outOfMemory)) :=
  Copied.run_refines _ _ _ _ valid_caller writable_target represented_source rfl (by decide)

theorem every_success (budget : Nat) (after : State)
    (done : Copied.run budget WordCopy.Tests.caller WordCopy.Tests.source WordCopy.Tests.target = (.ok (), after)) :
    Heap.Related WordCopy.Tests.target after (sortIds [3, 1, 2]) ∧ Represents after WordCopy.Tests.source [3, 1, 2] ∧
      HeapFrame WordCopy.Tests.target WordCopy.Tests.caller after := by
  rcases Copied.run_result budget _ after _ _ [3, 1, 2] (.ok ()) valid_caller writable_target represented_source rfl (by decide) done with
    incomplete | ⟨values, related, _, preserved, frame, effect⟩
  · cases incomplete
  · rcases effect with ⟨_, rfl⟩ | failed
    · exact ⟨related, preserved, frame⟩
    · cases failed

theorem zero_budget_keeps_copy : Copied.run 0 WordCopy.Tests.caller WordCopy.Tests.source WordCopy.Tests.target =
    (.error .incomplete, WordCopy.Tests.copied) := by rfl'
theorem failed_copy_keeps_prefix : Copied.run 160 WordCopy.Tests.incompleteSource WordCopy.Tests.source WordCopy.Tests.target =
    (.error (.memory .uninitialized), WordCopy.Tests.prefixState) := by rfl'
theorem overlap_skips_sort : Copied.run 160 WordCopy.Tests.caller WordCopy.Tests.source WordCopy.Tests.source =
    (.error (.memory .memoryValidity), WordCopy.Tests.caller) := by rfl'

def oneSwapRoom : State := { WordCopy.Tests.caller with nextAddress := addressLimit - 16 }
def prefixState : State := (Captured.exchange 160 WordCopy.Tests.target (WordCopy.copy oneSwapRoom WordCopy.Tests.source WordCopy.Tests.target).2 1 0).2

theorem one_swap_room_valid : oneSwapRoom.valid = true := by decide +kernel
theorem exhaustion_keeps_copy_and_swap : Copied.run 160 oneSwapRoom WordCopy.Tests.source WordCopy.Tests.target =
    (.error (.memory .outOfMemory), prefixState) := by rfl'
theorem exhaustion_observations : WordCopy.Tests.observations prefixState =
    [3, 1, 2, 3735928559, 1, 3, 2, 3131961357, 99].map (fun value => .ok (number value)) := by rfl'

def partialState : State := (Captured.exchange 23 (target [3735928559, 305419896])
  (WordCopy.copy (caller [3735928559, 305419896]) (source [3735928559, 305419896]) (target [3735928559, 305419896])).2 1 0).2
theorem suspension_keeps_copied_partial_swap : Copied.run 23 (caller [3735928559, 305419896])
    (source [3735928559, 305419896]) (target [3735928559, 305419896]) = (.error .incomplete, partialState) := by rfl'
def partialObservationState : State :=
  ⟨(3, ⟨88, usize, [(0, .scalar (.int false 64 0))], true, true⟩) ::
    (caller [3735928559, 305419896]).heap.replace 1
      ⟨48, .array 4 word, [(8, number 305420015), (4, number 3735928559),
        (0, number 3735928559), (12, number 3131961357)], true, false⟩, 4, 96⟩

theorem suspension_state : partialState = partialObservationState := by rfl'
theorem suspension_observations : observations partialState 2 = (expected [3735928559, 305419896] [3735928559, 305420015]).2 ∧
    partialState.heap.map Prod.fst = [3, 0, 1, 2] := by
  constructor
  · exact (congrArg (fun state => observations state 2) suspension_state).trans (by rfl')
  · exact (congrArg (fun state => state.heap.map Prod.fst) suspension_state).trans (by rfl')

/-- Source and destination can be disjoint slices of one writable allocation. -/
def sharedTarget : View := ⟨0, 3, 3⟩
def sharedAfter : State :=
  ⟨[(0, ⟨16, .array 6 word, [(16, number 2), (20, number 3), (12, number 1),
    (0, number 3), (4, number 1), (8, number 2)], true, false⟩)], 3, 56⟩
theorem shared_run : Copied.run 160 WordCopy.Tests.shared WordCopy.Tests.source sharedTarget = (.ok (), sharedAfter) := by rfl'
theorem same_allocation_source_preserved :
    let (result, after) := Copied.run 160 WordCopy.Tests.shared WordCopy.Tests.source sharedTarget
    result = .ok () ∧ (List.range 6).map (fun index => load after (WordCopy.Tests.source.pointer index)) =
      [3, 1, 2, 1, 2, 3].map (fun value => .ok (number value)) := by
  rw [shared_run]
  exact ⟨rfl, by rfl'⟩

end Compiler.Extraction.InsertionSort.CopiedTests
