/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryPreparation
import Compiler.ZigAir.MemoryWordCopyTests
import Compiler.Extraction.InsertionSortCopiedTests
import Compiler.Extraction.ArgumentMemoryTests
import Compiler.Extraction.NormalizationPreparedMemoryTests

namespace Compiler.Extraction.Memory.Arguments.PreparationTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray

def source : View := ⟨0, 0, 3⟩
-- This provisional payload supplies the registered extent. Its contents are
-- deliberately not represented before initialization and cannot be read via Related.
def destination : ArgumentSlice := ⟨1, [0, 0, 0]⟩
def logical : Heap := fun id =>
  if id = 1 then some ⟨7, .arguments destination.items⟩
  else if id = 2 then some ⟨11, .arguments [99]⟩ else none
def targetCell : Compiler.ZigAir.Memory.Allocation := ⟨32, .array 3 word, [], true, false⟩
def otherCell : Compiler.ZigAir.Memory.Allocation := ⟨48, .array 1 word, [(0, number 99)], true, false⟩
def before : Compiler.ZigAir.Memory.State :=
  ⟨[(0, Compiler.ZigAir.Memory.WordCopy.Tests.sourceCell), (1, targetCell), (2, otherCell)], 3, 52⟩
def after : Compiler.ZigAir.Memory.State := (Copied.run 160 before source (view destination)).2
def projected : Heap := write logical 1 (some ⟨7, .arguments [1, 2, 3]⟩)

theorem update_witness : Updated logical projected 1 [1, 2, 3] := ⟨7, destination.items, rfl, rfl, rfl⟩
theorem wrong_allocator_not_updated : ¬Updated logical (write logical 1 (some ⟨8, .arguments [1, 2, 3]⟩)) 1 [1, 2, 3] := by
  intro updated
  have owner := updated_owner _ _ 1 7 destination.items [1, 2, 3] updated rfl
  simp [write] at owner
theorem wrong_extent_not_updated : ¬Updated logical (write logical 1 (some ⟨7, .arguments [1, 2]⟩)) 1 [1, 2] := by
  intro updated
  have length := updated_length _ _ 1 7 destination.items [1, 2] updated rfl
  contradiction

theorem valid : before.valid = true := by decide +kernel
theorem owned : Owned before 1 3 := ⟨targetCell, by rfl', rfl, rfl, rfl⟩
theorem source_represented : Represents before source [3, 1, 2] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by simp only [List.length_cons, List.length_nil] at inside; omega
  rcases cases with rfl | rfl | rfl <;> rfl'
theorem others_related : Related (write logical 1 none) before := by
  intro allocator id items _ stored
  by_cases one : id = 1
  · simp [write, one] at stored
  · by_cases two : id = 2
    · subst id
      have same : 11 = allocator ∧ [99] = items := by simpa [write, logical] using stored
      rcases same with ⟨rfl, rfl⟩
      refine ⟨⟨otherCell, by rfl', rfl, rfl, rfl⟩, rfl, ?_⟩
      intro index inside
      have only : index = 0 := by simp only [List.length_cons, List.length_nil] at inside; omega
      subst index
      rfl'
    · simp [write, logical, one, two] at stored

theorem provisional_contents_uninitialized :
    Compiler.ZigAir.Memory.load before ((view destination).pointer 0) = .error .uninitialized := by rfl'
theorem provisional_not_related : ¬Related logical before := by
  intro assumed
  have loaded := (related_read logical before 7 destination assumed (Or.inr rfl) 0 (by decide)).2
  contradiction

theorem all_budgets_owned (budget : Nat) : Owned (Copied.run budget before source (view destination)).2 1 3 :=
  copied_owned budget before source (view destination) 1 3 valid owned
theorem all_budgets_valid (budget : Nat) : (Copied.run budget before source (view destination)).2.valid = true :=
  (Copied.run_storage budget before source (view destination) valid).1
theorem complete : Copied.run 160 before source (view destination) = (.ok (), after) := by rfl'
theorem complete_values :
    (List.range 3).map (fun index => Compiler.ZigAir.Memory.load after ((view destination).pointer index)) =
      [1, 2, 3].map (fun value => .ok (number value)) ∧
    Compiler.ZigAir.Memory.load after ((⟨2, 0, 1⟩ : View).pointer 0) = .ok (number 99) := ⟨by rfl', by rfl'⟩

theorem settles_with_projection : ∃ result final values heap, Captured.Settles
    (fun budget => Copied.run budget before source (view destination)) (result, final) ∧
    Updated logical heap 1 values ∧ Related heap final ∧ final.valid = true ∧ values.Perm [3, 1, 2] ∧
    Represents final source [3, 1, 2] ∧ HeapFrame (view destination) before final ∧
    SliceValid 7 heap ⟨1, values⟩ ∧
    ((result = .ok () ∧ values = sortIds [3, 1, 2]) ∨ result = .error (.memory .outOfMemory)) :=
  copied_refines logical before 7 source destination [3, 1, 2] valid owned rfl others_related source_represented rfl (by decide)

theorem every_budget_classified (budget : Nat) :
    let observed := Copied.run budget before source (view destination)
    observed.1 = .error .incomplete ∨ ∃ values heap,
      Updated logical heap 1 values ∧ Related heap observed.2 ∧ observed.2.valid = true ∧ values.Perm [3, 1, 2] ∧
      Represents observed.2 source [3, 1, 2] ∧ HeapFrame (view destination) before observed.2 ∧
      SliceValid 7 heap ⟨1, values⟩ ∧
      ((observed.1 = .ok () ∧ values = sortIds [3, 1, 2]) ∨ observed.1 = .error (.memory .outOfMemory)) := by
  exact copied_result budget logical before _ 7 source destination [3, 1, 2] _ valid owned rfl
    others_related source_represented rfl (by decide) rfl

theorem complete_related : Related projected after := by
  have copied := Copied.run_result 160 before after source (view destination) [3, 1, 2] (.ok ()) valid
    (owned_writable before 1 3 owned) source_represented rfl (by decide) complete
  rcases copied with impossible | ⟨values, connected, _, _, frame, effect⟩
  · contradiction
  · rcases effect with ⟨_, sorted⟩ | impossible
    · have valuesEq : values = [1, 2, 3] := sorted.trans (by rfl')
      subst values
      exact related_publish logical before after 7 (view destination) [1, 2, 3] others_related frame
        (all_budgets_owned 160) rfl connected.values
    · contradiction

theorem release_after_preparation : release projected after 7 ⟨1, [1, 2, 3]⟩ =
    .ok (write projected 1 none, Compiler.ZigAir.Memory.erase after 1) := by
  exact release_effects projected after 7 ⟨1, [1, 2, 3]⟩ (all_budgets_valid 160) (by decide)
    (write_same logical 1 (some ⟨7, .arguments [1, 2, 3]⟩)) (all_budgets_owned 160)
theorem release_preserves_relation : ∃ heap final, release projected after 7 ⟨1, [1, 2, 3]⟩ = .ok (heap, final) ∧
    ReleasePost projected after 7 ⟨1, [1, 2, 3]⟩ heap final :=
  release_refines projected after 7 ⟨1, [1, 2, 3]⟩ (all_budgets_valid 160) complete_related (Or.inr (by rfl'))
theorem release_retains_reached_counters :
    (Compiler.ZigAir.Memory.erase after 1).nextId = 5 ∧
    (Compiler.ZigAir.Memory.erase after 1).nextAddress = 72 := ⟨by rfl', by rfl'⟩
theorem released_alias_rejected :
    Compiler.ZigAir.Memory.load (Compiler.ZigAir.Memory.erase after 1) ((view destination).pointer 2) = .error .unallocated := by rfl'

theorem zero_budget_is_incomplete : (Copied.run 0 before source (view destination)).1 = .error .incomplete := by rfl'
theorem suspended_owned : Owned (Copied.run 35 before source (view destination)).2 1 3 := all_budgets_owned 35
def exhausted : Compiler.ZigAir.Memory.State := { before with nextAddress := Compiler.ZigAir.Memory.addressLimit - 8 }
theorem exhausted_valid : exhausted.valid = true := by decide +kernel
theorem exhaustion_is_fault : (Copied.run 160 exhausted source (view destination)).1 = .error (.memory .outOfMemory) := by rfl'
theorem exhaustion_keeps_owned : Owned (Copied.run 160 exhausted source (view destination)).2 1 3 :=
  copied_owned 160 exhausted source (view destination) 1 3 exhausted_valid owned
theorem failed_copy_keeps_owned :
    Owned (Copied.run 160 Compiler.ZigAir.Memory.WordCopy.Tests.incompleteSource
      Compiler.ZigAir.Memory.WordCopy.Tests.source Compiler.ZigAir.Memory.WordCopy.Tests.target).2 1 5 :=
  copied_owned 160 _ _ _ 1 5 Compiler.ZigAir.Memory.WordCopy.Tests.incomplete_source_valid
    ⟨Compiler.ZigAir.Memory.WordCopy.Tests.targetCell, by rfl', rfl, rfl, rfl⟩

end Compiler.Extraction.Memory.Arguments.PreparationTests
