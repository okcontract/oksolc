/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayCopyProofs
import Compiler.Extraction.RepresentativeArrayAllocationTests

namespace Compiler.Extraction.RepresentativeArray.Copy.Tests
open Compiler.ZigAir.Memory

def targetCell : Allocation := RegionAllocation.cell (Backing.type 5) 640
def before : State := RegionAllocation.extend Append.Tests.after (Backing.type 5) 160 640
def firstCells : Cells := [(28, Expression.Tests.sequence), (24, Expression.Tests.id),
  (16, .scalar (.int false 64 2)), (8, FieldTests.argumentPointer), (0, Expression.Tests.item)]
def copiedCells : Cells := [(60, FieldTests.sequence), (56, FieldTests.id), (48, .scalar (.int false 64 2)),
  (40, FieldTests.argumentPointer), (32, Expression.Tests.item)] ++ firstCells
def firstAfter : State := { before with heap := before.heap.replace 4 {targetCell with cells := firstCells} }
def after : State := { before with heap := before.heap.replace 4 {targetCell with cells := copiedCells} }

theorem initial_valid : before.valid = true := by decide

theorem initialized_source : ∀ index, index < 2 → ∀ slot ∈ expressionSlots,
    ∃ value, Expression.readField before false ⟨2, index * 32⟩ slot.1 = .ok value := by
  intro index inside slot member
  have choice : index = 0 ∨ index = 1 := by omega
  rcases slot with ⟨offset, type⟩
  simp only [expressionSlots, Expression.allocationType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases choice with rfl | rfl
  all_goals exact ⟨_, rfl⟩

theorem first_row : fields expressionSlots ⟨2, 0⟩ ⟨4, 0⟩ before = (.ok (), firstAfter) := by decide

theorem second_row : fields expressionSlots ⟨2, 32⟩ ⟨4, 32⟩ firstAfter = (.ok (), after) := by decide

theorem actual_complete_copy : run before 2 4 2 = (.ok (), after) := by
  simp only [run, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 4 by decide, ↓reduceIte, copyFrom,
    Nat.zero_mul, Nat.reduceAdd, Nat.reduceMul, first_row, second_row]

theorem copy_without_success_premise : ∃ finalState, run before 2 4 2 = (.ok (), finalState) ∧ finalState.valid = true ∧
    before.heap.RetainsShape finalState.heap ∧ finalState.nextId = before.nextId ∧ finalState.nextAddress = before.nextAddress ∧
    (∀ id, id ≠ 4 → finalState.heap.lookup id = before.heap.lookup id) ∧
    (∀ index, index < 2 → ∀ slot ∈ expressionSlots, Expression.readField finalState false ⟨4, index * 32⟩ slot.1 =
      Expression.readField before false ⟨2, index * 32⟩ slot.1) :=
  run_verified before 2 4 5 2 targetCell initial_valid (by decide) rfl rfl (by decide) (Or.inr (by decide)) initialized_source

theorem complete_readback_from_copy (index : Nat) (inside : index < 2) :
    Expression.readFields after false ⟨4, index * 32⟩ = Expression.readFields before false ⟨2, index * 32⟩ := by
  obtain ⟨finalState, executed, _, _, _, _, _, copied⟩ := copy_without_success_premise
  have same : finalState = after := (Prod.mk.inj (executed.symm.trans actual_complete_copy)).2
  subst finalState
  exact readFields_eq_of_slots before after _ _ (copied index inside)

theorem untouched_spare_fields (length index : Nat) (outside : length ≤ index) (slot : Nat × Ty)
    (declared : slot ∈ expressionSlots) :
    Expression.readField (run before 2 4 length).2 false ⟨4, index * 32⟩ slot.1 =
      Expression.readField before false ⟨4, index * 32⟩ slot.1 :=
  run_read_frame before 2 4 length 4 index slot.1 slot.2 declared (Or.inr outside)

theorem distinct_rows_and_slice_identity : Expression.readFields after false ⟨4, 0⟩ =
    .ok [Expression.Tests.item, Expression.Tests.arguments, Expression.Tests.id, Expression.Tests.sequence] ∧
    Expression.readFields after false ⟨4, 32⟩ =
    .ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence] := by decide

theorem untouched_source_header_and_spare_capacity : after.heap.lookup 2 = before.heap.lookup 2 ∧
    after.heap.lookup 3 = before.heap.lookup 3 ∧ after.heap.lookup 0 = before.heap.lookup 0 ∧
    Expression.readFields after false ⟨4, 64⟩ = .error .uninitialized ∧
    readHeader after ⟨3, 0⟩ = .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 3)) := by decide

theorem no_allocation_or_release : after.nextId = 5 ∧ after.nextAddress = 800 ∧ after.valid = true ∧
    (cleanup before.nextId after).heap.lookup 4 = after.heap.lookup 4 := by decide

theorem copied_offset_borrow :
    (do let arguments ← Expression.readField after false ⟨4, 32⟩ Expression.argumentsOffset
        let first ← sliceElementPointer after arguments 0
        let second ← sliceElementPointer after arguments 1
        .ok [← load after first, ← load after second]) = .ok [.scalar (.int false 32 99), .scalar (.int false 32 1)] := by decide

theorem parent_contents : WordArray.Represents before ⟨1, 1, 2⟩ [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have choice : index = 0 ∨ index = 1 := by simp at inside; omega
  rcases choice with rfl | rfl <;> rfl'

theorem every_length_preserves_parent (length : Nat) :
    (run before 2 4 length).2.heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧
    WordArray.Represents (run before 2 4 length).2 ⟨1, 1, 2⟩ [99, 1] :=
  run_parent_borrow before 2 4 5 length targetCell ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation
    initial_valid (by decide) rfl (by decide) rfl parent_contents

theorem spare_row : fields expressionSlots ⟨2, 64⟩ ⟨4, 64⟩ after = (.error .uninitialized, after) := by decide

theorem copying_spare_source_rejects_after_prefix : run before 2 4 3 = (.error .uninitialized, after) := by
  simp only [run, show (3 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 4 by decide, ↓reduceIte, copyFrom,
    Nat.zero_mul, Nat.reduceAdd, Nat.reduceMul, first_row, second_row, spare_row]

def shortTarget : State := {before with heap := before.heap.replace 4 {targetCell with type := Backing.type 1} }
def shortAfter : State := {shortTarget with heap := shortTarget.heap.replace 4 {targetCell with type := Backing.type 1, cells := firstCells} }
theorem short_target_retains_first_descriptor : shortTarget.valid = true ∧
    run shortTarget 2 4 2 = (.error .memoryValidity, shortAfter) := by decide

def partialSource : Allocation := {FieldTests.data with cells := Append.Tests.newCells.filter (fun entry => entry.1 != 48)}
def partialState : State := {before with heap := before.heap.replace 2 partialSource}
def partialFirst : State := {partialState with heap := partialState.heap.replace 4 {targetCell with cells := firstCells} }
def partialAfter : State := {partialState with heap := partialState.heap.replace 4 {targetCell with cells := (32, Expression.Tests.item) :: firstCells} }
theorem partial_first_row : fields expressionSlots ⟨2, 0⟩ ⟨4, 0⟩ partialState = (.ok (), partialFirst) := by decide

theorem partial_second_row : fields expressionSlots ⟨2, 32⟩ ⟨4, 32⟩ partialFirst = (.error .uninitialized, partialAfter) := by decide

theorem partial_slice_retains_item_and_prior_descriptor : partialState.valid = true ∧
    run partialState 2 4 2 = (.error .uninitialized, partialAfter) ∧
    Expression.readField partialAfter false ⟨4, 32⟩ Expression.itemOffset = .ok Expression.Tests.item ∧
    Expression.readField partialAfter false ⟨4, 32⟩ Expression.argumentsOffset = .error .uninitialized := by
  refine ⟨by decide, ?_, by rfl, by rfl⟩
  simp only [run, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 4 by decide, ↓reduceIte, copyFrom,
    Nat.zero_mul, Nat.reduceAdd, Nat.reduceMul, partial_first_row, partial_second_row]

def readonlyTarget : State := {before with heap := before.heap.replace 4 {targetCell with writable := false} }
theorem readonly_target_rejects_without_writes : run readonlyTarget 2 4 2 = (.error .readOnly, readonlyTarget) := by decide

def readonlySource : State := {before with heap := before.heap.replace 2 {FieldTests.data with cells := Append.Tests.newCells, writable := false} }
def readonlyFirst : State := {readonlySource with heap := readonlySource.heap.replace 4 {targetCell with cells := firstCells} }
def readonlyAfter : State := {readonlySource with heap := readonlySource.heap.replace 4 {targetCell with cells := copiedCells} }
theorem readonly_first_row : fields expressionSlots ⟨2, 0⟩ ⟨4, 0⟩ readonlySource = (.ok (), readonlyFirst) := by decide

theorem readonly_second_row : fields expressionSlots ⟨2, 32⟩ ⟨4, 32⟩ readonlyFirst = (.ok (), readonlyAfter) := by decide

theorem readonly_source_is_sufficient : readonlySource.valid = true ∧ run readonlySource 2 4 2 = (.ok (), readonlyAfter) := by
  refine ⟨by decide, ?_⟩
  simp only [run, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 4 by decide, ↓reduceIte, copyFrom,
    Nat.zero_mul, Nat.reduceAdd, Nat.reduceMul, readonly_first_row, readonly_second_row]

theorem overlapping_copy_rejects : run before 2 2 1 = (.error .memoryValidity, before) := by decide

theorem empty_sentinels_are_not_dereferenced : run before 99 99 0 = (.ok (), before) ∧
    run before 4 4 0 = (.ok (), before) := by decide

theorem stale_source_or_target_rejects : run (erase before 2) 2 4 1 = (.error .unallocated, erase before 2) ∧
    run (erase before 4) 2 4 1 = (.error .unallocated, erase before 4) := by decide

theorem source_extent_rejects_separately : copyFrom 2 4 1 3 before = (.error .memoryValidity, before) := by decide

end Compiler.Extraction.RepresentativeArray.Copy.Tests
