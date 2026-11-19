/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativePublicationProofs
import Compiler.Extraction.RepresentativeArrayCopyTests

namespace Compiler.Extraction.RepresentativeArray.Publication.Tests
open Compiler.ZigAir.Memory

-- This suffix receives evaluated inputs. An intentionally absent backing
-- demonstrates that publishing its address supplies no allocation or ownership.
def data : Address := ⟨99, 64⟩
def before (runtimeSafety stack : Bool) : State := Owner.FieldTests.after runtimeSafety stack
def pointerCells : Cells := Owner.FieldTests.completedCells.set 16 (.pointer pointerType data)
def finalCells : Cells := pointerCells.set 32 (.scalar (.int false 64 5))
def middle (runtimeSafety stack : Bool) : State := {before runtimeSafety stack with
  heap := (before runtimeSafety stack).heap.replace 3 (Owner.FieldTests.cell runtimeSafety true stack pointerCells)}
def after (runtimeSafety stack : Bool) : State := {before runtimeSafety stack with
  heap := (before runtimeSafety stack).heap.replace 3 (Owner.FieldTests.cell runtimeSafety true stack finalCells)}

theorem initial_valid (runtimeSafety stack : Bool) : (before runtimeSafety stack).valid = true :=
  (Owner.FieldTests.readonly_readback_from_assignment runtimeSafety stack).2

theorem pointer_assignment (runtimeSafety stack : Bool) :
    write .itemsPointer (before runtimeSafety stack) ⟨3, 16⟩ data 5 = .ok (middle runtimeSafety stack) := by
  cases runtimeSafety <;> cases stack <;> rfl

theorem capacity_assignment (runtimeSafety stack : Bool) :
    write .capacity (middle runtimeSafety stack) ⟨3, 16⟩ data 5 = .ok (after runtimeSafety stack) := by
  cases runtimeSafety <;> cases stack <;> rfl

theorem actual_publication (runtimeSafety stack : Bool) :
    run (before runtimeSafety stack) ⟨3, 16⟩ data 5 = (.ok (), after runtimeSafety stack) := by
  simp only [run, program, steps, pointer_assignment, capacity_assignment]

theorem publication_without_store_premises (runtimeSafety stack : Bool) :
    ∃ finalState, run (before runtimeSafety stack) ⟨3, 16⟩ data 5 = (.ok (), finalState) ∧
      finalState.valid = true ∧ (before runtimeSafety stack).heap.RetainsShape finalState.heap ∧
      readHeader finalState ⟨3, 16⟩ = .ok (.slice itemsType data 2, .scalar (.int false 64 5)) ∧
      finalState.nextId = (before runtimeSafety stack).nextId ∧
      finalState.nextAddress = (before runtimeSafety stack).nextAddress ∧
      (∀ id, id ≠ 3 → finalState.heap.lookup id = (before runtimeSafety stack).heap.lookup id) :=
  run_verified runtimeSafety (before runtimeSafety stack) 3
    (Owner.FieldTests.cell runtimeSafety true stack Owner.FieldTests.completedCells) ⟨2, 0⟩ data 2 5
    (initial_valid runtimeSafety stack) rfl rfl rfl (by cases runtimeSafety <;> cases stack <;> rfl) (by decide)

theorem readback_from_publication (runtimeSafety stack : Bool) :
    readHeader (after runtimeSafety stack) ⟨3, 16⟩ = .ok (.slice itemsType data 2, .scalar (.int false 64 5)) ∧
      (after runtimeSafety stack).valid = true := by
  obtain ⟨finalState, executed, valid, _, header, _⟩ := publication_without_store_premises runtimeSafety stack
  have same := (Prod.mk.inj (executed.symm.trans (actual_publication runtimeSafety stack))).2
  exact same ▸ ⟨header, valid⟩

theorem pointer_prefix_preserves_length_and_old_capacity (runtimeSafety stack : Bool) :
    readHeader (middle runtimeSafety stack) ⟨3, 16⟩ = .ok (.slice itemsType data 2, .scalar (.int false 64 3)) := by
  cases runtimeSafety <;> cases stack <;> rfl

theorem malformed_capacity_retains_pointer (runtimeSafety : Bool) :
    run (before runtimeSafety true) ⟨3, 16⟩ data (-1) = (.error .malformed, middle runtimeSafety true) ∧
      run (before runtimeSafety true) ⟨3, 16⟩ data addressLimit = (.error .malformed, middle runtimeSafety true) := by
  cases runtimeSafety <;> constructor <;> rfl

def readonly (runtimeSafety : Bool) : State := {before runtimeSafety true with
  heap := (before runtimeSafety true).heap.replace 3
    (Owner.FieldTests.cell runtimeSafety false true Owner.FieldTests.completedCells)}

theorem readonly_rejects_before_writes (runtimeSafety : Bool) :
    run (readonly runtimeSafety) ⟨3, 16⟩ data 5 = (.error .readOnly, readonly runtimeSafety) := by
  cases runtimeSafety <;> rfl

theorem stale_or_misaligned_owner_rejects (runtimeSafety : Bool) :
    run (erase (before runtimeSafety true) 3) ⟨3, 16⟩ data 5 = (.error .unallocated, erase (before runtimeSafety true) 3) ∧
      run (before runtimeSafety true) ⟨3, 17⟩ data 5 = (.error .memoryValidity, before runtimeSafety true) := by
  cases runtimeSafety <;> constructor <;> rfl

theorem publication_does_not_allocate_or_release (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).heap.lookup 99 = none ∧
      (after runtimeSafety stack).heap.lookup 2 = (before runtimeSafety stack).heap.lookup 2 ∧
      representativeFields (after runtimeSafety stack) ⟨3, 16⟩ 1 = .error .unallocated ∧
      (after runtimeSafety stack).nextId = (before runtimeSafety stack).nextId ∧
      (after runtimeSafety stack).nextAddress = (before runtimeSafety stack).nextAddress := by
  cases runtimeSafety <;> cases stack <;> decide

-- Reuse the actual prefix-copy fixture. Move the containing owner beyond both
-- backing regions, retaining its captured layout and initialized length.
def copied (runtimeSafety : Bool) : State := {Copy.Tests.after with
  heap := Copy.Tests.after.heap.replace 3 {Owner.FieldTests.cell runtimeSafety true true Owner.FieldTests.completedCells with base := 800}
  nextAddress := 800 + (Owner.layout runtimeSafety).bytes}

theorem published_copy_uses_new_backing (runtimeSafety : Bool) :
    let result := run (copied runtimeSafety) ⟨3, 16⟩ ⟨4, 0⟩ 5
    (copied runtimeSafety).valid = true ∧ result.1 = .ok () ∧
      representativeFields result.2 ⟨3, 16⟩ 0 =
        .ok (.ok [Expression.Tests.item, Expression.Tests.arguments, Expression.Tests.id, Expression.Tests.sequence]) ∧
      representativeFields result.2 ⟨3, 16⟩ 1 =
        .ok (.ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence]) ∧
      representative result.2 ⟨3, 16⟩ 2 = .ok (.error .invalidId) := by
  cases runtimeSafety <;> decide

def missingLength (runtimeSafety : Bool) : State := {before runtimeSafety true with
  heap := (before runtimeSafety true).heap.replace 3 (Owner.FieldTests.cell runtimeSafety true true
    (Owner.FieldTests.completedCells.filter (fun entry => entry.1 != 24)))}
def missingLengthAfter (runtimeSafety : Bool) : State := {missingLength runtimeSafety with
  heap := (missingLength runtimeSafety).heap.replace 3 (Owner.FieldTests.cell runtimeSafety true true
    (finalCells.filter (fun entry => entry.1 != 24)))}

theorem publication_neither_reads_nor_initializes_length (runtimeSafety : Bool) :
    run (missingLength runtimeSafety) ⟨3, 16⟩ data 5 = (.ok (), missingLengthAfter runtimeSafety) ∧
      readHeader (missingLengthAfter runtimeSafety) ⟨3, 16⟩ = .error .uninitialized := by
  cases runtimeSafety <;> constructor <;> rfl

def empty (runtimeSafety : Bool) : State := {before runtimeSafety true with
  heap := (before runtimeSafety true).heap.replace 3 (Owner.FieldTests.cell runtimeSafety true true
    (Owner.FieldTests.completedCells.set 24 (.scalar (.int false 64 0))))}

theorem empty_length_stays_empty (runtimeSafety : Bool) :
    let result := run (empty runtimeSafety) ⟨3, 16⟩ data 5
    result.1 = .ok () ∧ readHeader result.2 ⟨3, 16⟩ = .ok (.slice itemsType data 0, .scalar (.int false 64 5)) ∧
      representative result.2 ⟨3, 16⟩ 0 = .ok (.error .invalidId) := by
  cases runtimeSafety <;> decide

theorem capacity_assignment_does_not_extend_backing (runtimeSafety : Bool) :
    let result := run (before runtimeSafety true) ⟨3, 16⟩ ⟨2, 0⟩ 5
    result.1 = .ok () ∧ result.2.heap.lookup 2 = (before runtimeSafety true).heap.lookup 2 ∧
      Expression.readFields result.2 false ⟨2, 96⟩ = .error .memoryValidity := by
  cases runtimeSafety <;> decide

theorem parent_contents (runtimeSafety stack : Bool) : WordArray.Represents (before runtimeSafety stack) ⟨1, 1, 2⟩ [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have choice : index = 0 ∨ index = 1 := by simp at inside; omega
  rcases choice with rfl | rfl <;> cases runtimeSafety <;> cases stack <;> rfl

theorem all_outcomes_preserve_offset_parent (runtimeSafety stack : Bool) (capacity : Int) :
    (run (before runtimeSafety stack) ⟨3, 16⟩ data capacity).2.heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧
      WordArray.Represents (run (before runtimeSafety stack) ⟨3, 16⟩ data capacity).2 ⟨1, 1, 2⟩ [99, 1] := by
  have header : Owner.headerAddress ⟨3, 0⟩ = ⟨3, 16⟩ := rfl
  rw [← header]
  exact run_parent_borrow runtimeSafety (before runtimeSafety stack) 3
    (Owner.FieldTests.cell runtimeSafety true stack Owner.FieldTests.completedCells) data capacity
    ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation (initial_valid runtimeSafety stack) rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) rfl (parent_contents runtimeSafety stack)

-- Select the second embedded owner; the first owner remains byte-for-byte framed.
def nested (runtimeSafety : Bool) : State := {Owner.FieldTests.firstInitialized runtimeSafety with
  heap := [(7, {Owner.FieldTests.arrayCell runtimeSafety true with cells := (
    Owner.FieldTests.firstHeaderCells ++
    (.slice itemsType ⟨2, 0⟩ 2 : Value).leaves ((Owner.layout runtimeSafety).bytes + 16) ++
    (.scalar (.int false 64 3) : Value).leaves ((Owner.layout runtimeSafety).bytes + 32))})]}

theorem nested_owner_keeps_other_header (runtimeSafety : Bool) :
    let result := run (nested runtimeSafety) ⟨7, (Owner.layout runtimeSafety).bytes + 16⟩ data 5
    result.1 = .ok () ∧
      readHeader result.2 ⟨7, (Owner.layout runtimeSafety).bytes + 16⟩ = .ok (.slice itemsType data 2, .scalar (.int false 64 5)) ∧
      readHeader result.2 ⟨7, 16⟩ = .ok (.slice itemsType ⟨9, 0⟩ 0, .scalar (.int false 64 4)) := by
  cases runtimeSafety <;> decide

end Compiler.Extraction.RepresentativeArray.Publication.Tests
