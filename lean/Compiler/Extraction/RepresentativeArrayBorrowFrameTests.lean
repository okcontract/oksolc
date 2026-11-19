/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayBorrowFrame
import Compiler.Extraction.RepresentativeArrayAppendTests

namespace Compiler.Extraction.RepresentativeArray.Append.BorrowTests
open Compiler.ZigAir.Memory
open Compiler.Algebraic

def source : WordArray.View := ⟨1, 1, 2⟩

theorem initial_parent_contents : WordArray.Represents Tests.before source [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have alternatives : index = 0 ∨ index = 1 := by change index < 2 at inside; omega
  rcases alternatives with rfl | rfl <;> rfl

theorem persistent_offset_parent_frame :
    ∃ finalState, Tests.execute = .ok finalState ∧ finalState.valid = true ∧
      finalState.heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧ WordArray.Represents finalState source [99, 1] ∧
      finalState.nextId = Tests.before.nextId ∧ finalState.nextAddress = Tests.before.nextAddress ∧
      (∀ writable many type offset, load finalState (.pointer (.pointer writable many type) ⟨1, offset⟩) =
        load Tests.before (.pointer (.pointer writable many type) ⟨1, offset⟩)) :=
  append_parent_borrow Tests.before 3 2 3 1 Tests.header FieldTests.data ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 source [99, 1] 4
    Expression.Tests.argumentsAllocation (by decide) (by decide) rfl rfl (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl initial_parent_contents

theorem actual_persistent_parent : Tests.after.heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧
    WordArray.Represents Tests.after source [99, 1] := by
  obtain ⟨finalState, executed, _, found, represented, _⟩ := persistent_offset_parent_frame
  have same : finalState = Tests.after := Except.ok.inj (executed.symm.trans Tests.actual_append)
  exact same ▸ ⟨found, represented⟩

def parent (writable stack : Bool) : Allocation :=
  { Expression.Tests.argumentsAllocation with base := 640, writable, stack }
def extended (writable stack : Bool) : State :=
  { Tests.before with heap := (4, parent writable stack) :: Tests.before.heap, nextId := 5, nextAddress := 656 }
def extendedAfter (writable stack : Bool) : State :=
  { Tests.after with heap := (4, parent writable stack) :: Tests.after.heap, nextId := 5, nextAddress := 656 }
def outer : WordArray.View := ⟨4, 1, 2⟩

theorem extended_parent_contents (writable stack : Bool) : WordArray.Represents (extended writable stack) outer [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have alternatives : index = 0 ∨ index = 1 := by change index < 2 at inside; omega
  rcases alternatives with rfl | rfl <;> cases writable <;> cases stack <;> rfl

theorem actual_extended_append (writable stack : Bool) :
    Tests.execute (extended writable stack) = .ok (extendedAfter writable stack) := by
  cases writable <;> cases stack <;> decide

theorem extended_parent_frame (writable stack : Bool) :
    (extendedAfter writable stack).heap.lookup 4 = some (parent writable stack) ∧
      WordArray.Represents (extendedAfter writable stack) outer [99, 1] := by
  have initial : (extended writable stack).valid = true := by cases writable <;> cases stack <;> decide
  have found : (extended writable stack).heap.lookup 4 = some (parent writable stack) := rfl
  obtain ⟨finalState, executed, _, kept, represented, _⟩ := append_parent_borrow (extended writable stack) 3 2 3 1
    Tests.header FieldTests.data ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 outer [99, 1] 4 (parent writable stack)
    initial (by rfl) rfl rfl (by rfl) rfl rfl (by rfl) (by rfl) (by decide) (by decide) (by decide) (by decide)
    found rfl (extended_parent_contents writable stack)
  have same := Except.ok.inj (executed.symm.trans (actual_extended_append writable stack))
  exact same ▸ ⟨kept, represented⟩

theorem stack_and_readonly_metadata_survive :
    (extendedAfter true true).heap.lookup 4 = some (parent true true) ∧
    (extendedAfter false false).heap.lookup 4 = some (parent false false) :=
  ⟨(extended_parent_frame true true).1, (extended_parent_frame false false).1⟩

theorem readonly_borrow_cannot_write :
    store (extendedAfter false false) (outer.pointer 0) (WordArray.number 7) = .error .readOnly ∧
    load (extendedAfter false false) (.pointer (.pointer false false WordArray.word) (outer.address 0)) = .ok (WordArray.number 99) := by decide

theorem source_bound_and_outside_words_survive :
    sliceElementPointer (extendedAfter false false) (.slice (.slice false WordArray.word) (outer.address 0) 2) 2 = .error .sourceBounds ∧
    load (extendedAfter false false) (.pointer (.pointer false false WordArray.word) ⟨4, 0⟩) = .ok (WordArray.number 777) ∧
    load (extendedAfter false false) (.pointer (.pointer false false WordArray.word) ⟨4, 12⟩) = .ok (WordArray.number 5) := by decide

theorem no_new_lifetime_or_revived_alias : (extendedAfter true true).nextId = 5 ∧
    (extendedAfter true true).nextAddress = 656 ∧
    load (extendedAfter true true) (.pointer (.pointer false false WordArray.word) ⟨5, 4⟩) = .error .unallocated := by decide

def overwritten : State := RepresentativeArray.Tests.memory FieldTests.data (RepresentativeArray.Tests.headerCells ⟨2, 0⟩ 0)

/-- A word-typed pointer alone does not establish independent argument backing.
An initialized descriptor ID can be overwritten by append at that same slot. -/
theorem descriptor_alias_is_not_an_independent_parent :
    load overwritten (.pointer (.pointer false false WordArray.word) ⟨2, 24⟩) = .ok (WordArray.number 17) ∧
    (do let finalState ← Tests.execute overwritten 2 0
        load finalState (.pointer (.pointer false false WordArray.word) ⟨2, 24⟩)) = .ok (WordArray.number 0) := by decide

theorem descriptor_backing_rejects_word_array_admission (extent : Nat) :
    FieldTests.data.type ≠ .array extent WordArray.word := by
  intro impossible
  cases impossible

end Compiler.Extraction.RepresentativeArray.Append.BorrowTests
