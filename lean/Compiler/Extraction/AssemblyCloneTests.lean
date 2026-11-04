/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssemblyCloneProofs
import Compiler.Extraction.AssemblyCloneFixtures

namespace Compiler.Extraction.AssemblyClone.Fixtures
open Compiler.Algebraic Compiler.Extraction.Cache
set_option linter.unusedSimpArgs false

theorem duplicate_safe (succeeds : Bool) : Duplicates Frame Owns (duplicate succeeds) := by
  intro source before result after ran
  by_cases empty : source.contents.isEmpty = true
  · simp only [duplicate, empty, ↓reduceIte] at ran
    cases ran
    exact ⟨rfl, fun _ _ => rfl, by simp [Owns, empty]⟩
  · cases succeeds <;> simp only [duplicate, empty, ↓reduceIte, Bool.false_eq_true] at ran
    · cases ran; rfl
    · cases ran
      exact ⟨rfl, fun _ bound => List.getElem?_append_left bound, by simp [Owns, empty]⟩

theorem duplicate_free (succeeds : Bool) (source : Bytes) (before : Heap) (copied : Bytes) (after : Heap)
    (ran : duplicate succeeds source before = (.ok copied, after)) : free copied after = before := by
  by_cases empty : source.contents.isEmpty = true
  · simp only [duplicate, empty, ↓reduceIte] at ran
    cases ran
    simp [free, empty]
  · cases succeeds <;> simp only [duplicate, empty, ↓reduceIte, Bool.false_eq_true] at ran
    · cases ran
    · cases ran
      simp [free, empty]

theorem preserved : Cloned Frame Owns original copied initial allocated :=
  clone_safe Frame Owns (duplicate true) (duplicate_safe true) original initial (.ok copied) allocated rfl

theorem cleaned : deinitCode.run free copied allocated = (none, initial) :=
  clone_cleanup (duplicate true) free (duplicate_free true) original copied initial allocated rfl

theorem allocation_failure : cloneCode.run (duplicate false) original initial = (.error .outOfMemory, initial) := rfl
theorem no_payload_no_allocation : cloneCode.run (duplicate false) plain initial = (.ok plain, initial) := rfl
theorem empty_no_allocation : cloneCode.run (duplicate false) empty initial = (.ok empty, initial) := rfl

example : cloneCode.run (duplicate true) original initial = (.ok copied, allocated) := by rfl
example : copied.metadata = original.metadata := by rfl
example : allocated[0]? = initial[0]? := by rfl
example : (allocated.set 2 [255])[0]? = initial[0]? := by rfl
example : keyCode.run copied.item [0, 1] 99 = keyCode.run original.item [0, 1] 99 := by rfl
example : keyCode.run plain.item [] 0 = some ⟨2, 0, 7, [], 0⟩ := by rfl
example : deinitCode.run free empty initial = (none, initial) := by rfl
example : deinitCode.run free plain initial = (none, initial) := by rfl

-- A shallow copy has identical content, but fails the ownership contract after
-- a real duplicate. Equal sentinel addresses for empty buffers are permitted.
example : SameValue original original := ⟨rfl, rfl, rfl⟩
theorem shallow_rejected : ¬Cloned Frame Owns original original initial allocated := by
  intro checked
  obtain ⟨output, equal, _, owned⟩ := checked.2
  cases equal
  have impossible : (0 : Nat) = 2 := owned.1
  contradiction

theorem empty_owned : Cloned Frame Owns empty empty initial initial :=
  clone_safe Frame Owns (duplicate false) (duplicate_safe false) empty initial (.ok empty) initial rfl

end Compiler.Extraction.AssemblyClone.Fixtures
