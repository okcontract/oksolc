/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortProjection

namespace Compiler.Extraction.InsertionSort
open Compiler.Algebraic

/-- The source's adjacent exchange reads two existing, distinct elements.
The external exchange contract is represented by the two list writes. -/
theorem adjacent_exchange (items : List NodeId) (j : Nat) (valid : j + 1 < items.length) :
    ((items.set (j + 1) items[j]).set j items[j + 1]).Perm items :=
  List.set_set_perm valid (by omega)

theorem insert_total (j : Nat) (items : List NodeId) (valid : j < items.length ∨ j = 0) :
    ∃ after, insert j items = .ok after ∧ after.Perm items := by
  induction j generalizing items with
  | zero => exact ⟨items, rfl, .refl _⟩
  | succ j ih =>
    have current : j + 1 < items.length := by omega
    have previous : j < items.length := by omega
    simp only [insert_succ, List.getElem?_eq_getElem current, List.getElem?_eq_getElem previous]
    split
    · have permutation := adjacent_exchange items j current
      obtain ⟨after, result, preserves⟩ := ih
        ((items.set (j + 1) items[j]).set j items[j + 1])
        (Or.inl (by simpa only [List.length_set] using previous))
      exact ⟨after, result, preserves.trans permutation⟩
    · exact ⟨items, rfl, .refl _⟩

/-- One extra observation is needed to see the false outer guard. Each taken
iteration preserves the fixed slice length and decreases the fuel bound. -/
theorem passes_total (fuel stop i : Nat) (items : List NodeId)
    (length : items.length = stop) (enough : stop - i < fuel) :
    ∃ after, passes fuel stop i items = .ok after ∧ after.Perm items := by
  induction fuel generalizing i items with
  | zero => omega
  | succ fuel ih =>
    simp only [passes_succ]
    split
    next guard =>
      obtain ⟨middle, inner, permutation⟩ := insert_total i items (Or.inl (by omega))
      rw [inner]
      obtain ⟨after, result, preserves⟩ := ih (i + 1) middle
        (permutation.length_eq.trans length) (by omega)
      exact ⟨after, result, preserves.trans permutation⟩
    next => exact ⟨items, rfl, .refl _⟩

theorem run_total (items : List NodeId) :
    ∃ after, run items = .ok after ∧ after.Perm items :=
  passes_total (items.length + 1) items.length 1 items rfl (by omega)

/-- Total value projection used by the existing normalization interface.
The fault branch is unreachable by run_total; checked retains width errors. -/
def sortIds (items : List NodeId) : List NodeId :=
  match run items with
  | .ok after => after
  | .fault _ _ => items

theorem run_sortIds (items : List NodeId) : run items = .ok (sortIds items) := by
  obtain ⟨after, result, _⟩ := run_total items
  simp [sortIds, result]

theorem sortIds_perm (items : List NodeId) : (sortIds items).Perm items := by
  obtain ⟨after, result, permutation⟩ := run_total items
  simpa [sortIds, result] using permutation

theorem checked_total (items : List NodeId) (width : items.length < 2^64) :
    checked items = .ok (sortIds items) ∧ (sortIds items).Perm items :=
  ⟨by simpa [checked, width] using run_sortIds items, sortIds_perm items⟩

/-- Bounds required by each native loop iteration at a = 0. Permutation
preserves length between iterations. These are index facts, not a native
address-injectivity, byte-layout, or noalias refinement theorem. -/
theorem iteration_indices (length i j : Nat) (width : length < 2^64)
    (outer : i < length) (inner : 0 < j) (within : j ≤ i) :
    j < length ∧ j - 1 < length ∧ j ≠ j - 1 ∧
    i + 1 < 2^64 ∧ j - 1 < 2^64 := by omega

end Compiler.Extraction.InsertionSort
