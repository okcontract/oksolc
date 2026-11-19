/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpInvocationSafety

namespace Compiler.ZigAir.MemoryExp.SafetyTests
open Memory MemoryAir

private def cell (base : Nat) (writable stack : Bool) (value : Word := 7) : Allocation :=
  ⟨base, wordType, [(0, number value)], writable, stack⟩
private def heap (base : Nat) (writable stack : Bool) : State :=
  ⟨[(0, cell base writable stack)], 1, base + 32⟩

/-- A matching writable type alone cannot hide a misaligned physical region. -/
theorem invalid_alignment_needs_heap_invariant :
    Writable (heap 17 true true) ⟨0, 0⟩ ∧ (heap 17 true true).valid = false ∧
      store (heap 17 true true) (slot ⟨0, 0⟩) (number 9) = .error .memoryValidity := by
  refine ⟨⟨rfl, cell 17 true true, rfl, rfl, rfl⟩, ?_, ?_⟩ <;> rfl'

theorem readonly_is_not_writable :
    ¬ Writable (heap 16 false true) ⟨0, 0⟩ := by
  simp [Writable, heap, Heap.lookup, cell]

theorem nonzero_offset_is_not_writable :
    ¬ Writable (heap 16 true true) ⟨0, 16⟩ := by
  simp [Writable]

theorem cleanup_revokes_scratch :
    ¬ Writable (cleanup 0 (heap 16 true true)) ⟨0, 0⟩ := by
  simp [Writable, cleanup, heap, Heap.lookup, cell]

/-- Removing the freshness premise from the frame law would be unsound. -/
theorem older_write_changes_caller :
    ∃ after, store (heap 16 true false) (slot ⟨0, 0⟩) (number 9) = .ok after ∧
      after.heap.older 1 ≠ (heap 16 true false).heap.older 1 := by
  refine ⟨⟨[(0, cell 16 true false 9)], 1, 48⟩, ?_, ?_⟩
  · apply store_of_access (heap 16 true false) wordType ⟨0, 0⟩ ⟨32, 16⟩
      (cell 16 true false) [(0, number 9)] (number 9) (number_typed 9) rfl (by rfl')
    apply Cells.write_single
    · exact number_valid 9
    · rfl
    · change (decide (some wordType = some wordType) && (number 9).valid) = true
      rw [number_valid]; rfl
    · rfl
  · decide

/-- New lifetime identifiers alone do not authorize cleanup of a non-stack
allocation; the StackSince premise is independently necessary. -/
theorem new_nonstack_survives_cleanup :
    (cleanup 0 (heap 16 true false)).heap = (heap 16 true false).heap ∧
      (heap 16 true false).heap.older 0 = [] ∧ ¬ (heap 16 true false).heap.StackSince 0 := by
  refine ⟨rfl, rfl, ?_⟩
  intro stack
  have impossible := stack (0, cell 16 true false) (by simp [heap]) (by decide)
  cases impossible

end Compiler.ZigAir.MemoryExp.SafetyTests
