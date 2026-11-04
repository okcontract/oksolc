/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortCopied
import Compiler.Extraction.InsertionSortInvariants
import Compiler.ZigAir.MemoryInvocationShape
import Compiler.ZigAir.MemoryWordCopyShape

namespace Compiler.Extraction.InsertionSort.Captured
open Compiler.ZigAir Compiler.ZigAir.Memory Compiler.ZigAir.MemoryAir
open Compiler.ZigAir.Memory.WordArray

theorem outcome_state (invocation : Invocation) : (outcome invocation).2 = invocation.state := by
  cases invocation with
  | suspended => rfl
  | finished result state =>
    cases result with
    | error fault => rfl
    | ok value =>
      cases value with
      | scalar value => cases value <;> rfl
      | optionalScalar | optionalObject => rfl
      | pointer => rfl
      | slice => rfl

/-- Includes rejected arguments, every suspended prefix and every terminal
fault. In particular, cleanup cannot turn an original owned buffer into stack
storage or remove its allocation. -/
theorem exchange_storage (budget : Nat) (view : View) (state : State) (left right : Nat)
    (initial : state.valid = true) :
    (exchange budget view state left right).2.valid = true ∧
      state.heap.RetainsShape (exchange budget view state left right).2.heap := by
  simp only [exchange]
  split
  · cases first : elementPointer state view.buffer left with
    | error fault => exact ⟨initial, Heap.RetainsShape.refl _⟩
    | ok a =>
      dsimp only
      cases second : elementPointer state view.buffer right with
      | error fault => exact ⟨initial, Heap.RetainsShape.refl _⟩
      | ok b =>
        simp only [outcome_state]
        exact ⟨GeneratedMemory.fn_swap_u32.preserves_valid budget [a, b] state initial,
          GeneratedMemory.fn_swap_u32.retains_shape budget [a, b] state initial⟩
  · exact ⟨initial, Heap.RetainsShape.refl _⟩

theorem run_storage (budget : Nat) (state : State) (view : View) (initial : state.valid = true) :
    (run budget state view).2.valid = true ∧ state.heap.RetainsShape (run budget state view).2.heap := by
  unfold run
  split
  · apply runUsing_preserves (operations budget view)
      (fun after => after.valid = true ∧ state.heap.RetainsShape after.heap)
    · intro middle left right before
      have next := exchange_storage budget view middle left right before.1
      exact ⟨next.1, before.2.trans next.2⟩
    · exact ⟨initial, Heap.RetainsShape.refl _⟩
  · exact ⟨initial, Heap.RetainsShape.refl _⟩

end Compiler.Extraction.InsertionSort.Captured

namespace Compiler.Extraction.InsertionSort.Copied
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

/-- Copy and captured sort preserve original allocation metadata for every
budget and outcome, including partial copy and partial byte-swap faults. This
does not assert a value permutation or restore uninitialized data on failure. -/
theorem run_storage (budget : Nat) (state : State) (source target : View) (initial : state.valid = true) :
    (run budget state source target).2.valid = true ∧
      state.heap.RetainsShape (run budget state source target).2.heap := by
  have copied := WordCopy.copy_storage state source target initial
  simp only [run, copySortUsing, copyTo]
  cases step : WordCopy.copy state source target with
  | mk result middle =>
    simp only [step] at copied
    cases result with
    | error fault => exact copied
    | ok value =>
      cases value
      have sorted := Captured.run_storage budget middle target copied.1
      exact ⟨sorted.1, copied.2.trans sorted.2⟩

end Compiler.Extraction.InsertionSort.Copied
