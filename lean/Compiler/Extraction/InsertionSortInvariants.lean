/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortProgram

namespace Compiler.Extraction.InsertionSort

/-- Reads are pure in this interface. Every exchange outcome must preserve the
invariant, including faults; the extracted loops retain those exact states. -/
theorem insertUsing_preserves (ops : Operations σ ε) (invariant : σ → Prop)
    (exchange : ∀ state left right, invariant state → invariant (ops.exchange state left right).2)
    (j : Nat) (state : σ) (initial : invariant state) : invariant (insertUsing ops j state).2 := by
  induction j generalizing state with
  | zero => exact initial
  | succ j ih =>
    simp only [insertUsing]
    cases current : ops.read state (j + 1) with
    | error fault => exact initial
    | ok value =>
      dsimp only
      cases previous : ops.read state j with
      | error fault => exact initial
      | ok old =>
        dsimp only
        split
        · have preserved := exchange state (j + 1) j initial
          cases called : ops.exchange state (j + 1) j with
          | mk result middle =>
            simp only [called] at preserved
            cases result with
            | error fault => exact preserved
            | ok value => cases value; exact ih middle preserved
        · exact initial

theorem passesUsing_preserves (ops : Operations σ ε) (invariant : σ → Prop)
    (exchange : ∀ state left right, invariant state → invariant (ops.exchange state left right).2)
    (fuel stop index : Nat) (state : σ) (initial : invariant state) :
    invariant (passesUsing ops fuel stop index state).2 := by
  induction fuel generalizing index state with
  | zero => exact initial
  | succ fuel ih =>
    simp only [passesUsing]
    split
    · have preserved := insertUsing_preserves ops invariant exchange index state initial
      cases inserted : insertUsing ops index state with
      | mk result middle =>
        simp only [inserted] at preserved
        cases result with
        | error fault => exact preserved
        | ok value => cases value; exact ih (index + 1) middle preserved
    · exact initial

theorem runUsing_preserves (ops : Operations σ ε) (invariant : σ → Prop)
    (exchange : ∀ state left right, invariant state → invariant (ops.exchange state left right).2)
    (length : Nat) (state : σ) (initial : invariant state) : invariant (runUsing ops length state).2 :=
  passesUsing_preserves ops invariant exchange _ _ _ state initial

end Compiler.Extraction.InsertionSort
