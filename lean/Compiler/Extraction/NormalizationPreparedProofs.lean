/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationPrepared

namespace Compiler.Extraction.Cache.NormalizationOwnership

theorem finish_ready_safe (p : Primitives σ) (outcome : Outcome) (state : State) (effects : σ)
    (ready : Ready state) (notTransferred : outcome ≠ .transferred) :
    Safe (normalizationOwnershipCode.finishWith p outcome state effects).1 := by
  have closed := deinit_with_ready p.release effects state ready
  change _ ∧ _ ∧ _ at closed
  simpa only [Code.finishWith, Safe, if_neg notTransferred] using closed

theorem finish_taken_safe (p : Primitives σ) (state : State) (effects : σ) (taken : Taken state) :
    Safe (normalizationOwnershipCode.finishWith p .transferred state effects).1 := by
  simp only [Code.finishWith, deinit_with_taken p.release effects state taken, Safe, ↓reduceIte]
  exact ⟨True.intro, taken.2.1, taken.2.2.2⟩

theorem finish_cleaned_safe (p : Primitives σ) (state : State) (effects : σ) (taken : Taken state) :
    Safe (normalizationOwnershipCode.finishWith p .cleaned (state.move .caller .released) (p.release state effects)).1 := by
  rcases taken with ⟨alive, valid, unowned, owner⟩
  simp only [Code.finishWith, State.move, owner, ↓reduceIte, normalizationOwnershipCode, Code.deinitWith,
    unowned, Bool.and_false, Bool.false_eq_true, Safe, valid]
  exact ⟨True.intro, True.intro, Or.inr True.intro⟩

/-- Local ownership safety depends on the current effect state, not on a ghost
allocation decision made before preparation. Release and allocation callbacks
may have arbitrary private effects. Heap validity remains a separate contract. -/
theorem continue_with_safe (p : Primitives σ) (exit : Exit) (state : State) (effects : σ)
    (ready : Ready state) : Safe (normalizationOwnershipCode.continueWith p exit state effects).1 := by
  cases exit with
  | lookup => exact finish_ready_safe p .lookup state effects ready (by decide)
  | transfer | cleanup =>
    cases step : normalizationOwnershipCode.takeWith (p.allocate .duplicate) state effects with
    | mk result after =>
      rcases result with ⟨success, next⟩
      cases success with
      | false =>
        have same := take_with_failure normalizationOwnershipCode (p.allocate .duplicate) effects after state next step
        subst next
        simpa only [Code.continueWith, step, Bool.not_false, ↓reduceIte] using
          finish_ready_safe p .allocationFailure state after ready (by decide)
      | true =>
        have taken := take_with_success (p.allocate .duplicate) effects after state next ready step
        first
        | simpa only [Code.continueWith, step, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using finish_taken_safe p next after taken
        | simpa only [Code.continueWith, step, Bool.not_true, Bool.false_eq_true, ↓reduceIte] using finish_cleaned_safe p next after taken

/-- Normal returns close the ownership scope; preparation faults retain a live
ready token and its effects. An aborted allocated temporary can remain owned,
so this predicate deliberately does not assert closure on abnormal outcomes. -/
def PreparedSafe (result : PreparedResult ε) : Prop :=
  match result with
  | .ok value => Safe value
  | .error (_, state) => Ready state

theorem run_prepared_safe (commutative : Bool) (length bufferLength : Nat)
    (p : PreparedPrimitives σ ε) (exit : Exit) (effects : σ) :
    PreparedSafe (normalizationOwnershipCode.runPrepared commutative length bufferLength p exit effects).1 := by
  cases selected : normalizationOwnershipCode.initWith commutative length bufferLength (p.allocate .temporary) effects with
  | mk lookup after =>
    cases lookup with
    | none =>
      simp only [run_prepared_expand, selected, PreparedSafe, Safe]
      exact ⟨True.intro, True.intro, Or.inl True.intro⟩
    | some state =>
      have ready := init_with_ready commutative length bufferLength (p.allocate .temporary) effects after state selected
      by_cases borrowed : state.origin = .input
      · simpa only [run_prepared_expand, selected, if_pos borrowed, PreparedSafe] using
          continue_with_safe p.toPrimitives exit state after ready
      · cases prepared : p.prepare state after with
        | mk result next =>
          cases result with
          | error reason => simpa only [run_prepared_expand, selected, if_neg borrowed, prepared, PreparedSafe] using ready
          | ok returned =>
            cases returned
            simpa only [run_prepared_expand, selected, if_neg borrowed, prepared, PreparedSafe] using
              continue_with_safe p.toPrimitives exit state next ready

end Compiler.Extraction.Cache.NormalizationOwnership
