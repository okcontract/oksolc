/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecution

namespace Compiler.Extraction.Storage

/-- Local operation obligations used to derive the complete insertion caller's
memory contract. Both ordinary allocation outcomes preserve the invariant;
semantic rejection retains the actual reached state without such a claim. -/
structure Preserves (operations : Operations σ ε) (invariant : σ → Prop) : Prop where
  attempt : ∀ site owner before result after, invariant before →
    operations.attempt site owner before = (.ok result, after) → invariant after
  release : ∀ action owner before after, invariant before →
    operations.release action owner before = (.ok (), after) → invariant after

theorem Release.execute_preserves (operations : Operations σ ε) (invariant : σ → Prop)
    (kept : Preserves operations invariant) (release : Release) (state : State) (effects : σ)
    (initial : invariant effects) (completed : (release.execute operations state effects).1.1 = .ok ()) :
    invariant (release.execute operations state effects).2 := by
  cases called : operations.release release state effects with
  | mk result reached =>
    cases result with
    | error fault => simp [Release.execute, called] at completed
    | ok returned =>
      cases returned
      simpa only [Release.execute, called] using kept.release release state effects reached initial called

theorem releaseAll_preserves (operations : Operations σ ε) (invariant : σ → Prop)
    (kept : Preserves operations invariant) (releases : List Release) (state : State) (effects : σ)
    (initial : invariant effects) (completed : (releaseAll operations releases state effects).1.1 = .ok ()) :
    invariant (releaseAll operations releases state effects).2 := by
  induction releases generalizing state effects with
  | nil => exact initial
  | cons release rest ih =>
    cases called : release.execute operations state effects with
    | mk execution reached =>
      rcases execution with ⟨result, after⟩
      cases result with
      | error fault => simp [releaseAll, called] at completed
      | ok returned =>
        cases returned
        have step := Release.execute_preserves operations invariant kept release state effects initial (by rw [called])
        simp only [called] at step
        simp only [releaseAll, called] at completed ⊢
        exact ih after reached step completed

theorem Cleanup.execute_preserves (operations : Operations σ ε) (invariant : σ → Prop)
    (kept : Preserves operations invariant) (cleanup : Cleanup) (state : State) (effects : σ)
    (initial : invariant effects) (completed : (cleanup.execute operations state effects).1.1 = .ok ()) :
    invariant (cleanup.execute operations state effects).2 := by
  cases cleanup with
  | guarded flag release =>
    by_cases active : state.flag flag = true
    · simpa only [Cleanup.execute, active, ↓reduceIte] using
        Release.execute_preserves operations invariant kept release state effects initial (by simpa [Cleanup.execute, active] using completed)
    · simpa [Cleanup.execute, active] using initial
  | sequence releases => exact releaseAll_preserves operations invariant kept releases state effects initial completed

/-- The actual source program, including all applicable defers, preserves a
state invariant on every ordinary completion. No separate replay or policy
stream supplies the final memory or allocator effects. -/
theorem Program.execute_preserves (program : Program) (input : Input) (operations : Operations σ ε)
    (invariant : σ → Prop) (kept : Preserves operations invariant) (state : State) (effects : σ)
    (initial : invariant effects) (outcome : Option Outcome)
    (completed : (program.execute input operations state effects).1.1 = .ok outcome) :
    invariant (program.execute input operations state effects).2 := by
  induction program generalizing state effects outcome with
  | done | ret | capacityError => exact initial
  | command command next ih =>
    cases site : command.allocation with
    | none =>
      simp only [Program.execute, site] at completed ⊢
      exact ih _ effects initial outcome completed
    | some siteValue =>
      cases called : operations.attempt siteValue state effects with
      | mk result reached =>
        cases result with
        | error fault => simp [Program.execute, site, called] at completed
        | ok accepted =>
          have step := kept.attempt siteValue state effects accepted reached initial called
          cases accepted with
          | false => simpa only [Program.execute, site, called] using step
          | true =>
            simp only [Program.execute, site, called] at completed ⊢
            exact ih _ reached step outcome completed
  | branch test yes no next ihYes ihNo ihNext =>
    have branch : ∀ result,
        ((if test.eval input then yes else no).execute input operations state effects).1.1 = .ok result →
        invariant ((if test.eval input then yes else no).execute input operations state effects).2 := by
      cases active : test.eval input with
      | false => simpa only [active, Bool.false_eq_true, ↓reduceIte] using ihNo state effects initial
      | true => simpa only [active, ↓reduceIte] using ihYes state effects initial
    have selected : (if test.eval input then yes.execute input operations state effects
        else no.execute input operations state effects) =
        (if test.eval input then yes else no).execute input operations state effects := by split <;> rfl
    cases called : (if test.eval input then yes else no).execute input operations state effects with
    | mk execution reached =>
      rcases execution with ⟨result, after⟩
      cases result with
      | error fault => simp [Program.execute, selected, called] at completed
      | ok result =>
        have step := branch result (by rw [called])
        simp only [called] at step
        cases result with
        | none =>
          simp only [Program.execute, selected, called] at completed ⊢
          exact ihNext after reached step outcome completed
        | some value => simpa only [Program.execute, selected, called] using step
  | scope errorOnly cleanup body ih =>
    cases called : body.execute input operations state effects with
    | mk execution reached =>
      rcases execution with ⟨result, after⟩
      cases result with
      | error fault => simp [Program.execute, called] at completed
      | ok result =>
        have step := ih state effects initial result (by rw [called])
        simp only [called] at step
        by_cases skipped : (errorOnly && (result == some .success || result == none)) = true
        · simpa only [Program.execute, called, skipped, ↓reduceIte] using step
        · cases closed : cleanup.execute operations after reached with
          | mk execution finalEffects =>
            rcases execution with ⟨closeResult, final⟩
            cases closeResult with
            | error fault =>
              simp only [Program.execute, called, skipped, Bool.false_eq_true, ↓reduceIte, closed, Except.map, reduceCtorEq] at completed
            | ok returned =>
              cases returned
              have cleaned := Cleanup.execute_preserves operations invariant kept cleanup after reached step (by rw [closed])
              simpa only [Program.execute, called, skipped, Bool.false_eq_true, ↓reduceIte, closed] using cleaned

end Compiler.Extraction.Storage
