/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineProofs

namespace Compiler.ZigAir.Control.Machine
variable (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value)

/-- Interpret a finite evaluator's result in a machine continuation. -/
def continueOutcome (outcome : Outcome Value Fault State) (frames : List (Frame Ty Prim Ref)) :
    Execution Ty Prim Ref Value Fault State :=
  match outcome with
  | .jumped target value env state => jump sem target value env state frames
  | other => .finished other

/-- Universal compatibility, including malformed finite programs, fault effects,
escaping jumps and arbitrary enclosing machine frames. -/
theorem finite_steps (code : Code Ty Prim Ref) (env : Env Value) (state : State)
    (frames : List (Frame Ty Prim Ref)) :
    Steps sem args (.suspended ⟨code.enableLoops, env, state, frames⟩)
      (continueOutcome sem (code.eval sem args env state) frames) := by
  induction code generalizing env state frames with
  | bind id ty prim next ih =>
    apply Steps.step
    cases h : sem.evalPrim prim args env state with
    | mk result after =>
      cases result with
      | error reason => simp only [Code.enableLoops, step, h, Code.eval, continueOutcome]; exact .refl _
      | ok value =>
        by_cases typed : sem.hasType value ty = true
        · simpa only [Code.enableLoops, step, h, Code.eval, if_pos typed] using ih (env.set id value) after frames
        · simp only [Code.enableLoops, step, h, Code.eval, if_neg typed, continueOutcome]; exact .refl _
  | branch condition yes no ihYes ihNo =>
    apply Steps.step
    cases h : sem.evalRef condition env with
    | error reason => simp only [Code.enableLoops, step, h, Code.eval, continueOutcome]; exact .refl _
    | ok value =>
      cases flag : sem.truth value with
      | none => simp only [Code.enableLoops, step, h, flag, Code.eval, continueOutcome]; exact .refl _
      | some flagValue =>
        cases flagValue with
        | false =>
          simpa only [Code.enableLoops, step, h, flag, Code.eval, Bool.false_eq_true, ↓reduceIte] using ihNo env state frames
        | true =>
          simpa only [Code.enableLoops, step, h, flag, Code.eval, ↓reduceIte] using ihYes env state frames
  | block id ty body next ihBody ihNext =>
    apply Steps.step
    simp only [Code.enableLoops, step]
    have path := ihBody env state (.block id ty next.enableLoops :: frames)
    cases h : body.eval sem args env state with
    | returned value after => simpa only [Code.eval, h, continueOutcome] using path
    | fault reason after => simpa only [Code.eval, h, continueOutcome] using path
    | jumped target value afterEnv after =>
      by_cases catches : target = id
      · by_cases typed : sem.hasType value ty = true
        · have bodyPath : Steps sem args
              (.suspended ⟨body.enableLoops, env, state, .block id ty next.enableLoops :: frames⟩)
              (.suspended ⟨next.enableLoops, afterEnv.set id value, after, frames⟩) := by
            simpa only [h, continueOutcome, jump, if_pos catches, if_pos typed] using path
          simpa only [Code.eval, h, if_pos catches, if_pos typed] using
            bodyPath.trans sem args (ihNext (afterEnv.set id value) after frames)
        · simpa only [Code.eval, h, continueOutcome, jump, if_pos catches, if_neg typed] using path
      · simpa only [Code.eval, h, continueOutcome, jump, if_neg catches] using path
  | jump target ref =>
    apply Steps.step
    cases h : sem.evalRef ref env <;>
      simp only [Code.enableLoops, step, h, Code.eval, continueOutcome] <;> exact .refl _
  | ret ref =>
    apply Steps.step
    cases h : sem.evalRef ref env <;>
      simp only [Code.enableLoops, step, h, Code.eval, continueOutcome] <;> exact .refl _
  | loop enabled _ _ _ | «repeat» enabled _ => cases enabled

/-- Every finite evaluator result is reached by the machine with sufficient fuel.
No well-typedness or successful-return premise hides malformed/error cases. -/
theorem finite_run (code : Code Ty Prim Ref) (env : Env Value) (state : State) :
    ∃ fuel, run sem args fuel ⟨code.enableLoops, env, state, []⟩ =
      .finished (code.eval sem args env state) := by
  have path := finite_steps sem args code env state []
  have last : continueOutcome sem (code.eval sem args env state) [] =
      .finished (code.eval sem args env state) := by
    cases code.eval sem args env state <;> rfl
  rw [last] at path
  exact (steps_iff_fuel sem args _ _).mp path

/-- Conversely, every terminal machine result for finite code is the old result. -/
theorem finite_result (code : Code Ty Prim Ref) (env : Env Value) (state : State)
    (fuel : Nat) (outcome : Outcome Value Fault State)
    (done : run sem args fuel ⟨code.enableLoops, env, state, []⟩ = .finished outcome) :
    outcome = code.eval sem args env state := by
  obtain ⟨budget, expected⟩ := finite_run sem args code env state
  exact finished_unique sem args _ _ _ ((steps_iff_fuel sem args _ _).mpr ⟨fuel, done⟩)
    ((steps_iff_fuel sem args _ _).mpr ⟨budget, expected⟩)

end Compiler.ZigAir.Control.Machine
