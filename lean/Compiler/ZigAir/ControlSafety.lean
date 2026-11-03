/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Control

namespace Compiler.ZigAir.Control

def Outcome.state : Outcome Value Fault State → State
  | .returned _ state | .jumped _ _ _ state | .fault _ state => state

/-- Primitive invariant preservation composes through every finite control path,
including malformed operands, escaping jumps and state-changing failures. -/
theorem Code.preserves (sem : Semantics Ty Prim Ref Value Fault State)
    (invariant : State → Prop)
    (primitive : ∀ prim args env state, invariant state →
      invariant (sem.evalPrim prim args env state).2)
    (code : Code Ty Prim Ref) (args : List Value) (env : Env Value) (state : State)
    (initial : invariant state) : invariant (code.eval sem args env state).state := by
  induction code generalizing env state with
  | bind id ty prim next ih =>
    cases h : sem.evalPrim prim args env state with
    | mk result after =>
      have valid : invariant after := by simpa [h] using primitive prim args env state initial
      cases result with
      | error reason => simpa [Code.eval, h, Outcome.state] using valid
      | ok value =>
        by_cases typed : sem.hasType value ty = true
        · simpa [Code.eval, h, typed] using ih (env.set id value) after valid
        · simpa [Code.eval, h, typed, Outcome.state] using valid
  | branch condition yes no ihYes ihNo =>
    cases h : sem.evalRef condition env with
    | error reason => simpa [Code.eval, h, Outcome.state] using initial
    | ok value =>
      cases flag : sem.truth value with
      | none => simpa [Code.eval, h, flag, Outcome.state] using initial
      | some flagValue =>
        cases flagValue with
        | false => simpa [Code.eval, h, flag] using ihNo env state initial
        | true => simpa [Code.eval, h, flag] using ihYes env state initial
  | block id ty body next ihBody ihNext =>
    have valid := ihBody env state initial
    cases h : body.eval sem args env state with
    | returned value after => simpa [Code.eval, h] using valid
    | fault reason after => simpa [Code.eval, h] using valid
    | jumped target value afterEnv after =>
      have afterValid : invariant after := by simpa [h, Outcome.state] using valid
      by_cases catches : target = id
      · by_cases typed : sem.hasType value ty = true
        · simpa [Code.eval, h, catches, typed] using ihNext (afterEnv.set id value) after afterValid
        · simpa [Code.eval, h, catches, typed, Outcome.state] using afterValid
      · simpa [Code.eval, h, catches, Outcome.state] using afterValid
  | jump target value =>
    cases h : sem.evalRef value env <;> simpa [Code.eval, h, Outcome.state] using initial
  | ret value =>
    cases h : sem.evalRef value env <;> simpa [Code.eval, h, Outcome.state] using initial
  | loop enabled _ _ _ | «repeat» enabled _ => cases enabled

end Compiler.ZigAir.Control
