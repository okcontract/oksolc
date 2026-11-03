/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Scalar

/-! The former scalar evaluator is retained here as a reference specification,
not a second production interpreter. Structural induction checks the move to
the shared stateful core for every finite program, argument list and SSA state,
including malformed programs and faults. -/
namespace Compiler.ZigAir.Scalar.ControlRefinement

def reference (code : Code) (args : List Value) (env : Env) : Outcome :=
  match code with
  | .bind id type value next =>
    match value.eval args env with
    | .error error => .fault error
    | .ok value => if value.hasType type then reference next args (env.set id value) else .fault .malformed
  | .branch condition yes no =>
    match condition.eval env with
    | .ok (.bool flag) => if flag then reference yes args env else reference no args env
    | .ok _ => .fault .malformed
    | .error error => .fault error
  | .block id type body next =>
    match reference body args env with
    | .jumped target value after =>
      if target = id then
        if value.hasType type then reference next args (after.set id value) else .fault .malformed
      else .jumped target value after
    | other => other
  | .jump target value =>
    match value.eval env with
    | .ok value => .jumped target value env
    | .error error => .fault error
  | .ret value =>
    match value.eval env with
    | .ok value => .returned value
    | .error error => .fault error
  | .loop enabled _ _ | .repeat enabled _ => nomatch enabled

def embed : Outcome → Control.Outcome Value Fault Unit
  | .returned value => .returned value ()
  | .jumped target value env => .jumped target value env ()
  | .fault reason => .fault reason ()

theorem eval_eq_embed (code : Code) (args : List Value) (env : Env) :
    Control.Code.eval controlSemantics code args env () = embed (reference code args env) := by
  induction code generalizing env with
  | bind id ty prim next ih =>
    cases h : prim.eval args env with
    | error reason => simp [Control.Code.eval, controlSemantics, reference, h, embed]
    | ok value =>
      by_cases typed : value.hasType ty = true
      · simpa [Control.Code.eval, controlSemantics, reference, h, typed] using ih (env.set id value)
      · simp [Control.Code.eval, controlSemantics, reference, h, typed, embed]
  | branch condition yes no ihYes ihNo =>
    cases h : condition.eval env with
    | error reason => simp [Control.Code.eval, controlSemantics, reference, h, embed]
    | ok value =>
      cases value with
      | int s n x => simp [Control.Code.eval, controlSemantics, reference, h, embed]
      | unit => simp [Control.Code.eval, controlSemantics, reference, h, embed]
      | bool flag =>
        cases flag with
        | false => simpa [Control.Code.eval, controlSemantics, reference, h] using ihNo env
        | true => simpa [Control.Code.eval, controlSemantics, reference, h] using ihYes env
  | block id ty body next ihBody ihNext =>
    simp only [Control.Code.eval, reference, ihBody]
    cases h : reference body args env with
    | returned value => rfl
    | fault reason => rfl
    | jumped target value after =>
      by_cases catches : target = id
      · by_cases typed : value.hasType ty = true
        · simpa [embed, controlSemantics, catches, typed] using ihNext (after.set id value)
        · simp [embed, controlSemantics, catches, typed]
      · simp [embed, catches]
  | jump target value =>
    cases h : value.eval env <;> simp [Control.Code.eval, controlSemantics, reference, h, embed]
  | ret value =>
    cases h : value.eval env <;> simp [Control.Code.eval, controlSemantics, reference, h, embed]
  | loop enabled _ _ _ | «repeat» enabled _ => cases enabled

theorem eval_eq_reference (code : Code) (args : List Value) (env : Env) :
    Code.eval code args env = reference code args env := by
  rw [Code.eval, eval_eq_embed]
  cases reference code args env <;> rfl

end Compiler.ZigAir.Scalar.ControlRefinement
