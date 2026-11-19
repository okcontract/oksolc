/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Std

/-! Shared structured AIR control. The default capability excludes back edges and
keeps the finite evaluator total; the loop machine uses the same syntax with
back edges enabled. Primitive evaluation retains state on
failure as well as success: a later fault does not undo earlier memory effects.
SSA references themselves are read-only. This is not a memory semantics; each
client supplies its primitive operations and value/type interpretation. -/
namespace Compiler.ZigAir.Control

abbrev Env (Value : Type) := Nat → Option Value

def Env.set (env : Env Value) (id : Nat) (value : Value) : Env Value :=
  fun query => if query = id then some value else env query

inductive Code (Ty Prim Ref : Type) (loops : Bool := false) where
  | bind (id : Nat) (type : Ty) (value : Prim) (next : Code Ty Prim Ref loops)
  | branch (condition : Ref) (yes no : Code Ty Prim Ref loops)
  | block (id : Nat) (type : Ty) (body next : Code Ty Prim Ref loops)
  | jump (target : Nat) (value : Ref)
  | ret (value : Ref)
  | loop (enabled : loops = true) (id : Nat) (body : Code Ty Prim Ref loops)
  | repeat (enabled : loops = true) (target : Nat)
  deriving DecidableEq, Repr

inductive Outcome (Value Fault State : Type) where
  | returned (value : Value) (state : State)
  | jumped (target : Nat) (value : Value) (env : Env Value) (state : State)
  | fault (reason : Fault) (state : State)

structure Semantics (Ty Prim Ref Value Fault State : Type) where
  hasType : Value → Ty → Bool
  truth : Value → Option Bool
  evalRef : Ref → Env Value → Except Fault Value
  evalPrim : Prim → List Value → Env Value → State → Except Fault Value × State
  malformed : Fault

def Code.eval (sem : Semantics Ty Prim Ref Value Fault State)
    (code : Code Ty Prim Ref) (args : List Value) (env : Env Value) (state : State) :
    Outcome Value Fault State :=
  match code with
  | .bind id type prim next =>
    let (result, after) := sem.evalPrim prim args env state
    match result with
    | .error error => .fault error after
    | .ok value =>
      if sem.hasType value type then next.eval sem args (env.set id value) after
      else .fault sem.malformed after
  | .branch condition yes no =>
    match sem.evalRef condition env with
    | .ok value => match sem.truth value with
      | some true => yes.eval sem args env state
      | some false => no.eval sem args env state
      | none => .fault sem.malformed state
    | .error error => .fault error state
  | .block id type body next =>
    match body.eval sem args env state with
    | .jumped target value afterEnv after =>
      if target = id then
        if sem.hasType value type then next.eval sem args (afterEnv.set id value) after
        else .fault sem.malformed after
      else .jumped target value afterEnv after
    | other => other
  | .jump target value =>
    match sem.evalRef value env with
    | .ok value => .jumped target value env state
    | .error error => .fault error state
  | .ret value =>
    match sem.evalRef value env with
    | .ok value => .returned value state
    | .error error => .fault error state
  | .loop enabled _ _ | .repeat enabled _ => nomatch enabled

/-- Enable the machine without changing any instruction or reference. -/
def Code.enableLoops : Code Ty Prim Ref → Code Ty Prim Ref true
  | .bind id ty prim next => .bind id ty prim next.enableLoops
  | .branch condition yes no => .branch condition yes.enableLoops no.enableLoops
  | .block id ty body next => .block id ty body.enableLoops next.enableLoops
  | .jump target value => .jump target value
  | .ret value => .ret value
  | .loop enabled _ _ | .repeat enabled _ => nomatch enabled

end Compiler.ZigAir.Control
