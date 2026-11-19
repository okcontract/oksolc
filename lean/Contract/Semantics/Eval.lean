/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Language.Basic

namespace Contract

structure Context where
  caller : BitVec 160 := 0
  self : BitVec 160 := 0

def Ty.equal : (t : Ty) → t.Value → t.Value → Bool
  | .word, a, b => a == b
  | .bool, a, b => a == b
  | .address, a, b => a == b

def Expr.eval (state : Storage slots) (ctx : Context) (env : Env vars) :
    Expr slots vars t → t.Value
  | .word n => n
  | .bool b => b
  | .address a => a
  | .var i => env.get i
  | .load slot => state slot
  | .caller => ctx.caller
  | .self => ctx.self
  | .add a b => a.eval state ctx env + b.eval state ctx env
  | .sub a b => a.eval state ctx env - b.eval state ctx env
  | .binary op a b => op.eval (a.eval state ctx env) (b.eval state ctx env)
  | .bitnot a => ~~~(a.eval state ctx env)
  | .lt a b => (a.eval state ctx env).ult (b.eval state ctx env)
  | .le a b => (a.eval state ctx env).ule (b.eval state ctx env)
  | .eq a b => Ty.equal _ (a.eval state ctx env) (b.eval state ctx env)
  | .not a => !(a.eval state ctx env)

def Exprs.eval (state : Storage slots) (ctx : Context) (env : Env vars) :
    Exprs slots vars ts → Env ts
  | .nil => .nil
  | .cons v vs => .cons (v.eval state ctx env) (vs.eval state ctx env)

def Env.words : Env ts → List (BitVec 256)
  | .nil => []
  | .cons (t := .word) v vs => v :: vs.words
  | .cons (t := .bool) v vs => (if v then 1 else 0) :: vs.words
  | .cons (t := .address) v vs => BitVec.ofNat 256 v.toNat :: vs.words

structure Log where
  emitter : BitVec 160
  topics : List (BitVec 256)
  data : List (BitVec 256)
  deriving DecidableEq, Repr

/-- A failure has no committed state. This models rollback of all earlier writes
in this invocation, not just the final statement. Gas/ABI/deployment are outside
this typed, call-free semantics and require separate claims. -/
inductive Outcome (slots : Nat) (returns : List Ty) where
  | success : Storage slots → Env returns → (logs : List Log := []) → Outcome slots returns
  | revert : Revert → Outcome slots returns

/-- A later failure discards every earlier log, just as it discards writes. -/
def Outcome.prependLogs (logs : List Log) : Outcome slots returns → Outcome slots returns
  | .success state values rest => .success state values (logs ++ rest)
  | .revert bytes => .revert bytes

def Stmt.eval (state : Storage slots) (ctx : Context) (env : Env vars) :
    Stmt slots returns vars → Outcome slots returns
  | .ret values => .success state (values.eval state ctx env)
  | .revert bytes => .revert bytes
  | .let_ value body => body.eval state ctx (.cons (value.eval state ctx env) env)
  | .assign i value next => next.eval state ctx (env.set i (value.eval state ctx env))
  | .checked op a b next =>
      match op.eval (a.eval state ctx env) (b.eval state ctx env) with
      | .ok result => next.eval state ctx (.cons result env)
      | .error bytes => .revert bytes
  | .assert_ condition next =>
      if condition.eval state ctx env then next.eval state ctx env else .revert (panic 1)
  | .store slot value next => next.eval (state.write slot (value.eval state ctx env)) ctx env
  | .branch cond yes no =>
      if cond.eval state ctx env then yes.eval state ctx env else no.eval state ctx env
  | .call helper args next =>
      match helper.eval state ctx (args.eval state ctx env) with
      | .revert bytes => .revert bytes
      | .success after values logs =>
          (next.eval after ctx (values.append env)).prependLogs logs
  | .emit _ topics data next =>
      (next.eval state ctx env).prependLogs [⟨ctx.self,
        (topics.eval state ctx env).words, (data.eval state ctx env).words⟩]

def Outcome.committed (before : Storage slots) : Outcome slots returns → Storage slots
  | .success after _ _ => after
  | .revert _ => before

def Outcome.logs : Outcome slots returns → List Log
  | .success _ _ logs => logs
  | .revert _ => []

/-- Proof fields can be attached without entering the executable representation.
This wrapper cannot make a false property true; constructing it requires a proof. -/
structure Proved (program : Program) (property : Program → Prop) where
  proof : property program

def Proved.erase {program : Program} {property : Program → Prop}
    (_ : Proved program property) : Program := program

theorem proof_erasure (a b : Proved program property) : a.erase = b.erase := rfl

theorem revert_rolls_back (before : Storage slots) (bytes : Revert) :
    (Outcome.revert (returns := returns) bytes).committed before = before := rfl

theorem store_then_revert (before : Storage slots) (ctx : Context) (env : Env vars)
    (slot : Fin slots) (value : Expr slots vars .word) (bytes : Revert) :
    (Stmt.store (returns := returns) slot value (.revert bytes)).eval before ctx env =
      .revert bytes := rfl

end Contract
