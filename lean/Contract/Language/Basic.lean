/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Language.Word

/-! The first executable fragment. Types and indices exclude unbound variables,
out-of-layout slots, and proof-valued runtime operands by construction. -/
namespace Contract

inductive Ty where
  | word | bool | address
  deriving DecidableEq, Repr

abbrev Ty.Value : Ty → Type
  | .word => BitVec 256
  | .bool => Bool
  | .address => BitVec 160

inductive Var : List Ty → Ty → Type where
  | here : Var (t :: ts) t
  | there : Var ts t → Var (s :: ts) t

inductive Env : List Ty → Type where
  | nil : Env []
  | cons : t.Value → Env ts → Env (t :: ts)

def Env.get : Env ts → Var ts t → t.Value
  | .cons v _, .here => v
  | .cons _ vs, .there i => vs.get i

def Env.set : Env ts → Var ts t → t.Value → Env ts
  | .cons _ vs, .here, value => .cons value vs
  | .cons v vs, .there i, value => .cons v (vs.set i value)

def Env.append : Env ts → Env us → Env (ts ++ us)
  | .nil, tail => tail
  | .cons value rest, tail => .cons value (rest.append tail)

abbrev Storage (slots : Nat) := Fin slots → BitVec 256

def Storage.write (state : Storage slots) (slot : Fin slots) (value : BitVec 256) :
    Storage slots := fun other => if other = slot then value else state other

inductive Expr (slots : Nat) (vars : List Ty) : Ty → Type where
  | word : BitVec 256 → Expr slots vars .word
  | bool : Bool → Expr slots vars .bool
  | address : BitVec 160 → Expr slots vars .address
  | var : Var vars t → Expr slots vars t
  | load : Fin slots → Expr slots vars .word
  | caller : Expr slots vars .address
  | self : Expr slots vars .address
  | add : Expr slots vars .word → Expr slots vars .word → Expr slots vars .word
  | sub : Expr slots vars .word → Expr slots vars .word → Expr slots vars .word
  | binary : WordOp → Expr slots vars .word → Expr slots vars .word → Expr slots vars .word
  | bitnot : Expr slots vars .word → Expr slots vars .word
  | lt : Expr slots vars .word → Expr slots vars .word → Expr slots vars .bool
  | le : Expr slots vars .word → Expr slots vars .word → Expr slots vars .bool
  | eq : Expr slots vars t → Expr slots vars t → Expr slots vars .bool
  | not : Expr slots vars .bool → Expr slots vars .bool

inductive Exprs (slots : Nat) (vars : List Ty) : List Ty → Type where
  | nil : Exprs slots vars []
  | cons : Expr slots vars t → Exprs slots vars ts → Exprs slots vars (t :: ts)

/-- Payloads are explicit ABI bytes. The empty payload is the default revert. -/
abbrev Revert := List UInt8

inductive Stmt (slots : Nat) : List Ty → List Ty → Type where
  | ret {returns vars} : Exprs slots vars returns → Stmt slots returns vars
  | revert {returns vars} : Revert → Stmt slots returns vars
  | let_ {returns vars t} : Expr slots vars t → Stmt slots returns (t :: vars) → Stmt slots returns vars
  | assign {returns vars t} : Var vars t → Expr slots vars t → Stmt slots returns vars → Stmt slots returns vars
  | checked {returns vars} : CheckedOp → Expr slots vars .word → Expr slots vars .word →
      Stmt slots returns (.word :: vars) → Stmt slots returns vars
  | assert_ {returns vars} : Expr slots vars .bool → Stmt slots returns vars → Stmt slots returns vars
  | store {returns vars} : Fin slots → Expr slots vars .word → Stmt slots returns vars →
      Stmt slots returns vars
  | branch {returns vars} : Expr slots vars .bool → Stmt slots returns vars → Stmt slots returns vars →
      Stmt slots returns vars
  /-- A helper is a finite closed typed body. It cannot refer to caller locals
  or itself; recursive call graphs are unrepresentable in the finite AST. -/
  | call {returns vars params results} : Stmt slots results params → Exprs slots vars params →
      Stmt slots returns (results ++ vars) → Stmt slots returns vars
  /-- Topics/data are static ABI words; topics are bounded by the EVM LOG0..4
  family. The bound is a compile-time proof, never a runtime witness. -/
  | emit {returns vars topics data} : topics.length ≤ 4 → Exprs slots vars topics → Exprs slots vars data →
      Stmt slots returns vars → Stmt slots returns vars

structure Param where
  name : String
  type : Ty

structure Function (slots : Nat) where
  name : String
  params : List Param
  returns : List Ty
  body : Stmt slots returns (params.map Param.type)

structure Program where
  name : String
  slots : List String
  constructorParams : List Param
  constructor : Stmt slots.length [] (constructorParams.map Param.type)
  functions : List (Function slots.length)

end Contract
