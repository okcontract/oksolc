/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Semantics.Eval

/-! The word-valued, effect-free EVM-dialect Yul expressions emitted by the
typed frontend. This is the exporter's expression representation, not a second
compiler. Statement evaluation, parsing and backend preservation are separate. -/
namespace Contract.Yul
abbrev Word := BitVec 256

inductive Unary where
  | bitnot | iszero
  deriving DecidableEq, Repr

inductive Binary where
  | add | sub | mul | div | mod | and | or | xor | shl | shr | lt | gt | eq
  deriving DecidableEq, Repr

def Unary.name : Unary → String
  | .bitnot => "not" | .iszero => "iszero"

def Binary.name : Binary → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .mod => "mod"
  | .and => "and" | .or => "or" | .xor => "xor" | .shl => "shl" | .shr => "shr"
  | .lt => "lt" | .gt => "gt" | .eq => "eq"

def boolWord (b : Bool) : Word := if b then 1 else 0

def Unary.eval : Unary → Word → Word
  | .bitnot, a => ~~~a
  | .iszero, a => boolWord (a == 0)

/-- Arguments follow Yul/EVM order: shifts receive the count first. Storage
reads are pure in this functional layer; metered EVM reads separately warm slots. -/
def Binary.eval : Binary → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => if b = 0 then 0 else a % b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shl, a, b => if a.toNat < 256 then b <<< a.toNat else 0
  | .shr, a, b => if a.toNat < 256 then b >>> a.toNat else 0
  | .lt, a, b => boolWord (a.ult b)
  | .gt, a, b => boolWord (b.ult a)
  | .eq, a, b => boolWord (a == b)

inductive Expression where
  | literal (value : Nat)
  | variable (name : String)
  | load (slot : Nat)
  | caller | self
  | unary (op : Unary) (arg : Expression)
  | binary (op : Binary) (left right : Expression)
  deriving Repr

def Expression.render : Expression → String
  | .literal n => toString n
  | .variable name => name
  | .load slot => s!"sload({slot})"
  | .caller => "caller()"
  | .self => "address()"
  | .unary op a => s!"{op.name}({a.render})"
  | .binary op a b => s!"{op.name}({a.render}, {b.render})"

def Expression.eval (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    Expression → Word
  | .literal n => BitVec.ofNat 256 n
  | .variable name => locals name
  | .load slot => storage (BitVec.ofNat 256 slot)
  | .caller => BitVec.ofNat 256 ctx.caller.toNat
  | .self => BitVec.ofNat 256 ctx.self.toNat
  | .unary op a => op.eval (a.eval storage ctx locals)
  | .binary op a b => op.eval (a.eval storage ctx locals) (b.eval storage ctx locals)

end Contract.Yul
