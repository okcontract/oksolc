/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Primitives

/-! Word-valued EVM-dialect Yul expression model covering all nullary, unary,
binary, and ternary pure/environmental operations optimized by `RuleList` and
`ExpressionClasses`. Operand order matches Yul and EVM stack top-first order
(in particular, shifts and `byte`/`signextend` take the shift/index first). -/
namespace Contract.Yul

inductive Nullary where
  | address | caller | origin | coinbase
  deriving DecidableEq, Repr

inductive Unary where
  | bitnot | iszero
  deriving DecidableEq, Repr

inductive Binary where
  | add | sub | mul | div | sdiv | mod | smod | exp | signextend
  | and | or | xor | byte | shl | shr | sar
  | lt | gt | slt | sgt | eq
  deriving DecidableEq, Repr

inductive Ternary where
  | addmod | mulmod
  deriving DecidableEq, Repr

def Nullary.name : Nullary → String
  | .address => "address"
  | .caller => "caller"
  | .origin => "origin"
  | .coinbase => "coinbase"

def Unary.name : Unary → String
  | .bitnot => "not"
  | .iszero => "iszero"

def Binary.name : Binary → String
  | .add => "add" | .sub => "sub" | .mul => "mul"
  | .div => "div" | .sdiv => "sdiv" | .mod => "mod" | .smod => "smod"
  | .exp => "exp" | .signextend => "signextend"
  | .and => "and" | .or => "or" | .xor => "xor" | .byte => "byte"
  | .shl => "shl" | .shr => "shr" | .sar => "sar"
  | .lt => "lt" | .gt => "gt" | .slt => "slt" | .sgt => "sgt" | .eq => "eq"

def Ternary.name : Ternary → String
  | .addmod => "addmod"
  | .mulmod => "mulmod"

def Nullary.eval (ctx : Context) : Nullary → Word
  | .address => ctx.self.toWord
  | .caller => ctx.caller.toWord
  | .origin => ctx.origin.toWord
  | .coinbase => ctx.coinbase.toWord

def Unary.eval : Unary → Word → Word
  | .bitnot, a => ~~~a
  | .iszero, a => boolWord (a == 0#256)

def Binary.eval : Binary → Word → Word → Word
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => evmDiv a b
  | .sdiv, a, b => evmSdiv a b
  | .mod, a, b => evmMod a b
  | .smod, a, b => evmSmod a b
  | .exp, a, b => evmExp a b
  | .signextend, a, b => evmSignextend a b
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .byte, a, b => evmByte a b
  | .shl, a, b => evmShl a b
  | .shr, a, b => evmShr a b
  | .sar, a, b => evmSar a b
  | .lt, a, b => boolWord (a.ult b)
  | .gt, a, b => boolWord (b.ult a)
  | .slt, a, b => boolWord (a.slt b)
  | .sgt, a, b => boolWord (b.slt a)
  | .eq, a, b => boolWord (a == b)

def Ternary.eval : Ternary → Word → Word → Word → Word
  | .addmod, a, b, m => evmAddmod a b m
  | .mulmod, a, b, m => evmMulmod a b m

theorem Nullary.eval_masked (ctx : Context) (op : Nullary) :
    op.eval ctx &&& addressMask = op.eval ctx := by
  cases op <;> exact Address.toWord_and_mask _

inductive Expression where
  | literal (value : Nat)
  | variable (name : String)
  | nullary (op : Nullary)
  | unary (op : Unary) (arg : Expression)
  | binary (op : Binary) (left right : Expression)
  | ternary (op : Ternary) (first second third : Expression)
  deriving DecidableEq, Repr

def Expression.render : Expression → String
  | .literal n => toString n
  | .variable name => "$" ++ name
  | .nullary op => op.name ++ "()"
  | .unary op a => op.name ++ "(" ++ a.render ++ ")"
  | .binary op a b => op.name ++ "(" ++ a.render ++ "," ++ b.render ++ ")"
  | .ternary op a b c => op.name ++ "(" ++ a.render ++ "," ++ b.render ++ "," ++ c.render ++ ")"

def Expression.eval (ctx : Context) (locals : String → Word) : Expression → Word
  | .literal n => BitVec.ofNat 256 n
  | .variable name => locals name
  | .nullary op => op.eval ctx
  | .unary op a => op.eval (a.eval ctx locals)
  | .binary op a b => op.eval (a.eval ctx locals) (b.eval ctx locals)
  | .ternary op a b c =>
    op.eval (a.eval ctx locals) (b.eval ctx locals) (c.eval ctx locals)

end Contract.Yul
