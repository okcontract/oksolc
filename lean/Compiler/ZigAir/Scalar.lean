/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Control

/-! Total semantics for the integer/control fragment of fresh Zig AIR. Memory,
calls, loops and ordinary Zig error unions are outside this vocabulary. Bounds
failure in unchecked arithmetic/casts is illegal behavior; checked operations
have a separate panic outcome. Neither becomes an ordinary returned value.
The structured program is finite, so evaluation needs no fuel or partial def.
Source-to-AIR and native backend preservation are separate obligations. -/
namespace Compiler.ZigAir.Scalar

inductive Ty where
  | int (signed : Bool) (width : Nat)
  | bool | unit
  deriving DecidableEq, Repr

def Ty.lower : Ty → Int
  | .int true (n + 1) => -(2 ^ n)
  | _ => 0

def Ty.upper : Ty → Int
  | .int true (n + 1) => 2 ^ n
  | .int false n => 2 ^ n
  | _ => 1

def Ty.contains (t : Ty) (x : Int) : Bool := decide (t.lower ≤ x ∧ x < t.upper)

inductive Value where
  | int (signed : Bool) (width : Nat) (value : Int)
  | bool (value : Bool)
  | unit
  deriving DecidableEq, Repr

def Value.type : Value → Ty
  | .int s n _ => .int s n
  | .bool _ => .bool
  | .unit => .unit

def Value.valid : Value → Bool
  | .int s n x => (Ty.int s n).contains x
  | _ => true

def Value.hasType (value : Value) (t : Ty) : Bool := decide (value.type = t) && value.valid

inductive Fault where
  | malformed | illegalBehavior | safetyPanic
  deriving DecidableEq, Repr

abbrev Result := Except Fault Value
abbrev Env := Control.Env Value

abbrev Env.set (env : Env) (id : Nat) (value : Value) : Env :=
  Control.Env.set env id value

inductive Ref where
  | local (id : Nat)
  | constant (value : Value)
  deriving DecidableEq, Repr

def Ref.eval (ref : Ref) (env : Env) : Result :=
  match ref with
  | .constant value => if value.valid then .ok value else .error .malformed
  | .local id => match env id with
    | none => .error .malformed
    | some value => if value.valid then .ok value else .error .malformed

inductive Arithmetic where | add | sub | mul deriving DecidableEq, Repr
inductive Overflow where | unchecked | checked | wrapping deriving DecidableEq, Repr
inductive Comparison where | eq | ne | lt | le | gt | ge deriving DecidableEq, Repr
inductive Cast where | unchecked | checked | bitcast | trunc deriving DecidableEq, Repr

def Arithmetic.eval : Arithmetic → Int → Int → Int
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .mul, x, y => x * y

def Comparison.eval : Comparison → Int → Int → Bool
  | .eq, x, y => decide (x = y)
  | .ne, x, y => decide (x ≠ y)
  | .lt, x, y => decide (x < y)
  | .le, x, y => decide (x ≤ y)
  | .gt, x, y => decide (x > y)
  | .ge, x, y => decide (x ≥ y)

/-- Interpret low bits using the destination's signedness. -/
def normalize (signed : Bool) (width : Nat) (x : Int) : Int :=
  let modulus : Int := 2 ^ width
  let residue := x % modulus
  if signed && decide (width > 0 ∧ residue ≥ 2 ^ (width - 1)) then residue - modulus else residue

def integer (signed : Bool) (width : Nat) (x : Int) (mode : Overflow) : Result :=
  if mode = .wrapping then .ok (.int signed width (normalize signed width x))
  else if (Ty.int signed width).contains x then .ok (.int signed width x)
  else .error (if mode = .checked then .safetyPanic else .illegalBehavior)

/-- Width of Zig's unsigned shift count for a positive-width integer.
Zero-width left operands are rejected separately. -/
def shiftCountWidth (width : Nat) : Nat :=
  if width ≤ 1 then 0 else (width - 1).log2 + 1

inductive Prim where
  | argument (index : Nat)
  | arithmetic (op : Arithmetic) (mode : Overflow) (left right : Ref)
  | bitAnd (left right : Ref)
  | bitXor (left right : Ref)
  | shiftRight (left right : Ref)
  | comparison (op : Comparison) (left right : Ref)
  | cast (op : Cast) (destination : Ty) (operand : Ref)
  deriving DecidableEq, Repr

def Prim.eval (prim : Prim) (args : List Value) (env : Env) : Result := do
  match prim with
  | .argument index =>
    match args[index]? with
    | none => .error .malformed
    | some value => if value.valid then .ok value else .error .malformed
  | .arithmetic op mode left right =>
    let .int s n x ← left.eval env | .error .malformed
    let .int t m y ← right.eval env | .error .malformed
    if s = t ∧ n = m then integer s n (op.eval x y) mode else .error .malformed
  | .comparison op left right =>
    let .int s n x ← left.eval env | .error .malformed
    let .int t m y ← right.eval env | .error .malformed
    if s = t ∧ n = m then .ok (.bool (op.eval x y)) else .error .malformed
  | .bitAnd left right =>
    let .int false n x ← left.eval env | .error .malformed
    let .int false m y ← right.eval env | .error .malformed
    if n = m then .ok (.int false n (x.toNat &&& y.toNat)) else .error .malformed
  | .bitXor left right =>
    let .int false n x ← left.eval env | .error .malformed
    let .int false m y ← right.eval env | .error .malformed
    if n = m then .ok (.int false n (x.toNat ^^^ y.toNat)) else .error .malformed
  | .shiftRight left right =>
    let .int false n x ← left.eval env | .error .malformed
    let .int false m y ← right.eval env | .error .malformed
    if n = 0 ∨ m ≠ shiftCountWidth n then .error .malformed
    else if y.toNat < n then .ok (.int false n (x.toNat >>> y.toNat))
    else .error .illegalBehavior
  | .cast op destination operand =>
    let .int s n x ← operand.eval env | .error .malformed
    let .int t m := destination | .error .malformed
    match op with
    | .unchecked => integer t m x .unchecked
    | .checked => integer t m x .checked
    | .bitcast =>
      if n = m then integer t m x .wrapping else .error .malformed
    | .trunc =>
      if s = t ∧ m ≤ n then integer t m x .wrapping else .error .malformed

abbrev Code := Control.Code Ty Prim Ref

inductive Outcome where
  | returned (value : Value)
  | jumped (target : Nat) (value : Value) (env : Env)
  | fault (reason : Fault)

def controlSemantics : Control.Semantics Ty Prim Ref Value Fault Unit where
  hasType := Value.hasType
  truth := fun value => match value with | .bool flag => some flag | _ => none
  evalRef := Ref.eval
  evalPrim := fun prim args env state => (prim.eval args env, state)
  malformed := .malformed

def Outcome.ofControl : Control.Outcome Value Fault Unit → Outcome
  | .returned value _ => .returned value
  | .jumped target value env _ => .jumped target value env
  | .fault reason _ => .fault reason

def Code.eval (code : Code) (args : List Value) (env : Env) : Outcome :=
  Outcome.ofControl (Control.Code.eval controlSemantics code args env ())

structure Program where
  parameters : List Ty
  returnType : Ty
  body : Code
  deriving DecidableEq, Repr

def Program.run (program : Program) (args : List Value) : Result :=
  if args.length = program.parameters.length &&
      (args.zip program.parameters).all (fun (value, type) => value.hasType type) then
    match program.body.eval args (fun _ => none) with
    | .returned value => if value.hasType program.returnType then .ok value else .error .malformed
    | .fault reason => .error reason
    | .jumped .. => .error .malformed
  else .error .malformed

end Compiler.ZigAir.Scalar
