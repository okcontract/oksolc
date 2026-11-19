/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Yul.Expression
import Contract.Interaction.Eval

/-! Closed arithmetic vocabulary of the production constant folder. The
specification reuses the language's word operations; the implementation
interpreter additionally observes bounds faults, invalid narrowing and Zig's
undefined integer operations. These outcomes are never ordinary `null` folds.
This models integer execution, not allocator or native-code correctness. -/
namespace Compiler.Extraction.Folding
open Contract.Yul

inductive Op where
  | add | mul | sub | div | sdiv | mod | smod | exp | not | lt | gt | slt | sgt
  | eq | iszero | and | or | xor | byte | addmod | mulmod | signextend | shl | shr
  deriving DecidableEq, Repr

def Op.arity : Op → Nat
  | .not | .iszero => 1
  | .addmod | .mulmod => 3
  | _ => 2

def Op.opcode : Op → BitVec 8
  | .add => 0x01 | .mul => 0x02 | .sub => 0x03 | .div => 0x04 | .sdiv => 0x05
  | .mod => 0x06 | .smod => 0x07 | .addmod => 0x08 | .mulmod => 0x09 | .exp => 0x0a
  | .signextend => 0x0b | .lt => 0x10 | .gt => 0x11 | .slt => 0x12 | .sgt => 0x13
  | .eq => 0x14 | .iszero => 0x15 | .and => 0x16 | .or => 0x17 | .xor => 0x18
  | .not => 0x19 | .byte => 0x1a | .shl => 0x1b | .shr => 0x1c

/-- Independent EVM value specification, including full-precision modular
arithmetic and signed division/remainder rounded toward zero. -/
def Op.value (op : Op) (a b c : Word) : Word := match op with
  | .add => Binary.add.eval a b
  | .mul => Binary.mul.eval a b
  | .sub => Binary.sub.eval a b
  | .div => Binary.div.eval a b
  | .mod => Binary.mod.eval a b
  | .sdiv => BitVec.ofInt 256 (a.toInt.tdiv b.toInt)
  | .smod => if b = 0 then 0 else BitVec.ofInt 256 (a.toInt.tmod b.toInt)
  | .exp => Contract.Interaction.WordPower.pow a b.toNat
  | .not => Unary.bitnot.eval a
  | .lt => Binary.lt.eval a b
  | .gt => Binary.gt.eval a b
  | .slt => if a.toInt < b.toInt then 1 else 0
  | .sgt => if b.toInt < a.toInt then 1 else 0
  | .eq => Binary.eq.eval a b
  | .iszero => Unary.iszero.eval a
  | .and => Binary.and.eval a b
  | .or => Binary.or.eval a b
  | .xor => Binary.xor.eval a b
  | .byte => if a.toNat < 32 then (b >>> (8 * (31 - a.toNat))) &&& 255 else 0
  | .addmod => if c = 0 then 0 else BitVec.ofNat 256 ((a.toNat + b.toNat) % c.toNat)
  | .mulmod => if c = 0 then 0 else BitVec.ofNat 256 ((a.toNat * b.toNat) % c.toNat)
  | .signextend => if a.toNat < 31 then (b.setWidth (8 * (a.toNat + 1))).signExtend 256 else b
  | .shl => Binary.shl.eval a b
  | .shr => Binary.shr.eval a b

def Op.eval (op : Op) (args : List Word) : Option Word :=
  if args.length = op.arity then some (op.value (args[0]?.getD 0) (args[1]?.getD 0) (args[2]?.getD 0))
  else none

inductive Fault where
  | bounds | divisionByZero | signedOverflow | integerOverflow | invalidCast | recursionLimit
  deriving DecidableEq, Repr

abbrev Result := Except Fault Word

namespace Zig

def narrow (width value : Nat) : Except Fault Nat :=
  if value < 2 ^ width then .ok value else .error .invalidCast

def checkedSub (a b : Nat) : Except Fault Nat :=
  if b ≤ a then .ok (a - b) else .error .integerOverflow

def checkedAdd (width a b : Nat) : Except Fault Nat :=
  if a + b < 2 ^ width then .ok (a + b) else .error .integerOverflow

def checkedMul (width a b : Nat) : Except Fault Nat :=
  if a * b < 2 ^ width then .ok (a * b) else .error .integerOverflow

def divTrunc (a b : Word) : Result :=
  if b = 0 then .error .divisionByZero
  else if a.toInt = -(2 ^ 255) ∧ b.toInt = -1 then .error .signedOverflow
  else .ok (BitVec.ofInt 256 (a.toInt.tdiv b.toInt))

def rem (a b : Word) : Result :=
  if b = 0 then .error .divisionByZero
  else if a.toInt = -(2 ^ 255) ∧ b.toInt = -1 then .error .signedOverflow
  else .ok (BitVec.ofInt 256 (a.toInt.tmod b.toInt))

end Zig

/-- Bodies are generated from the admitted helper source, not supplied as
correctness contracts. Each callback still returns explicit arithmetic faults. -/
structure Helpers where
  sdiv : Word → Word → Result
  smod : Word → Word → Result
  exp : Word → Word → Result
  byte : Word → Word → Result
  addmod : Word → Word → Word → Result
  mulmod : Word → Word → Word → Result
  signextend : Word → Word → Result
  shl : Word → Word → Result
  shr : Word → Word → Result

def primitive (helpers : Helpers) (op : Op) (args : List Word) : Result :=
  if args.length ≠ op.arity then .error .bounds else
  let a := args[0]?.getD 0
  let b := args[1]?.getD 0
  let c := args[2]?.getD 0
  match op with
  | .div => if b = 0 then .error .divisionByZero else .ok (a / b)
  | .mod => if b = 0 then .error .divisionByZero else .ok (a % b)
  | .sdiv => helpers.sdiv a b
  | .smod => helpers.smod a b
  | .exp => helpers.exp a b
  | .byte => helpers.byte a b
  | .addmod => helpers.addmod a b c
  | .mulmod => helpers.mulmod a b c
  | .signextend => helpers.signextend a b
  | .shl => helpers.shl a b
  | .shr => helpers.shr a b
  | _ => .ok (op.value a b c)

structure Body where
  op : Op
  indices : List Nat
  zeroGuard : Option (Nat × Word) := none

def argument (args : List Word) (index : Nat) : Result :=
  match args[index]? with
  | some value => .ok value
  | none => .error .bounds

def Body.run (helpers : Helpers) (body : Body) (args : List Word) : Result := do
  match body.zeroGuard with
  | some (index, value) => if (← argument args index) = 0 then return value
  | none => pure ()
  let values ← body.indices.mapM (argument args)
  primitive helpers body.op values

structure Clause where
  opcode : BitVec 8
  arity : Nat
  body : Body

def run (helpers : Helpers) (clauses : List Clause) (opcode : BitVec 8)
    (args : List Word) : Except Fault (Option Word) :=
  match clauses with
  | [] => .ok none
  | clause :: rest =>
    if opcode = clause.opcode then
      if args.length = clause.arity then (clause.body.run helpers args).map some else .ok none
    else run helpers rest opcode args

end Compiler.Extraction.Folding
