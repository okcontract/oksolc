/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPairInput
import Compiler.Extraction.RuleShiftInputProgram

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- EVM versions SHA-256: 5e84058712718707559b37b4129377fd03a336ef04bd35325060799760c7bcd4

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.LiteralInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

private abbrev read := @ShiftInput.operand

/-- Exact literal segments after their enclosing source queries and guards.
Native views are read in source order through the reached world. Scalar locals
and successful guard/query selection still require their native correspondence.
Together with RulePairInputProgram this covers all 53 nonempty RuleList literals;
it does not cover local arrays or borrowed/forwarded constructor arguments. -/
def sameSignextend (context : PairInput.Context σ) (left : NodeId) (inner : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSIGNEXTEND [left, ← read inner 1] debug

def minimumSignextend (context : PairInput.Context σ) (outerByte innerByte : Word) (inner : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSIGNEXTEND [← c.constant (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug, ← read inner 1] debug

def modularMultiply (context : PairInput.Context σ) (nested : View) (right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opMULMOD [← read nested 0, ← read nested 1, right] debug

def modularAdd (context : PairInput.Context σ) (nested : View) (right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opADDMOD [← read nested 0, ← read nested 1, right] debug

def sameDirectionShift (context : PairInput.Context σ) (instruction : Opcode) (outerShift innerShift : Word) (inner : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation instruction [← c.constant (← Dispatch.addWord outerShift innerShift) debug, ← read inner 1] debug

def andShifted (context : PairInput.Context σ) (lhs rhs : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opAND [← read lhs 1, ← read rhs 1] debug

def restoreShift (context : PairInput.Context σ) (lhs : View) (combined : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSHL [← read lhs 0, combined] debug

def divideShift (context : PairInput.Context σ) (shift : View) (left : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSHR [← read shift 0, left] debug

def byteLeftShift (context : PairInput.Context σ) (index amount : Word) (shift : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opBYTE [← c.constant (← Dispatch.addWord index (amount / 8)) debug, ← read shift 1] debug

def byteRightShift (context : PairInput.Context σ) (index amount : Word) (shift : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opBYTE [← c.constant (← Dispatch.subWord index (amount / 8)) debug, ← read shift 1] debug

def shiftSignextend (context : PairInput.Context σ) (left : NodeId) (signExtend : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSHL [left, ← read signExtend 1] debug

def arithmeticShift (context : PairInput.Context σ) (shift : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSAR [← read shift 0, ← read shift 1] debug

def leftSubtractRightConstant (context : PairInput.Context σ) (nested : View) (right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSUB [← read nested 0, right] debug

def subtractMaterializedRight (context : PairInput.Context σ) (difference : NodeId) (nested : View) (constant : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSUB [difference, ← c.materialize (← read nested 1) constant debug] debug

def leftSubtractLeftConstant (context : PairInput.Context σ) (nested : View) (right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opADD [← read nested 1, right] debug

def subtractMaterializedLeft (context : PairInput.Context σ) (nested : View) (constant : Word) (sum : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSUB [← c.materialize (← read nested 0) constant debug, sum] debug

def rightSubtractRightConstant (context : PairInput.Context σ) (left : NodeId) (nested : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSUB [left, ← read nested 0] debug

def rightSubtractLeftConstant (context : PairInput.Context σ) (left : NodeId) (nested : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opADD [left, ← read nested 1] debug

def tripleIszero (context : PairInput.Context σ) (third : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opISZERO [← read third 0] debug

def exponentZero (context : PairInput.Context σ) (arguments : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opISZERO [← read arguments 1] debug

def exponentTwo (context : PairInput.Context σ) (arguments : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := ShiftInput.zigLiteral context .exponentTwo 0 arguments debug

def exponentParity (context : PairInput.Context σ) (arguments : View) (one : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opAND [← read arguments 1, one] debug

def exponentEven (context : PairInput.Context σ) (parity : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opISZERO [parity] debug

def multiplyLeft (context : PairInput.Context σ) (power : Nat) (arguments : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := ShiftInput.zigLiteral context .multiplyLeft power arguments debug

def multiplyRight (context : PairInput.Context σ) (power : Nat) (arguments : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := ShiftInput.zigLiteral context .multiplyRight power arguments debug

def divide (context : PairInput.Context σ) (power : Nat) (arguments : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := ShiftInput.zigLiteral context .divide power arguments debug

def doubleIszeroFirst (context : PairInput.Context σ) (value : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opISZERO [value] debug

def doubleIszeroSecond (context : PairInput.Context σ) (inner : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opISZERO [inner] debug

def signextendMask (context : PairInput.Context σ) (materializedMask : NodeId) (signExtend : View)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opAND [materializedMask, ← read signExtend 1] debug

def alternatingLeft (context : PairInput.Context σ) (inner : View) (expressionIndex : Nat) (innerMask outerMask : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opAND [← read inner expressionIndex, ← c.constant (innerMask &&& outerMask) debug] debug

def alternatingRight (context : PairInput.Context σ) (alternatives : View) (innerIndex : Nat) (materializedMask : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opAND [← read alternatives (← Dispatch.arithmetic (Folding.Zig.checkedSub 1 innerIndex)), materializedMask] debug

def shiftProduct (context : PairInput.Context σ) (shift : View) (value : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := PairInput.constructors context
  c.operation Dispatch.opSHL [← read shift 0, value] debug

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.LiteralInput
