/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPairInput

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- EVM versions SHA-256: 5e84058712718707559b37b4129377fd03a336ef04bd35325060799760c7bcd4

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Source literal segments following their enclosing queries and guards.
These typed arguments are the source's evaluated scalar locals. Native query
correspondence and guard selection are separate recursive obligations. -/
def byteLast (context : Context σ) (right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opAND right (← c.constant 255 debug) debug

def modPower (context : Context σ) (left : NodeId) (modulus : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opAND left (← c.constant (← Dispatch.subWord modulus 1) debug) debug

def maskedShift (context : Context σ) (instruction : Opcode) (left expression : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c instruction left expression debug

def shiftedMask (context : Context σ) (shifted : NodeId) (mask : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opAND shifted (← c.constant mask debug) debug

def shiftedSignextend (context : Context σ) (amount index : Word) (shifted : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opSIGNEXTEND (← c.constant (← Dispatch.addWord (amount >>> 3) index) debug) shifted debug

def subtractConstant (context : Context σ) (left : NodeId) (constant : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opADD left (← c.constant (0 - constant) debug) debug

def subtractLeftAdd (context : Context σ) (expression right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opSUB expression right debug

def addMaterializedDifference (context : Context σ) (difference original : NodeId) (value : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opADD difference (← c.materialize original value debug) debug

def subtractRightAdd (context : Context σ) (left expression : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opSUB left expression debug

def addNegatedDifference (context : Context σ) (difference : NodeId) (value : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opADD difference (← c.constant (0 - value) debug) debug

def addDifference (context : Context σ) (difference : NodeId) (constant : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opADD difference (← c.constant constant debug) debug

def addNegatedSum (context : Context σ) (sum : NodeId) (constant : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opADD sum (← c.constant (0 - constant) debug) debug

def maxParity (context : Context σ) (even parity : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opSUB even parity debug

def reassociateConstants (context : Context σ) (instruction : Opcode) (expression : NodeId) (value other : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c instruction expression (← c.constant (← Nested.readAction (Associative.combineConstants instruction value other)) debug) debug

def reassociateRight (context : Context σ) (instruction : Opcode) (other expression : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c instruction other expression debug

def reassociateLeft (context : Context σ) (instruction : Opcode) (expression other : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c instruction expression other debug

def reassociateMaterialized (context : Context σ) (instruction : Opcode) (inner original : NodeId) (value : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c instruction inner (← c.materialize original value debug) debug

def oppositeInner (context : Context σ) (opcode : Opcode) (inner outer : Word) (value : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c (OppositeShifts.oppositeOpcode opcode) (← c.constant (← Nested.readAction (OppositeShifts.checkedDifference inner outer)) debug) value debug

def oppositeOuter (context : Context σ) (opcode : Opcode) (outer inner : Word) (value : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c opcode (← c.constant (← Nested.readAction (OppositeShifts.checkedDifference outer inner)) debug) value debug

def oppositeMask (context : Context σ) (shifted : NodeId) (mask : Word)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opAND shifted (← c.constant mask debug) debug

def alternatingOr (context : Context σ) (left right : NodeId)
    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do
  let c := constructors context
  ConstructorPair.scalars c Dispatch.opOR left right debug

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput
