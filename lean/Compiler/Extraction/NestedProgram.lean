/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Nested

namespace Compiler.Extraction.Nested
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def nestedNotOpcode : Opcode := 25

def sameExpression (reads : Reads) (left right : NodeId) : Bool :=
  match reads.overrideEquality with
  | some equal => equal left right
  | none => left == right

def splitConstant (reads : Reads) (arguments : List NodeId) : Except ReadError (Option ConstantOperand) := do
  match arguments with
  | [left, right] =>
    if let some value ← reads.constant right then return some ⟨left, right, value⟩
    if let some value ← reads.constant left then return some ⟨right, left, value⟩
    return none
  | _ => return none

def cancelNestedBinary (reads : Reads) (instruction : Opcode) (single nestedId : NodeId) :
    Except ReadError (Option NodeId) := do
  let some nested ← reads.operation nestedId instruction | return none
  match nested.items with
  | [left, right] =>
    if sameExpression reads left single then return some right
    if sameExpression reads right single then return some left
    return none
  | _ => return none

def absorbedOccurrence (reads : Reads) (single nestedId : NodeId) (instruction : Opcode) :
    Except ReadError (Option NodeId) := do
  let some nested ← reads.operation nestedId instruction | return none
  match nested.items with
  | [left, right] =>
    if sameExpression reads left single then return some left
    if sameExpression reads right single then return some right
    return none
  | _ => return none

def isNegation (reads : Reads) (value possibleNot : NodeId) : Except ReadError Bool := do
  let some arguments ← reads.operation possibleNot nestedNotOpcode | return false
  match arguments.items with
  | [operand] => return sameExpression reads operand value
  | _ => return false

end Compiler.Extraction.Nested
