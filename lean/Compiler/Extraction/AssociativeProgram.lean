/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ConstructorPair

namespace Compiler.Extraction.Associative
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul

variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def isAssociative (instruction : Opcode) : Bool := [1, 2, 22, 23, 24].contains instruction

def combineConstants (instruction : Opcode) (left right : Word) : Except ReadError Word :=
  if instruction == 1 then .ok (left + right) else
  if instruction == 2 then .ok (left * right) else
  if instruction == 22 then .ok (left &&& right) else
  if instruction == 23 then .ok (left ||| right) else
  if instruction == 24 then .ok (left ^^^ right) else
  .error .safetyFault

def materializeConstant (make : Word → Debug → m NodeId) (_ : NodeId) (value : Word) (debug : Debug) : m NodeId :=
  make value debug

def reassociate (reads : Reads) (constructors : Constructors Debug m) (instruction : Opcode)
    (nestedId other : NodeId) (nestedIsRight : Bool) (debug : Debug)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some nested ← query (fun reads => reads.operation nestedId instruction) | return none
  let some parts ← query (fun reads => splitConstant reads nested.items) | return none
  if let some otherConstant ← query (fun reads => reads.constant other) then
    let combined ← readAction (combineConstants instruction parts.value otherConstant)
    let constant ← constructors.constant combined debug
    return some (← ConstructorPair.scalars constructors instruction parts.expression constant debug)
  let inner ← if nestedIsRight then
    ConstructorPair.scalars constructors instruction other parts.expression debug
  else
    ConstructorPair.scalars constructors instruction parts.expression other debug
  let constant ← constructors.materialize parts.constantExpression parts.value debug
  return some (← ConstructorPair.scalars constructors instruction inner constant debug)

end Compiler.Extraction.Associative
