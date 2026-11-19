/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedConstruction

namespace Compiler.Extraction.Nested
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner Contract.Yul

variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def nestedIszeroOpcode : Opcode := 21

def doubleIsZero (build : OperationBuilder Debug m) (value : NodeId) (debug : Debug) : m NodeId := do
  let inner ← build nestedIszeroOpcode [value] debug
  build nestedIszeroOpcode [inner] debug

def repeatedIndex (reads : Reads) (left right repeated : NodeId) : Option Nat :=
  if sameExpression reads right repeated then some 1
  else if sameExpression reads left repeated then some 0
  else none

def repeatedOperands (reads : Reads) (left right repeated : NodeId) (repeatedIsFirst : Bool) : Option (List NodeId) :=
  (repeatedIndex reads left right repeated).map
    (fun selected => localArguments ⟨0, [left, right]⟩ selected repeated repeatedIsFirst)

def dropRepeatedLocal (reads : Reads) (localBuild : LocalOperationBuilder Debug m) (instruction : Opcode)
    (nestedId repeated : NodeId) (repeatedIsFirst : Bool) (debug : Debug)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some nested ← query (fun reads => reads.operation nestedId instruction) | return none
  match nested.items with
  | [left, right] =>
    let some selected := repeatedIndex reads left right repeated | return none
    return some (← localBuild instruction nested selected repeated repeatedIsFirst debug)
  | _ => return none

/-- Storage-erasing specialization for existing logical clients. Both entries
execute the same admitted query/selection body above. -/
def dropRepeatedNested (reads : Reads) (build : OperationBuilder Debug m) (instruction : Opcode)
    (nestedId repeated : NodeId) (repeatedIsFirst : Bool) (debug : Debug) : m (Option NodeId) :=
  dropRepeatedLocal reads (localBuilder build) instruction nestedId repeated repeatedIsFirst debug


end Compiler.Extraction.Nested
