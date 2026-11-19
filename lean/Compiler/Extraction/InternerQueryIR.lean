/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.Interner

namespace Compiler.Extraction.Interner.Queries
open Compiler.Algebraic Compiler.Extraction.Cache

/-- The source's early AssemblyException precedes hasInstruction's assertion.
The assertion is a defined-execution precondition in every build mode. A failed
check is a model safety fault, never a cache miss or ordinary assembly error. -/
structure Determinism where
  verbatim : Kind
  rejectOnVerbatim : Bool
  instructionTest : Test
  checkShape : Bool
  plain : Bool
  opcodes : List Opcode
  selected : Bool
  fallback : Bool

def Determinism.run (code : Determinism) (item : Item) : Except Error Bool :=
  if (item.kind == code.verbatim) == code.rejectOnVerbatim then .error .assemblyException else
  let hasInstruction := code.instructionTest.run item
  if code.checkShape && (hasInstruction != item.instruction.isSome) then .error .safetyFault else
  if !hasInstruction then .ok code.plain else
  match item.instruction with
  | none => .error .invalidOptional
  | some opcode => .ok (if opcode ∈ code.opcodes then code.selected else code.fallback)

end Compiler.Extraction.Interner.Queries
