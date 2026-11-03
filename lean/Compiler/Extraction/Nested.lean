/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageOperations
import Compiler.Extraction.WordMeaning

namespace Compiler.Extraction.Nested
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

abbrev Equal := NodeId → NodeId → Bool

structure Reads where
  constant : NodeId → Except ReadError (Option Word)
  operation : NodeId → Opcode → Except ReadError (Option ArgumentSlice)
  overrideEquality : Option Equal := none

structure ConstantOperand where
  expression : NodeId
  constantExpression : NodeId
  value : Word

/-- An indexed source read at its evaluation position. The last argument is
the logical annotation, not the native result: physical interpretations ignore
it and load the retained slice in the reached world. -/
abbrev OperandRead (m : Type → Type) := ArgumentSlice → Nat → NodeId → m NodeId

abbrev logicalOperand [Monad m] : OperandRead m := fun _ _ value => pure value

/-- Concrete specialization of the compiler's expression classes. The Yul
adapter has different equality/lookup implementations and needs its own proof. -/
def storageReads (cells : List Cell) : Reads :=
  ⟨constantProgram.run cells, operationProgram.run cells, none⟩

end Compiler.Extraction.Nested
