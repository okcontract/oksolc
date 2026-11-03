/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.Associative

namespace Compiler.Extraction.ConstructorPair
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Associative

/-- Shared source literal construction. Scalar operands are already evaluated
local values. A child action is evaluated in its original initializer position,
and the outer operation is entered only after that action succeeds. -/
abbrev scalars {m : Type → Type} (constructors : Constructors Debug m)
    (opcode : Opcode) (first second : NodeId) (debug : Debug) : m NodeId :=
  constructors.operation opcode [first, second] debug

def first {m : Type → Type} [Monad m] (constructors : Constructors Debug m)
    (opcode : Opcode) (child : m NodeId) (second : NodeId) (debug : Debug) : m NodeId := do
  let value ← child
  constructors.operation opcode [value, second] debug

def second {m : Type → Type} [Monad m] (constructors : Constructors Debug m)
    (opcode : Opcode) (first : NodeId) (child : m NodeId) (debug : Debug) : m NodeId := do
  let value ← child
  constructors.operation opcode [first, value] debug

end Compiler.Extraction.ConstructorPair
