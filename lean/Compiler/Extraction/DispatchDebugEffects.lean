/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.DispatchInputEffects

namespace Compiler.Extraction.Dispatch.Effects
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Contract.Yul

variable {m n : Type → Type} [Monad m] [Monad n]
  [MonadLift (Except Interner.Error) m] [MonadLift (Except Interner.Error) n]

set_option maxRecDepth 8192 in
/-- The complete shared body, including indexed loads and arbitrary source
queries, forwards exactly the supplied debug value. This is a definitional
equality, not an additional assumption about child callbacks. -/
theorem simplify_at_debug (reads : Reads) (c : Associative.Constructors Debug m) (debug : Debug)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (options : Options)
    (operand : OperandRead m) (address : Nat) (query : QueryRead m) :
    simplifyOptionsWithInputs reads (atDebug c debug) usizeBits instruction arguments () options operand address query =
      simplifyOptionsWithInputs reads c usizeBits instruction arguments debug options operand address query := by
  rfl

variable (r : Effects m n) (rb : ReadBind r) (reads : Reads) (operand : OperandRead m)
  (inputs : Inputs r reads operand)
  {left : Associative.Constructors Debug m} {right : Associative.Constructors Debug n}
include rb inputs

/-- Reuse all dispatcher input and source-query proofs at the actual debug
value. The stronger all-debug relation remains a compatibility specialization. -/
theorem simplify_options_with_inputs_at (debug : Debug) (c : SourceConstructorsAt r reads debug left right)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (options : Options) (address : Nat)
    (root : SliceInput r operand ⟨address, arguments⟩) :
    r.related (simplifyOptionsWithInputs reads left usizeBits instruction arguments debug options operand address)
      (simplifyWithOptions reads right usizeBits instruction arguments debug options) := by
  simpa only [simplifyWithOptions, simplify_at_debug] using
    (simplify_options_with_inputs r rb reads operand inputs c usizeBits instruction arguments () options address root)

theorem simplify_with_inputs_at (debug : Debug) (c : SourceConstructorsAt r reads debug left right)
    (usizeBits : Nat) (instruction : Opcode) (arguments : List NodeId) (address : Nat)
    (root : SliceInput r operand ⟨address, arguments⟩) :
    r.related (simplifyWithInputs reads left usizeBits instruction arguments debug operand address)
      (Dispatch.simplify reads right usizeBits instruction arguments debug) :=
  simplify_options_with_inputs_at r rb reads operand inputs debug c usizeBits instruction arguments defaultOptions address root

end Compiler.Extraction.Dispatch.Effects
