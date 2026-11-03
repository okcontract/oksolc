/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.TemporaryUnaryProgram
import Compiler.Extraction.ConstructionProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary
open Compiler.Algebraic Contract.Yul

/-- This adapter only supplies the admitted unary callback. The equality below
connects its temporary preparation to the existing extracted production body;
it does not assert the remaining native graph or recursive callback contracts. -/
def unaryBuilder (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) :
    Builder (Effect (World σ) Fault) Unit where
  makeConstant := fun _ _ before => (.error .outsideOwnedContinuation, before)
  makeOperation := fun opcode arguments _ => match arguments with
    | [operand] => invoke external budget allocator p q (Interner.buildOpcode opcode) operand
    | _ => fun before => (.error .outsideOwnedContinuation, before)

def UnaryFamily (replacement : Replacement) : Prop :=
  replacement = .not_right ∨ replacement = .iszero_left ∨ replacement = .iszero_right ∨
    replacement = .bool_left ∨ replacement = .bool_right

/-- Reuse the original source extraction, including its effectful binds. -/
theorem source_projection (replacement : Replacement) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (left right : NodeId) (admitted : UnaryFamily replacement) :
    zigUnary replacement external budget allocator p q left right =
      Compiler.Algebraic.zigApply replacement (unaryBuilder external budget allocator p q) left right () := by
  cases replacement <;> simp_all [UnaryFamily, zigUnary, Compiler.Algebraic.zigApply, unaryBuilder]

/-- No continuation (and therefore no second allocation) follows an error,
including a rejected observation. The exact first call's reached world survives. -/
theorem first_error (replacement : Replacement) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (left right : NodeId) (before reached : World σ) (fault : Fault)
    (boolean : replacement = .bool_left ∨ replacement = .bool_right)
    (failed : invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
      (if replacement == .bool_left then left else right) before = (.error fault, reached)) :
    zigUnary replacement external budget allocator p q left right before = (.error fault, reached) := by
  rcases boolean with rfl | rfl <;>
    change Effect.bind _ _ before = _ <;> simp only [Effect.bind, failed]

/-- State the same error frame using the actual first call as its result. Keeping
that call intact avoids normalizing an arbitrary reached world to match a pair. -/
theorem first_error_result (replacement : Replacement) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (left right : NodeId) (before : World σ) (fault : Fault)
    (boolean : replacement = .bool_left ∨ replacement = .bool_right)
    (failed : (invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
      (if replacement == .bool_left then left else right) before).1 = .error fault) :
    zigUnary replacement external budget allocator p q left right before =
      invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
        (if replacement == .bool_left then left else right) before := by
  let called := invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
    (if replacement == .bool_left then left else right) before
  have reached : called = (.error fault, called.2) := Prod.ext failed rfl
  exact (first_error replacement external budget allocator p q left right before called.2 fault boolean reached).trans reached.symm

/-- The second array is prepared only after the first call, from its actual
result and reached world. No final initialized buffer is assumed. -/
theorem after_first (replacement : Replacement) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (left right first : NodeId) (before middle : World σ)
    (boolean : replacement = .bool_left ∨ replacement = .bool_right)
    (returned : invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
      (if replacement == .bool_left then left else right) before = (.ok first, middle)) :
    zigUnary replacement external budget allocator p q left right before =
      invoke external budget allocator p q (Interner.buildOpcode .ISZERO) first middle := by
  rcases boolean with rfl | rfl <;>
    change Effect.bind _ _ before = _ <;> simp only [Effect.bind, returned]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary
