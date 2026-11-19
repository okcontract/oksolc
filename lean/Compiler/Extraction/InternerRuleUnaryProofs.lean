/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RuleUnaryProgram
import Compiler.Extraction.InternerTemporaryUnaryProofs
import Compiler.Extraction.DispatchProgram

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral
open Compiler.Algebraic Compiler.ZigAir.Memory.WordArray

theorem opcode_binding : Interner.buildOpcode .ISZERO = Compiler.Extraction.Dispatch.opISZERO := rfl

/-- The retained prefix supplies the actual borrowed view. This segment reads
its word before allocating, rather than using a logical query's final list. -/
theorem nested_initializer_from_load (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (operand parity : NodeId) (before : World σ)
    (inside : 0 < source.length)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 0) = .ok (number operand)) :
    zigLiteral .nestedIszero external budget allocator p q source parity before =
      (unaryBuilder external budget allocator p q).makeOperation .ISZERO [operand] () before := by
  exact BorrowedInput.invoke_of_load _ _ _ _ _ _ _ _ _ _ inside loaded

theorem exponent_initializer_from_load (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (operand parity : NodeId) (before : World σ)
    (inside : 1 < source.length)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 1) = .ok (number operand)) :
    zigLiteral .zeroBaseExponent external budget allocator p q source parity before =
      (unaryBuilder external budget allocator p q).makeOperation .ISZERO [operand] () before := by
  exact BorrowedInput.invoke_of_load _ _ _ _ _ _ _ _ _ _ inside loaded

theorem parity_initializer (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries)
    (source : View) (parity : NodeId) :
    zigLiteral .parity external budget allocator p q source parity =
      (unaryBuilder external budget allocator p q).makeOperation .ISZERO [parity] () := rfl

theorem child_error (child : GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (before reached : World σ) (fault : Fault)
    (failed : child before = (.error fault, reached)) :
    afterParity child external budget allocator p q before = (.error fault, reached) := by
  change Effect.bind _ _ before = _
  simp only [Effect.bind, failed]

theorem child_return (child : GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (before reached : World σ) (parity : NodeId)
    (returned : child before = (.ok parity, reached)) :
    afterParity child external budget allocator p q before =
      invoke external budget allocator p q (Interner.buildOpcode .ISZERO) parity reached := by
  change Effect.bind _ _ before = _
  simp only [Effect.bind, returned, zigLiteral]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral
