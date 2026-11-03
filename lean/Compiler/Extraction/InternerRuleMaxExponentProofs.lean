/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RuleMaxExponentProgram
import Compiler.Extraction.DispatchExponentProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Dispatch (opAND opISZERO opSUB)

/-- Source projection of the shared helper, with no additional constructor or
assumed effect law. The surrounding EVM stage's return is reduced separately. -/
theorem helper_projection (c : Compiler.Extraction.Associative.Constructors Debug (Effect Heap Error))
    (operand : NodeId) (debug : Debug) :
    Compiler.Extraction.Dispatch.maxExponent c (fun one debug => c.operation opAND [operand, one] debug) debug =
      (do let one ← c.constant 1 debug
          let odd ← c.operation opAND [operand, one] debug
          let even ← c.operation opISZERO [odd] debug
          return some (← c.operation opSUB [even, odd] debug)) := rfl

theorem parity_initializer (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (one operand : NodeId) (before : World σ)
    (inside : 1 < source.length)
    (loaded : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 1) = .ok (number operand)) :
    parity external budget allocator p q source one before =
      invoke external budget allocator p q opAND operand one before :=
  borrowedFirst_of_load _ _ _ _ _ _ _ _ _ _ _ inside loaded

theorem even_initializer (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (odd : NodeId) :
    (constructors constant external budget allocator p q).operation opISZERO [odd] () =
      TemporaryUnary.invoke external budget allocator p q opISZERO odd := rfl

theorem final_initializer (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (even odd : NodeId) :
    (constructors constant external budget allocator p q).operation opSUB [even, odd] () =
      invoke external budget allocator p q opSUB even odd := rfl

theorem constant_error (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before reached : World σ) (fault : Fault) (failed : constant 1 before = (.error fault, reached)) :
    zigChain constant external budget allocator p q source before = (.error fault, reached) :=
  Effect.bind_failure _ _ _ _ _ failed

theorem after_constant (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before middle : World σ) (one : NodeId) (returned : constant 1 before = (.ok one, middle)) :
    zigChain constant external budget allocator p q source before =
      (do let odd ← parity external budget allocator p q source one
          let even ← TemporaryUnary.invoke external budget allocator p q opISZERO odd
          return some (← invoke external budget allocator p q opSUB even odd)) middle :=
  Effect.bind_success _ _ _ _ _ returned

theorem parity_error (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before middle reached : World σ) (one : NodeId) (fault : Fault)
    (returned : constant 1 before = (.ok one, middle))
    (failed : parity external budget allocator p q source one middle = (.error fault, reached)) :
    zigChain constant external budget allocator p q source before = (.error fault, reached) := by
  rw [after_constant _ _ _ _ _ _ _ _ _ _ returned]
  exact Effect.bind_failure _ _ _ _ _ failed

theorem after_parity (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before middle reached : World σ) (one odd : NodeId)
    (constantReturned : constant 1 before = (.ok one, middle))
    (returned : parity external budget allocator p q source one middle = (.ok odd, reached)) :
    zigChain constant external budget allocator p q source before =
      (do let even ← TemporaryUnary.invoke external budget allocator p q opISZERO odd
          return some (← invoke external budget allocator p q opSUB even odd)) reached := by
  rw [after_constant _ _ _ _ _ _ _ _ _ _ constantReturned]
  exact Effect.bind_success _ _ _ _ _ returned

theorem even_error (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before middle afterOdd reached : World σ) (one odd : NodeId) (fault : Fault)
    (constantReturned : constant 1 before = (.ok one, middle))
    (parityReturned : parity external budget allocator p q source one middle = (.ok odd, afterOdd))
    (failed : TemporaryUnary.invoke external budget allocator p q opISZERO odd afterOdd = (.error fault, reached)) :
    zigChain constant external budget allocator p q source before = (.error fault, reached) := by
  rw [after_parity _ _ _ _ _ _ _ _ _ _ _ _ constantReturned parityReturned]
  exact Effect.bind_failure _ _ _ _ _ failed

theorem after_even (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before middle afterOdd reached : World σ) (one odd even : NodeId)
    (constantReturned : constant 1 before = (.ok one, middle))
    (parityReturned : parity external budget allocator p q source one middle = (.ok odd, afterOdd))
    (returned : TemporaryUnary.invoke external budget allocator p q opISZERO odd afterOdd = (.ok even, reached)) :
    zigChain constant external budget allocator p q source before =
      Effect.bind (invoke external budget allocator p q opSUB even odd)
        (fun id => Effect.pure (some id)) reached := by
  rw [after_parity _ _ _ _ _ _ _ _ _ _ _ _ constantReturned parityReturned]
  exact Effect.bind_success _ _ _ _ _ returned

theorem final_error (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before middle afterOdd afterEven reached : World σ) (one odd even : NodeId) (fault : Fault)
    (constantReturned : constant 1 before = (.ok one, middle))
    (parityReturned : parity external budget allocator p q source one middle = (.ok odd, afterOdd))
    (evenReturned : TemporaryUnary.invoke external budget allocator p q opISZERO odd afterOdd = (.ok even, afterEven))
    (failed : invoke external budget allocator p q opSUB even odd afterEven = (.error fault, reached)) :
    zigChain constant external budget allocator p q source before = (.error fault, reached) := by
  rw [after_even _ _ _ _ _ _ _ _ _ _ _ _ _ _ constantReturned parityReturned evenReturned]
  exact Effect.bind_failure _ _ _ _ _ failed

theorem success (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View)
    (before middle afterOdd afterEven reached : World σ) (one odd even result : NodeId)
    (constantReturned : constant 1 before = (.ok one, middle))
    (parityReturned : parity external budget allocator p q source one middle = (.ok odd, afterOdd))
    (evenReturned : TemporaryUnary.invoke external budget allocator p q opISZERO odd afterOdd = (.ok even, afterEven))
    (returned : invoke external budget allocator p q opSUB even odd afterEven = (.ok result, reached)) :
    zigChain constant external budget allocator p q source before = (.ok (some result), reached) := by
  rw [after_even _ _ _ _ _ _ _ _ _ _ _ _ _ _ constantReturned parityReturned evenReturned]
  exact Effect.bind_success _ _ _ _ _ returned

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent
