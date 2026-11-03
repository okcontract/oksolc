/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryUnary
import Compiler.Extraction.DispatchProgram

-- Generated constructor segment of the complete simplifyWithOptions owner.
-- Query/condition admission and native graph correspondence remain open.
-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- EVM versions SHA-256: 5e84058712718707559b37b4129377fd03a336ef04bd35325060799760c7bcd4

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

/-- Only the two remaining operation sites of this branch are admitted. The
constant constructor is supplied by the retained production prefix. -/
def constructors (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) :
    Compiler.Extraction.Associative.Constructors Unit (GraphAction σ) where
  constant := fun value _ => constant value
  operation := fun opcode values _ => match values with
    | [odd] => if opcode == Compiler.Extraction.Dispatch.opISZERO then
        TemporaryUnary.invoke external budget allocator p q opcode odd
      else fun before => (.error .outsideOwnedContinuation, before)
    | [even, odd] => if opcode == Compiler.Extraction.Dispatch.opSUB then
        invoke external budget allocator p q opcode even odd
      else fun before => (.error .outsideOwnedContinuation, before)
    | _ => fun before => (.error .outsideOwnedContinuation, before)
  materialize := fun _ _ _ before => (.error .outsideOwnedContinuation, before)

/-- The parity callback reads arguments[1] in the world returned by constant.
It then allocates and initializes the actual pair, never a final-ID snapshot. -/
def parity (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (one : NodeId) : GraphAction σ NodeId :=
  borrowedFirst external budget allocator p q Compiler.Extraction.Dispatch.opAND source 1 one

def zigChain (constant : Word → GraphAction σ NodeId) (external : External σ)
    (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) (source : View) :
    GraphAction σ (Option NodeId) :=
  Compiler.Extraction.Dispatch.maxExponent (constructors constant external budget allocator p q)
    (fun one _ => parity external budget allocator p q source one) ()

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryArguments.MaxExponent
