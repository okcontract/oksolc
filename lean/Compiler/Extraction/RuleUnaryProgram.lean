/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerBorrowedUnary

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral
open Compiler.Algebraic Compiler.ZigAir.Memory.WordArray

-- Generated literal segments from the complete admitted simplifyWithOptions owner.
-- Retained query/condition prefixes and parity construction are separate obligations.
-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- EVM versions SHA-256: 5e84058712718707559b37b4129377fd03a336ef04bd35325060799760c7bcd4
inductive Site where
  | nestedIszero | zeroBaseExponent | parity
  deriving DecidableEq, Repr

def zigLiteral (site : Site) (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (parity : NodeId) : GraphAction σ NodeId :=
  match site with
  | .nestedIszero => BorrowedInput.invoke external budget allocator p q (Interner.buildOpcode .ISZERO) source 0
  | .zeroBaseExponent => BorrowedInput.invoke external budget allocator p q (Interner.buildOpcode .ISZERO) source 1
  | .parity => invoke external budget allocator p q (Interner.buildOpcode .ISZERO) parity

def afterParity (child : GraphAction σ NodeId) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) : GraphAction σ NodeId := do
  let parity ← child
  zigLiteral .parity external budget allocator p q ⟨0, 0, 0⟩ parity

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary.RuleLiteral
