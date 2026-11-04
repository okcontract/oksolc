/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryTernary
import Compiler.Extraction.DispatchProgram

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

-- Generated literal segments of the complete admitted simplifyWithOptions owner.
-- The retained constant/query/option prefix remains a compiler obligation.
-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- EVM versions SHA-256: 5e84058712718707559b37b4129377fd03a336ef04bd35325060799760c7bcd4
inductive Site where
  | multiplication | addition
  deriving DecidableEq, Repr

def opcode : Site → Opcode
  | .multiplication => Compiler.Extraction.Dispatch.opMULMOD
  | .addition => Compiler.Extraction.Dispatch.opADDMOD

def zigLiteral (site : Site) (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (right : NodeId) : GraphAction σ NodeId :=
  borrowed external budget allocator p q (opcode site) source right

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral
