/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerShiftInput

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- EVM versions SHA-256: 5e84058712718707559b37b4129377fd03a336ef04bd35325060799760c7bcd4

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput
open Contract.Yul

inductive Site where
  | exponentTwo | multiplyLeft | multiplyRight | divide
  deriving DecidableEq, Repr

/-- The selected source segment, after its enclosing queries and guards.
`power` is the already evaluated local binary-logarithm result; the argument
element itself is loaded from native memory at its source evaluation position. -/
def zigLiteral (context : Context σ) (site : Site) (power : Nat)
    (source : Compiler.ZigAir.Memory.WordArray.View) (debug : AssemblyItem.Fields.Values) : GraphAction σ Compiler.Algebraic.NodeId :=
  match site with
  | .exponentTwo => run context false Dispatch.opSHL 1 source 1 debug
  | .multiplyLeft => run context true Dispatch.opSHL (BitVec.ofNat 256 power) source 1 debug
  | .multiplyRight => run context true Dispatch.opSHL (BitVec.ofNat 256 power) source 0 debug
  | .divide => run context true Dispatch.opSHR (BitVec.ofNat 256 power) source 0 debug

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput
