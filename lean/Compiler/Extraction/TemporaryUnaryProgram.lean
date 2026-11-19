/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryUnary

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary
open Compiler.Algebraic Contract.Yul

-- Generated from every unary literal in the production Algebraic.apply body.
-- Source SHA-256: d2c488ec16a8dcd03b89c992a1f4e0a21c998184a84d94aef65d0cd0781ee3fa
-- Boolean rewriting returns from the first invocation before preparing the second array.
def zigUnary (replacement : Replacement) (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Caller.Queries) (left right : NodeId) : GraphAction σ NodeId :=
  match replacement with
  | .not_right => invoke external budget allocator p q (Interner.buildOpcode .NOT) right
  | .iszero_left | .iszero_right => invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
      (if replacement == .iszero_left then left else right)
  | .bool_left | .bool_right => do
    let first ← invoke external budget allocator p q (Interner.buildOpcode .ISZERO)
      (if replacement == .bool_left then left else right)
    invoke external budget allocator p q (Interner.buildOpcode .ISZERO) first
  | _ => fun before => (.error .outsideOwnedContinuation, before)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryUnary
