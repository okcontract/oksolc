/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RuleTernaryProgram

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

/-- Supply the original dispatcher's constructor interface for these literal
segments. Other arities/constructors fail explicitly outside this scope. -/
def constructors (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Caller.Queries) :
    Compiler.Extraction.Associative.Constructors Unit (GraphAction σ) where
  operation := fun opcode values _ => match values with
    | [first, second, third] => invoke external budget allocator p q opcode first second third
    | _ => fun before => (.error .outsideOwnedContinuation, before)
  constant := fun _ _ before => (.error .outsideOwnedContinuation, before)
  materialize := fun _ _ _ before => (.error .outsideOwnedContinuation, before)

theorem opcode_binding : opcode .multiplication = Folding.Op.mulmod.opcode ∧
    opcode .addition = Folding.Op.addmod.opcode := ⟨rfl, rfl⟩

/-- Actual readonly loads supply the values to the same constructor callback
used by the complete extracted dispatcher. Its retained prefix is separate. -/
theorem initializer_projection (site : Site) (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Caller.Queries) (source : View) (first second right : NodeId) (before : World σ)
    (length : source.length = 2)
    (firstLoad : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 0) = .ok (number first))
    (secondLoad : Compiler.ZigAir.Memory.load before.memory.memory (source.pointer 1) = .ok (number second)) :
    zigLiteral site external budget allocator p q source right before =
      (constructors external budget allocator p q).operation (opcode site) [first, second, right] () before :=
  borrowed_of_loads _ _ _ _ _ _ _ _ _ _ _ length firstLoad secondLoad

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryTernary.RuleLiteral
