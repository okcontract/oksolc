/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerProofs
import Compiler.Extraction.ConstructionProofs

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Source-bound constructor arguments. Debug metadata is passed through the
native wrappers; this value projection does not observe source locations. -/
structure ConstructorCode where
  constant : Scalar Word
  instruction : Scalar Opcode
  sequence : BitVec 32

def ConstructorCode.constantRequest (code : ConstructorCode) (value : Word) : Request :=
  ⟨⟨2, none, code.constant.run value⟩, [], code.sequence⟩

def ConstructorCode.operationRequest (code : ConstructorCode) (opcode : Opcode) (ids : List NodeId) : Request :=
  ⟨⟨1, some (code.instruction.run opcode), 0⟩, ids, code.sequence⟩

/-- Independent EVM bindings used in the denotation laws. The extracted opcode
function must agree with this specification; a changed byte cannot become a
new semantic assumption unnoticed. -/
def specifiedOpcode : BuildOp → Opcode
  | .NOT => 0x19
  | .SUB => 0x03
  | .ISZERO => 0x15

structure MeaningLaws (meaning : Meaning) : Prop where
  constant : ∀ value, meaning.atom 2 value 0 [] = some value
  operation : ∀ op values, meaning.operation (specifiedOpcode op) 0 values = op.eval values

/-- The laws have a concrete model for every interpretation of the remaining
instructions and atoms. Pure constructor operations ignore the sequence stamp;
Push has no operands. Unsupported arities stay undefined. -/
def constructorMeaning (other : Meaning) : Meaning where
  operation := fun opcode sequence values =>
    if opcode == specifiedOpcode .NOT then BuildOp.NOT.eval values
    else if opcode == specifiedOpcode .SUB then BuildOp.SUB.eval values
    else if opcode == specifiedOpcode .ISZERO then BuildOp.ISZERO.eval values
    else other.operation opcode sequence values
  atom := fun kind value sequence values =>
    if kind == 2 then if values.isEmpty then some value else none
    else other.atom kind value sequence values

end Compiler.Extraction.Interner
