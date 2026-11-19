/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ShiftMasks

namespace Compiler.Extraction.ShiftMasks
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Contract.Yul

variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def shlOpcode : Opcode := 27
def shrOpcode : Opcode := 28

def shiftedCoverage (amount : Word) : Except ReadError Word :=
  if amount.toNat == 256 then .ok 0 else
  if amount.toNat < 256 then .ok (BitVec.allOnes 256 >>> amount.toNat) else .error .safetyFault

def removeCoveredShiftMask (reads : Reads) (constructors : Compiler.Extraction.Associative.Constructors Debug m)
    (maskId shiftedId : NodeId) (debug : Debug)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some mask ← query (fun reads => reads.constant maskId) | return none
  let some shifted ← query (fun reads => reads.operation shiftedId shrOpcode) | return none
  match shifted.items with
  | [amountId, _] =>
    let some amount ← query (fun reads => reads.constant amountId) | return none
    if amount.toNat > 256 then return none
    let coverage ← readAction (shiftedCoverage amount)
    if mask &&& coverage == coverage then
      return some (← constructors.borrowedOperation shifted.address shrOpcode shifted.items debug)
    return none
  | _ => return none

@[reducible] def powerOfTwoShiftProductWithInputs (reads : Reads) (build : OperationBuilder Debug m)
    (value shiftId : NodeId) (debug : Debug)
    (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some shift ← query (fun reads => reads.operation shiftId shlOpcode) | return none
  match shift.items with
  | [amountId, baseId] =>
    if (← query (fun reads => reads.constant baseId)) != some 1 then return none
    return some (← build shlOpcode [← operand shift 0 amountId, value] debug)
  | _ => return none


/-- Logical projection of the same source body. -/
def powerOfTwoShiftProduct (reads : Reads) (build : OperationBuilder Debug m)
    (value shiftId : NodeId) (debug : Debug) : m (Option NodeId) :=
  powerOfTwoShiftProductWithInputs reads build value shiftId debug

end Compiler.Extraction.ShiftMasks
