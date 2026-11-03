/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.SignExtendMask

namespace Compiler.Extraction.SignExtendMask
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def signextendOpcode : Opcode := 11
def andOpcode : Opcode := 22

def nativeLowMask (index : Word) : Folding.Result := do
  let incremented ← Folding.Zig.checkedAdd 256 index.toNat 1
  let product ← Folding.Zig.checkedMul 256 incremented 8
  let count ← Folding.Zig.narrow 8 product
  let high : Word := (1 : Word) <<< count
  let low ← Folding.Zig.checkedSub high.toNat 1
  return BitVec.ofNat 256 low

def lowMaskRead (index : Word) : Except ReadError Word :=
  match nativeLowMask index with
  | .ok mask => .ok mask
  | .error _ => .error .safetyFault

@[reducible] def stripRedundantSignExtendMaskWithInputs (reads : Reads) (constructors : Constructors Debug m)
    (constantId signExtendId : NodeId) (debug : Debug)
    (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let some mask ← query (fun reads => reads.constant constantId) | return none
  let some extended ← query (fun reads => reads.operation signExtendId signextendOpcode) | return none
  match extended.items with
  | [indexId, valueId] =>
    let some index ← query (fun reads => reads.constant indexId) | return none
    if index.toNat ≥ 31 then return none
    let low ← readAction (lowMaskRead index)
    if mask &&& low != mask then return none
    let materialized ← constructors.materialize constantId mask debug
    return some (← constructors.operation andOpcode [materialized, ← operand extended 1 valueId] debug)
  | _ => return none


/-- Logical projection of the same source body. -/
def stripRedundantSignExtendMask (reads : Reads) (constructors : Constructors Debug m)
    (constantId signExtendId : NodeId) (debug : Debug) : m (Option NodeId) :=
  stripRedundantSignExtendMaskWithInputs reads constructors constantId signExtendId debug

end Compiler.Extraction.SignExtendMask
