/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.OppositeShifts

namespace Compiler.Extraction.OppositeShifts
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def shlOpcode : Opcode := 27
def shrOpcode : Opcode := 28
def andOpcode : Opcode := 22

def oppositeOpcode (opcode : Opcode) : Opcode := if opcode == shrOpcode then shlOpcode else shrOpcode

def nativeMask (opcode : Opcode) (outer inner : Word) : Except ReadError Word :=
  if inner.toNat < 256 then
    if outer.toNat < 256 then
      if opcode == shrOpcode then .ok ((BitVec.allOnes 256 <<< inner.toNat) >>> outer.toNat)
      else .ok ((BitVec.allOnes 256 >>> inner.toNat) <<< outer.toNat)
    else .error .safetyFault
  else .error .safetyFault

def checkedDifference (left right : Word) : Except ReadError Word :=
  if right.toNat ≤ left.toNat then .ok (left - right) else .error .safetyFault

def buildNet (constructors : Constructors Debug m) (opcode : Opcode)
    (outer inner : Word) (value : NodeId) (debug : Debug) : m NodeId := do
  if inner.toNat > outer.toNat then
    let difference ← readAction (checkedDifference inner outer)
    let amount ← constructors.constant difference debug
    ConstructorPair.scalars constructors (oppositeOpcode opcode) amount value debug
  else if outer.toNat > inner.toNat then
    let difference ← readAction (checkedDifference outer inner)
    let amount ← constructors.constant difference debug
    ConstructorPair.scalars constructors opcode amount value debug
  else return value

def combineOppositeShifts (constructors : Constructors Debug m) (opcode : Opcode)
    (outer inner : Word) (value : NodeId) (debug : Debug) : m NodeId := do
  let mask ← readAction (nativeMask opcode outer inner)
  let shifted ← buildNet constructors opcode outer inner value debug
  let maskId ← constructors.constant mask debug
  ConstructorPair.scalars constructors andOpcode shifted maskId debug

end Compiler.Extraction.OppositeShifts
