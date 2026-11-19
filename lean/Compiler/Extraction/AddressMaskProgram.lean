/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AddressMask

namespace Compiler.Extraction.AddressMask
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Nested Contract.Yul

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def addressOpcodes : List Opcode := [48, 51, 50, 65]

-- A closed compile-time expression; its non-wrapping subtraction is proved safe.
def nativeMask : Word := ((1 : Word) <<< 160) - 1

def search (reads : Reads) (operationId : NodeId) : List Opcode → Except ReadError (Option Opcode)
  | [] => .ok none
  | instruction :: rest => do
    if let some arguments ← reads.operation operationId instruction then
      if arguments.items.isEmpty then return some instruction
    search reads operationId rest

def addressInstruction (reads : Reads) (operationId maskId : NodeId) : Except ReadError (Option Opcode) := do
  if (← reads.constant maskId) != some nativeMask then return none
  search reads operationId addressOpcodes

end Compiler.Extraction.AddressMask
