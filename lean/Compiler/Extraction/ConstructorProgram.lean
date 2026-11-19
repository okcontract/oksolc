/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Constructor

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache

-- Constructors SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- AssemblyItem SHA-256: 294d255a0ddec3bbc2a00f95853e38e76a4a1ee88efda1f6b60784b75cc80c3d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
def constructorCode : ConstructorCode := { constant := .input, instruction := .input, sequence := 0 }

def buildOpcode : BuildOp → Opcode
  | .NOT => 25
  | .SUB => 3
  | .ISZERO => 21

end Compiler.Extraction.Interner
