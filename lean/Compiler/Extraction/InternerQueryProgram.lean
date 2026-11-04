/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerQueryIR

namespace Compiler.Extraction.Interner.Queries

-- ExpressionClasses SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- SemanticInformation SHA-256: f1dd80a58d654620252118aadb5eb1ecec2893cbca76999a05f3ee1e89cd7c34
-- AssemblyItem SHA-256: 294d255a0ddec3bbc2a00f95853e38e76a4a1ee88efda1f6b60784b75cc80c3d
-- Instruction SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
def determinismCode : Determinism := {
  verbatim := 13, rejectOnVerbatim := true,
  instructionTest := .operation, checkShape := true, plain := true,
  opcodes := [241, 242, 244, 250, 240, 245, 90, 88, 89, 49, 71, 59, 63, 62, 61], selected := false, fallback := true }

end Compiler.Extraction.Interner.Queries
