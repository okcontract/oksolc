/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NormalizationOwnership

namespace Compiler.Extraction.Cache

-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- Semantic information SHA-256: f1dd80a58d654620252118aadb5eb1ecec2893cbca76999a05f3ee1e89cd7c34
-- Item kinds SHA-256: 294d255a0ddec3bbc2a00f95853e38e76a4a1ee88efda1f6b60784b75cc80c3d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
def keyCode : KeyCode := { kind := .input, instructionTest := .operation, dataTest := .operation, operationData := (.literal 0), otherData := .input, sequence := .input }
def equalityFields : List Field := [.kind, .instruction, .data, .sequence, .arguments]
def normalizeCode : NormalizeCode := { commutative := [1, 2, 20, 22, 23, 24], guard := .operation, threshold := 2 }
def normalizationOwnershipCode : NormalizationOwnership.Code := { threshold := 2, useScratch := .le, ownTemporary := .gt, clearOnTake := true, freeOnDeinit := true }

end Compiler.Extraction.Cache
