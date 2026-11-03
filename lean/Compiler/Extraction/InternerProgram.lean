/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerControl

namespace Compiler.Extraction.Interner

-- Shared value/scoped control profile, including both ownership handoff sites.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def findCode : FindCode := { hit := .captured, simplified := .captured, published := .captured }

def forceCode : ForceCode := { published := .captured }

end Compiler.Extraction.Interner
