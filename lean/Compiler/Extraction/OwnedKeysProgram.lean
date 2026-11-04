/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.OwnedKeys

namespace Compiler.Extraction.OwnedKeys

-- Exact publishOwned profile admitted by storage and interner extraction.
-- Source SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def publicationCode : Code := { releaseExisting := true, replaceKey := true, value := .input }

end Compiler.Extraction.OwnedKeys
