/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationPreparedTransport

namespace Compiler.Extraction.Cache.NormalizationOwnership

/-- Close the current scope after intervening graph work. Transfer has already
occurred; this boundary only performs caller release and lookup deinit. -/
def Code.closeWith (code : Code) (release : State → σ → σ) (phase : Exit) (lookup : State)
    (before : σ) : State × σ :=
  let (lookup, before) := if phase = .cleanup then
    (lookup.move .caller .released, release lookup before) else (lookup, before)
  code.deinitWith release lookup before

theorem close_transport (code : Code) (release : State → σ → σ) (other : State → τ → τ)
    (project : σ → τ) (mapped : ∀ lookup before, other lookup (project before) = project (release lookup before))
    (phase : Exit) (lookup : State) (before : σ) :
    code.closeWith other phase lookup (project before) =
      ((code.closeWith release phase lookup before).1, project (code.closeWith release phase lookup before).2) := by
  cases phase <;> simp only [Code.closeWith, reduceCtorEq, ↓reduceIte, mapped,
    deinit_transport code release other project mapped]

end Compiler.Extraction.Cache.NormalizationOwnership
