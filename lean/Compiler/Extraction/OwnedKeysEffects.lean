/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.OwnedKeys

namespace Compiler.Extraction.OwnedKeys
open Compiler.Extraction.Cache Compiler.Extraction.Storage

/-- Local equations for the existing publication interpreter. Both failures and
successful writes keep the reached state; no enclosing publication result is
assumed. The lookup and written ownership entry are unchanged by projection. -/
structure Operations.Transport (physical : Operations σ ε) (original : Operations τ ε) (project : σ → τ) : Prop where
  probe : ∀ key before, original.getOrPut key (project before) =
    ((physical.getOrPut key before).1, project (physical.getOrPut key before).2)
  lookup : ∀ key before, original.lookup key (project before) = physical.lookup key before
  release : ∀ slice before, original.release slice (project before) =
    ((physical.release slice before).1, project (physical.release slice before).2)
  write : ∀ key entry before, original.write key entry (project before) = project (physical.write key entry before)
  outOfMemory : original.outOfMemory = physical.outOfMemory

namespace Operations.Transport
variable {physical : Operations σ ε} {original : Operations τ ε} {project : σ → τ}
  (mapped : Operations.Transport physical original project)
include mapped

theorem complete (code : Code) (key : Key) (incoming : Entry) (before : σ) :
    code.complete original key incoming (project before) =
      ((code.complete physical key incoming before).1, project (code.complete physical key incoming before).2) := by
  unfold Code.complete
  rw [mapped.lookup]
  cases physical.lookup key before with
  | none => dsimp only; rw [mapped.write]
  | some old =>
    cases code.releaseExisting with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; rw [mapped.write]
    | true =>
      simp only [↓reduceIte]
      rw [mapped.release]
      cases physical.release (slice key old) before with
      | mk result reached =>
        cases result with
        | error fault => rfl
        | ok value => cases value; dsimp only; rw [mapped.write]

theorem execute (code : Code) (key : Key) (incoming : Entry) (before : σ) :
    code.execute original key incoming (project before) =
      ((code.execute physical key incoming before).1, project (code.execute physical key incoming before).2) := by
  unfold Code.execute
  rw [mapped.probe]
  cases physical.getOrPut key before with
  | mk ok reached =>
    cases ok with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, mapped.outOfMemory]
    | true => exact mapped.complete code key incoming reached

end Operations.Transport
end Compiler.Extraction.OwnedKeys
