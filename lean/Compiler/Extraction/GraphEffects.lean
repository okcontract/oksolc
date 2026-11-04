/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.Graph

namespace Compiler.Algebraic.Effect

/-- Exact effect erasure, including errors and their reached states. Unlike an
ordinary-outcome simulation this does not omit semantic rejection or exhaustion. -/
def Transport (project : σ → τ) (physical : Effect σ ε α) (original : Effect τ ε α) : Prop :=
  ∀ before, original (project before) = ((physical before).1, project (physical before).2)

namespace Transport

theorem pure (project : σ → τ) (value : α) :
    Transport project (Effect.pure value : Effect σ ε α) (Effect.pure value) := fun _ => rfl

theorem bind (project : σ → τ) {physical : Effect σ ε α} {original : Effect τ ε α}
    {nextPhysical : α → Effect σ ε β} {nextOriginal : α → Effect τ ε β}
    (first : Transport project physical original)
    (next : ∀ value, Transport project (nextPhysical value) (nextOriginal value)) :
    Transport project (physical >>= nextPhysical) (original >>= nextOriginal) := by
  intro before
  change Effect.bind original nextOriginal (project before) =
    ((Effect.bind physical nextPhysical before).1, project (Effect.bind physical nextPhysical before).2)
  unfold Effect.bind
  rw [first]
  cases physical before with
  | mk result reached =>
    cases result with
    | error fault => rfl
    | ok value => exact next value reached

end Transport
end Compiler.Algebraic.Effect
