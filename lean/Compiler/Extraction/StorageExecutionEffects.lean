/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecution
import Compiler.Extraction.GraphEffects

namespace Compiler.Extraction.Storage
open Compiler.Algebraic

/-- Local equations at the reached ownership state, including rejected calls
and their effects. Ordinary allocation failure and semantic faults stay distinct. -/
structure Operations.Transport (physical : Operations σ ε) (original : Operations τ ε) (project : σ → τ) : Prop where
  attempt : ∀ site owner, Effect.Transport project (physical.attempt site owner) (original.attempt site owner)
  release : ∀ action owner, Effect.Transport project (physical.release action owner) (original.release action owner)

namespace Operations.Transport
variable {physical : Operations σ ε} {original : Operations τ ε} {project : σ → τ}
  (mapped : Operations.Transport physical original project)
include mapped

theorem release_execute (action : Release) (owner : State) (before : σ) :
    action.execute original owner (project before) =
      ((action.execute physical owner before).1, project (action.execute physical owner before).2) := by
  unfold Release.execute
  rw [mapped.release]
  cases physical.release action owner before with
  | mk result reached => cases result with
    | error fault => rfl
    | ok value => cases value; rfl

theorem release_all (actions : List Release) (owner : State) (before : σ) :
    releaseAll original actions owner (project before) =
      ((releaseAll physical actions owner before).1, project (releaseAll physical actions owner before).2) := by
  induction actions generalizing owner before with
  | nil => rfl
  | cons action rest next =>
    simp only [releaseAll, release_execute mapped]
    cases action.execute physical owner before with
    | mk result reached =>
      cases result with
      | mk outcome after => cases outcome with
        | error fault => rfl
        | ok value => cases value; exact next after reached

theorem cleanup_execute (cleanup : Cleanup) (owner : State) (before : σ) :
    cleanup.execute original owner (project before) =
      ((cleanup.execute physical owner before).1, project (cleanup.execute physical owner before).2) := by
  cases cleanup with
  | guarded flag action =>
    simp only [Cleanup.execute]
    split
    · exact release_execute mapped action owner before
    · rfl
  | sequence actions => exact release_all mapped actions owner before

/-- Transport the existing source-bound program. Branch continuations observe
the reached effects; ordinary exits run applicable defers, while semantic faults
retain the exact stopped ownership/effects and do not invent unwinding. -/
theorem execute (input : Input) (program : Program) (owner : State) (before : σ) :
    program.execute input original owner (project before) =
      ((program.execute input physical owner before).1, project (program.execute input physical owner before).2) := by
  induction program generalizing owner before with
  | done | ret | capacityError => rfl
  | command action next continued =>
    simp only [Program.execute]
    cases allocated : action.allocation with
    | none => simpa only [allocated] using continued (action.success input owner) before
    | some site =>
      dsimp only
      rw [mapped.attempt site owner before]
      cases physical.attempt site owner before with
      | mk result reached => cases result with
        | error fault => rfl
        | ok succeeded => cases succeeded with
          | false => rfl
          | true => exact continued (action.success input owner) reached
  | branch test yes no next yesMapped noMapped nextMapped =>
    simp only [Program.execute]
    cases selected : test.eval input with
    | true =>
      simp only [↓reduceIte]
      rw [yesMapped]
      cases yes.execute input physical owner before with
      | mk result reached => cases result with
        | mk outcome after => cases outcome with
          | error fault => rfl
          | ok returned => cases returned with
            | none => exact nextMapped after reached
            | some value => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [noMapped]
      cases no.execute input physical owner before with
      | mk result reached => cases result with
        | mk outcome after => cases outcome with
          | error fault => rfl
          | ok returned => cases returned with
            | none => exact nextMapped after reached
            | some value => rfl
  | scope errorOnly cleanup body bodyMapped =>
    simp only [Program.execute, bodyMapped]
    cases body.execute input physical owner before with
    | mk result reached => cases result with
      | mk outcome after => cases outcome with
        | error fault => rfl
        | ok returned =>
          dsimp only
          split
          · rfl
          · rw [cleanup_execute mapped]

end Operations.Transport
end Compiler.Extraction.Storage
