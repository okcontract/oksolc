/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryEffects
import Compiler.Extraction.NormalizationMemoryContracts

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Project private effects only. Both existing heaps and every typed memory
observation remain the same, including partial writes on rejected executions. -/
def Session.mapEffects (project : σ → τ) (before : Session σ) : Session τ :=
  ⟨before.heap, before.memory, project before.effects⟩

@[simp] theorem Session.mapEffects_heap (project : σ → τ) (before : Session σ) :
    (before.mapEffects project).heap = before.heap := rfl

@[simp] theorem Session.mapEffects_memory (project : σ → τ) (before : Session σ) :
    (before.mapEffects project).memory = before.memory := rfl

@[simp] theorem Session.mapEffects_effects (project : σ → τ) (before : Session σ) :
    (before.mapEffects project).effects = project before.effects := rfl

def Step.mapEffects (project : σ → τ) (execution : Step σ α) : Step τ α :=
  (execution.1, execution.2.mapEffects project)

/-- Local equations on the actual host calls. They assume no normalization,
ownership, graph or enclosing-caller preservation result. -/
structure External.Transport (physical : External σ) (original : External τ) (project : σ → τ) : Prop where
  allocate : ∀ site before bytes effects,
    original.allocate site (before.mapEffects project) bytes (project effects) =
      ((physical.allocate site before bytes effects).1, project (physical.allocate site before bytes effects).2)
  release : ∀ slice before, original.free slice (before.mapEffects project) = project (physical.free slice before)

theorem Valid.mapEffects (project : σ → τ) {before : Session σ} (valid : Valid before) :
    Valid (before.mapEffects project) := ⟨valid.memory, valid.related, valid.injected⟩

theorem External.Transport.admitted {physical : External σ} {original : External τ} {project : σ → τ}
    (mapped : External.Transport physical original project) (admitted : Admitted original) : Admitted physical := by
  intro site before values base reached valid nonempty response
  apply admitted site (before.mapEffects project) values base (project reached) valid nonempty
  change original.allocate site (before.mapEffects project) (values.length * 4) (project before.effects) = _
  rw [mapped.allocate, response]

namespace External.Transport
variable {physical : External σ} {original : External τ} {project : σ → τ}
  (mapped : External.Transport physical original project)
include mapped

theorem reserve (allocator : Nat) (values : List NodeId) (before : Session σ) :
    Normalization.reserve original allocator values (before.mapEffects project) =
      Step.mapEffects project (Normalization.reserve physical allocator values before) := by
  unfold Normalization.reserve
  simp only [Session.mapEffects_heap, Session.mapEffects_memory, Session.mapEffects_effects]
  rw [Allocation.reserve_transport before.heap before.memory allocator values
    (physical.allocate .temporary before) (original.allocate .temporary (before.mapEffects project))
    project (mapped.allocate .temporary before) before.effects]
  cases Allocation.reserve before.heap before.memory allocator values (physical.allocate .temporary before) before.effects with
  | mk allocation reached =>
    rcases allocation with ⟨result, heap, memory⟩
    cases result with
    | error fault => rfl
    | ok result => cases result <;> rfl

omit mapped in
theorem prepare (code : NormalizationOwnership.Code) (budget allocator bufferLength : Nat)
    (source target : View) (values : List NodeId) (allocated : Bool) (before : Session σ) :
    Normalization.prepare code budget allocator bufferLength source target values allocated (before.mapEffects project) =
      Step.mapEffects project (Normalization.prepare code budget allocator bufferLength source target values allocated before) := by
  unfold Normalization.prepare
  simp only [Session.mapEffects_heap, Session.mapEffects_memory, Session.mapEffects_effects]
  cases Compiler.Extraction.InsertionSort.Copied.run budget before.memory source target with
  | mk result memory =>
    cases result with
    | error fault => rfl
    | ok returned =>
      cases returned
      cases allocated <;> rfl

theorem init (code : NormalizationOwnership.Code) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (before : Session σ) :
    Normalization.init code original budget allocator commutative source buffer values (before.mapEffects project) =
      Step.mapEffects project (Normalization.init code physical budget allocator commutative source buffer values before) := by
  unfold Normalization.init
  by_cases borrowed : (!commutative || decide (source.length < code.threshold)) = true
  · simp only [if_pos borrowed]; rfl
  · simp only [if_neg borrowed]
    by_cases fits : code.useScratch.test source.length buffer.length = true
    · simp only [if_pos fits]
      exact prepare code budget allocator buffer.length source (bufferPrefix buffer source.length) values false before
    · simp only [if_neg fits, mapped.reserve]
      dsimp only [Step.mapEffects]
      cases Normalization.reserve physical allocator values before with
      | mk result reached =>
        cases result with
        | error fault => rfl
        | ok slice =>
          exact prepare code budget allocator buffer.length source (view slice) values true reached

theorem takeOwned (code : NormalizationOwnership.Code) (allocator : Nat) (handle : Handle) (before : Session σ) :
    Normalization.takeOwned code original allocator handle (before.mapEffects project) =
      Step.mapEffects project (Normalization.takeOwned code physical allocator handle before) := by
  unfold Normalization.takeOwned
  simp only [Session.mapEffects_heap, Session.mapEffects_memory, Session.mapEffects_effects]
  cases owned : handle.owned with
  | some slice => rfl
  | none =>
    rw [Duplication.run_transport before.heap before.memory allocator handle.items handle.values
      (physical.allocate .duplicate before) (original.allocate .duplicate (before.mapEffects project))
      project (mapped.allocate .duplicate before) before.effects]
    cases Duplication.run before.heap before.memory allocator handle.items handle.values
        (physical.allocate .duplicate before) before.effects with
    | mk allocation reached =>
      rcases allocation with ⟨result, heap, memory⟩
      cases result with
      | error fault => rfl
      | ok result => cases result <;> rfl

theorem free (allocator : Nat) (slice : ArgumentSlice) (before : Session σ) :
    Normalization.free original allocator slice (before.mapEffects project) =
      Step.mapEffects project (Normalization.free physical allocator slice before) := by
  unfold Normalization.free
  simp only [Session.mapEffects_heap, Session.mapEffects_memory, Session.mapEffects_effects]
  cases Arguments.release before.heap before.memory allocator slice with
  | error fault => rfl
  | ok released =>
    rcases released with ⟨heap, memory⟩
    cases empty : slice.items.isEmpty with
    | true => rfl
    | false => rw [mapped.release slice before]; rfl

theorem deinitialize (code : NormalizationOwnership.Code) (allocator : Nat) (handle : Handle) (before : Session σ) :
    Normalization.deinitialize code original allocator handle (before.mapEffects project) =
      Step.mapEffects project (Normalization.deinitialize code physical allocator handle before) := by
  unfold Normalization.deinitialize
  cases handle.owned with
  | none => rfl
  | some slice =>
    cases code.freeOnDeinit with
    | false => rfl
    | true => exact mapped.free allocator slice before

theorem close (code : NormalizationOwnership.Code) (allocator : Nat) (handle : Handle)
    (result : Except Failure Outcome) (before : Session σ) :
    Normalization.close code original allocator handle result (before.mapEffects project) =
      Step.mapEffects project (Normalization.close code physical allocator handle result before) := by
  unfold Normalization.close
  rw [mapped.deinitialize]
  dsimp only [Step.mapEffects]
  cases Normalization.deinitialize code physical allocator handle before with
  | mk closed after => cases closed <;> rfl

theorem continueWith (code : NormalizationOwnership.Code) (allocator : Nat)
    (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ) :
    Normalization.continueWith code original allocator exit handle (before.mapEffects project) =
      Step.mapEffects project (Normalization.continueWith code physical allocator exit handle before) := by
  cases exit with
  | lookup => exact mapped.close code allocator handle (.ok .lookup) before
  | transfer | cleanup =>
    all_goals
      unfold Normalization.continueWith
      rw [mapped.takeOwned]
      dsimp only [Step.mapEffects]
      cases Normalization.takeOwned code physical allocator handle before with
      | mk taken reached =>
        cases taken with
        | error failure =>
          cases failure with
          | outOfMemory => exact mapped.close code allocator handle (.error .outOfMemory) reached
          | allocation | preparation | release => rfl
        | ok owned =>
          rcases owned with ⟨slice, remaining⟩
          dsimp only
          first
          | exact mapped.close code allocator remaining (.ok (.transferred slice)) reached
          | rw [mapped.free]
            dsimp only [Step.mapEffects]
            cases Normalization.free physical allocator slice reached with
            | mk released after =>
              cases released with
              | error fault => rfl
              | ok returned => cases returned; exact mapped.close code allocator remaining (.ok .cleaned) after

/-- Instrumentation erases through the same complete native lifecycle. Every
budget, callback response and rejection retains its exact reached state. -/
theorem run (code : NormalizationOwnership.Code) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (exit : NormalizationOwnership.Exit) (before : Session σ) :
    Normalization.run code original budget allocator commutative source buffer values exit (before.mapEffects project) =
      Step.mapEffects project (Normalization.run code physical budget allocator commutative source buffer values exit before) := by
  unfold Normalization.run
  rw [mapped.init]
  dsimp only [Step.mapEffects]
  cases Normalization.init code physical budget allocator commutative source buffer values before with
  | mk initialized reached =>
    cases initialized with
    | error failure => rfl
    | ok handle => exact mapped.continueWith code allocator exit handle reached

end External.Transport
end Compiler.Extraction.Memory.Arguments.Normalization
