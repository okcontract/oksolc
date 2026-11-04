/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredCapacity
import Compiler.Extraction.NormalizationMemoryEffects
import Compiler.Extraction.GraphEffects

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory Compiler.Algebraic
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Local equations retain the actual allocator brand, native request, response
and reached effects, including refusal and rejected native regions. -/
def Backing.Registry.Allocate.Transport (project : σ → τ)
    (left : Backing.Registry.Allocate σ) (right : Backing.Registry.Allocate τ) : Prop :=
  ∀ allocator bytes alignment effects, right allocator bytes alignment (project effects) =
    ((left allocator bytes alignment effects).1, project (left allocator bytes alignment effects).2)

def Backing.Release.External.Transport (project : σ → τ)
    (left : Backing.Release.External σ) (right : Backing.Release.External τ) : Prop :=
  ∀ allocator base bytes alignment effects,
    right allocator base bytes alignment (project effects) = project (left allocator base bytes alignment effects)

namespace Backing
variable {project : σ → τ} {left : Registry.Allocate σ} {right : Registry.Allocate τ}
  (allocated : Registry.Allocate.Transport project left right)
include allocated

theorem reserve_transport (allocator capacity : Nat) (memory : State) (effects : σ) :
    reserve memory capacity (right allocator) (project effects) =
      ((reserve memory capacity (left allocator) effects).1, project (reserve memory capacity (left allocator) effects).2) := by
  unfold reserve
  split
  · rfl
  · exact RegionAllocation.reserve_transport memory (type capacity) (left allocator) (right allocator)
      project (allocated allocator) effects

theorem Registry.run_transport (allocator capacity : Nat) :
    Effect.Transport (Session.mapEffects project) (Registry.run left allocator capacity) (Registry.run right allocator capacity) := by
  intro before
  unfold Registry.run
  dsimp only [Session.mapEffects]
  rw [reserve_transport allocated]
  cases reserve before.memory capacity (left allocator) before.effects with
  | mk result effects =>
    rcases result with ⟨outcome, memory⟩
    cases outcome with
    | error reason => rfl
    | ok value => cases value with
      | none => rfl
      | some data =>
        dsimp only
        split
        · rfl
        · split <;> rfl

omit allocated in
theorem Release.check_transport (project : σ → τ) (allocator capacity : Nat) (data : Address) (before : Session σ) :
    Release.check allocator data capacity (before.mapEffects project) = Release.check allocator data capacity before := rfl

omit allocated in
theorem Release.run_transport {leftFree : Release.External σ} {rightFree : Release.External τ}
    (freed : Release.External.Transport project leftFree rightFree) (allocator capacity : Nat) (data : Address) :
    Effect.Transport (Session.mapEffects project) (Release.run leftFree allocator data capacity) (Release.run rightFree allocator data capacity) := by
  intro before
  unfold Release.run
  rw [Release.check_transport]
  split
  · rfl
  · split
    · rfl
    · dsimp only [Session.mapEffects]
      rw [freed]

omit allocated in
theorem RegisteredCopy.run_transport (project : σ → τ) (source target length : Nat) :
    Effect.Transport (Session.mapEffects project) (RegisteredCopy.run source target length) (RegisteredCopy.run source target length) := by
  intro before
  unfold RegisteredCopy.run
  rfl

omit allocated in
theorem publication_transport (project : σ → τ) (header data : Address) (capacity : Nat) :
    Effect.Transport (Session.mapEffects project) (Publication.Registered.run header data capacity) (Publication.Registered.run header data capacity) := by
  intro before
  unfold Publication.Registered.run
  rfl

variable {leftFree : Release.External σ} {rightFree : Release.External τ}
  (freed : Release.External.Transport project leftFree rightFree)
include freed

omit allocated in
theorem Relocation.finish_transport (allocator oldCapacity capacity : Nat) (header oldData data : Address) :
    Effect.Transport (Session.mapEffects project)
      (Relocation.finish leftFree allocator header oldData data oldCapacity capacity)
      (Relocation.finish rightFree allocator header oldData data oldCapacity capacity) := by
  intro before
  unfold Relocation.finish
  rw [Release.run_transport freed]
  cases Release.run leftFree allocator oldData oldCapacity before with
  | mk outcome reached => cases outcome with
    | error reason => rfl
    | ok value =>
      cases value
      dsimp only
      rw [publication_transport]

omit allocated in
theorem Relocation.run_transport (allocator oldCapacity capacity : Nat) (header oldData data : Address) :
    Effect.Transport (Session.mapEffects project)
      (Relocation.run leftFree allocator header oldData data oldCapacity capacity)
      (Relocation.run rightFree allocator header oldData data oldCapacity capacity) := by
  intro before
  unfold Relocation.run
  simp only [Session.mapEffects_memory]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [RegisteredCopy.run_transport]
        cases RegisteredCopy.run _ _ _ before with
        | mk outcome reached => cases outcome with
          | error reason => rfl
          | ok value => cases value; exact Relocation.finish_transport freed allocator oldCapacity capacity header oldData data reached
  · rfl

theorem Fallback.run_transport (allocator oldCapacity capacity : Nat) (header oldData : Address) :
    Effect.Transport (Session.mapEffects project)
      (Fallback.run left leftFree allocator header oldData oldCapacity capacity)
      (Fallback.run right rightFree allocator header oldData oldCapacity capacity) := by
  intro before
  unfold Fallback.run
  rw [Registry.run_transport allocated]
  cases Registry.run left allocator capacity before with
  | mk outcome reached => cases outcome with
    | error reason => cases reason <;> rfl
    | ok value => cases value with
      | none => rfl
      | some data =>
        dsimp only
        rw [Relocation.run_transport freed]

end Backing

theorem Remap.run_transport {project : σ → τ} {leftFree : Backing.Release.External σ} {rightFree : Backing.Release.External τ}
    (freed : Backing.Release.External.Transport project leftFree rightFree)
    (callback : Remap.Callback) (allocator oldCapacity capacity : Nat) (data : Address) :
    Effect.Transport (Session.mapEffects project)
      (Remap.run callback leftFree allocator data oldCapacity capacity)
      (Remap.run callback rightFree allocator data oldCapacity capacity) := by
  intro before
  unfold Remap.run
  rw [Backing.Release.check_transport]
  split
  · rfl
  · split
    · rw [Backing.Release.run_transport freed]
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · cases callback <;> rfl

theorem Growth.Registered.run_transport {project : σ → τ}
    {left : Backing.Registry.Allocate σ} {right : Backing.Registry.Allocate τ}
    {leftFree : Backing.Release.External σ} {rightFree : Backing.Release.External τ}
    (allocated : Backing.Registry.Allocate.Transport project left right)
    (freed : Backing.Release.External.Transport project leftFree rightFree)
    (callback : Remap.Callback) (allocator capacity : Nat) (header : Address) :
    Effect.Transport (Session.mapEffects project)
      (Growth.Registered.run callback left leftFree allocator header capacity)
      (Growth.Registered.run callback right rightFree allocator header capacity) := by
  intro before
  unfold Growth.Registered.run
  simp only [Session.mapEffects_memory]
  split
  · rfl
  · rfl
  · rw [Remap.run_transport freed]
    cases Remap.run callback leftFree allocator _ _ capacity before with
    | mk outcome reached => cases outcome with
      | error reason => rfl
      | ok value => cases value with
        | none => exact Backing.Fallback.run_transport allocated freed allocator _ capacity header _ reached
        | some data => dsimp only; rw [Backing.publication_transport]

/-- Captured callback identity is shared; only its actual free effects change
representation. This does not admit a new remap implementation. -/
structure Growth.Registered.Callbacks.Transport (project : σ → τ)
    (left : Growth.Registered.Callbacks σ) (right : Growth.Registered.Callbacks τ) : Prop where
  remap : left.remap = right.remap
  release : Backing.Release.External.Transport project left.release right.release

/-- Absence selects the existing first/spare facade on both sides. -/
def Growth.Registered.Callbacks.OptionalTransport (project : σ → τ)
    (left : Option (Growth.Registered.Callbacks σ)) (right : Option (Growth.Registered.Callbacks τ)) : Prop :=
  match left, right with
  | none, none => True
  | some left, some right => Growth.Registered.Callbacks.Transport project left right
  | _, _ => False

theorem Capacity.Registered.ensure_transport {project : σ → τ}
    {left : Backing.Registry.Allocate σ} {right : Backing.Registry.Allocate τ}
    {leftCalls : Growth.Registered.Callbacks σ} {rightCalls : Growth.Registered.Callbacks τ}
    (allocated : Backing.Registry.Allocate.Transport project left right)
    (calls : Growth.Registered.Callbacks.Transport project leftCalls rightCalls) (allocator minimum : Nat) (header : Address) :
    Effect.Transport (Session.mapEffects project)
      (Capacity.Registered.ensure leftCalls left allocator header minimum)
      (Capacity.Registered.ensure rightCalls right allocator header minimum) := by
  intro before
  unfold Capacity.Registered.ensure
  simp only [Session.mapEffects_memory]
  split
  · rfl
  · rfl
  · rw [← calls.remap]
    exact Growth.Registered.run_transport allocated calls.release leftCalls.remap allocator _ header before

end Compiler.Extraction.RepresentativeArray
