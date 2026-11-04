/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.OwnedKeysEffects
import Compiler.Extraction.OwnedKeysPhysical
import Compiler.Extraction.NormalizationMemoryEffects

namespace Compiler.Extraction.OwnedKeys.Physical
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments

def State.mapEffects (project : σ → τ) (before : State σ) : State τ :=
  ⟨before.table, before.memory.mapEffects project⟩

/-- The actual probe observes the projected reached session and preserves its
returned decision. Native map probing remains a separate implementation claim. -/
def Probe.Transport (physical : Probe σ) (original : Probe τ) (project : σ → τ) : Prop :=
  ∀ key before, original key (before.mapEffects project) =
    ((physical key before).1, project (physical key before).2)

theorem operations_transport {physical : Normalization.External σ} {original : Normalization.External τ}
    {project : σ → τ} (mapped : Normalization.External.Transport physical original project)
    {left : Probe σ} {right : Probe τ} (probes : Probe.Transport left right project) (allocator : Nat) :
    Operations.Transport (operations left physical allocator) (operations right original allocator) (State.mapEffects project) := by
  constructor
  · intro key before
    dsimp only [operations, State.mapEffects]
    rw [probes key before.memory]
    rfl
  · intro key before; rfl
  · intro slice before
    dsimp only [operations, State.mapEffects]
    rw [mapped.free]
    rfl
  · intro key entry before; rfl
  · rfl

theorem run_transport {physical : Normalization.External σ} {original : Normalization.External τ}
    {project : σ → τ} (mapped : Normalization.External.Transport physical original project)
    {left : Probe σ} {right : Probe τ} (probes : Probe.Transport left right project)
    (allocator : Nat) (key : Key) (incoming : Entry) (before : State σ) :
    run right original allocator key incoming (before.mapEffects project) =
      ((run left physical allocator key incoming before).1, (run left physical allocator key incoming before).2.mapEffects project) :=
  (operations_transport mapped probes allocator).execute publicationCode key incoming before

end Compiler.Extraction.OwnedKeys.Physical
