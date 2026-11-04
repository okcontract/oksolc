/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.OwnedKeysPhysical

namespace Compiler.Extraction.OwnedKeys.Physical
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments

/-- The logical release has the same footprint as the typed release. -/
theorem Completed.registry_frame (external : Normalization.External σ) (key : Key) (incoming : Entry)
    (before after : State σ) (completed : Completed external key incoming before after) (id : Nat)
    (apart : ∀ old, before.table key = some old → key.arguments ≠ [] → id ≠ old.address) :
    after.memory.heap id = before.memory.heap id := by
  have heap := congrArg OwnedKeys.State.memory completed.logical
  change after.memory.heap = retire before.logical key at heap
  rw [heap]
  exact retire_frame before.logical key id apart

theorem Completed.registry_dead (external : Normalization.External σ) (key : Key) (incoming : Entry)
    (before after : State σ) (completed : Completed external key incoming before after)
    (old : Entry) (found : before.table key = some old) (nonempty : key.arguments ≠ []) :
    after.memory.heap old.address = none := by
  have heap := congrArg OwnedKeys.State.memory completed.logical
  change after.memory.heap = retire before.logical key at heap
  simp only [heap, retire, State.logical, found, nonempty, ↓reduceIte]
  simp [Memory.write]

end Compiler.Extraction.OwnedKeys.Physical
