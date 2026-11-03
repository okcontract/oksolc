/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerOrigin

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Release the actual caller's normalized owner in a reached world. Its
original entry proves separation from every pre-existing allocation; the
released frame retains the reached contents, not the entry contents. -/
theorem Origin.release_frame {allocator : Nat} {source : View} {request : Interner.Request}
    {values : List NodeId} {before : World σ} {taken : State σ}
    {owned : ArgumentSlice} {lookup : Handle}
    (origin : Origin allocator source request values before taken owned lookup)
    (external : External σ) (world : World σ)
    (valid : Valid world.memory) (live : SliceValid allocator world.memory.heap owned) :
    ∃ after, free external allocator owned world.memory = (.ok (), after) ∧
      Valid after ∧ ReleasePost world.memory.heap world.memory.memory allocator owned after.heap after.memory ∧
      after.effects = (if owned.items.isEmpty then world.memory.effects else external.free owned world.memory) ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell →
        after.memory.heap.lookup id = world.memory.memory.heap.lookup id) ∧
      (∀ id block, before.memory.heap id = some block → after.heap id = world.memory.heap id) := by
  obtain ⟨after, ran, kept, released, effects⟩ := free_valid external allocator owned world.memory valid live
  exact ⟨after, ran, kept, released, effects,
    fun id cell found => (released.frame id (origin.freshNative id cell found).symm).2,
    fun id block found => (released.frame id (origin.fresh id block found).symm).1⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
