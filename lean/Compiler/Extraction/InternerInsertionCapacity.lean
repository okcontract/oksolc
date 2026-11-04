/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionCount
import Compiler.Extraction.StoragePreparationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The second capacity check uses the reached count and releases precisely its
incoming normalized owner. No caller origin or pre-recursion header is used. -/
theorem capacity_execution (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (rows : List Storage.Cell) (world : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (released : Session (Publication.Effects σ))
    (saturated : 2 ^ 32 - 1 ≤ rows.length)
    (freed : free (Publication.external ops.arguments) allocator normalized world.memory = (.ok (), released)) :
    execution ops allocate safety allocator container source address meaning input key normalized deterministic rows world growth =
      ((.ok (some .capacityFailure), Storage.Release.normalized.run Storage.normalizedOwnership),
        ⟨⟨⟨⟨released, false⟩, none⟩, none⟩, none⟩) := by
  let value := (key.eval meaning world.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun state frame => Interner.InsertionExecution.project rows world.graph.table
    (cell input key normalized value state frame) key state
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  let calls := callbacks ops allocate safety allocator container source address input key normalized rows value graph growth
  have normalizedCall : ∀ state, calls.release .normalized state start = (.ok (), withMemory start released) := by
    intro state
    simp only [calls, callbacks, Insertion.callbacks, start, memory, freed, Except.mapError]
  have noRoom : decide (rows.length < 2 ^ 32 - 1) = false := by
    simp only [decide_eq_false_iff_not]
    exact Nat.not_lt_of_ge saturated
  simpa only [execution, noRoom] using Storage.insert_capacity_failure calls deterministic start (withMemory start released) normalizedCall

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
