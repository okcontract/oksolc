/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionTransferredPreparation
import Compiler.Extraction.InternerInsertionUnappendedCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Common conclusions of entry/preparation failure, relative to the actual pre-caller
world and reached allocation history. This proposition packages derived native
facts; it supplies neither an alternate executor nor a recursive frame premise. -/
structure CallerPreparationFailure (allocator : Nat) (normalized : ArgumentSlice)
    (before : World (Publication.Effects σ)) (history : Session (Publication.Effects σ)) (after : Frame σ) : Prop where
  valid : Valid (memory after)
  consumed : Consumed normalized (memory after)
  nextId : (memory after).memory.nextId = history.memory.nextId
  nextAddress : (memory after).memory.nextAddress = history.memory.nextAddress
  keys : (memory after).effects.keys = before.memory.effects.keys
  live : OwnedKeys.Live allocator ⟨(memory after).effects.keys, (memory after).heap⟩
  unique : OwnedKeys.Unique (memory after).effects.keys
  native : ∀ id cell, before.memory.memory.heap.lookup id = some cell → (memory after).memory.heap.lookup id = some cell
  registry : ∀ id block, before.memory.heap id = some block → (memory after).heap id = some block
  object : after.item.object = none
  value : after.item.clone.value = none
  marker : after.item.clone.execution.invalidated = false

/-- The same actual free derives final ownership, allocation frames and key
liveness for both the normalized defer and transferred-argument errdefer. -/
theorem CallerInput.free_incoming (ops : Operations σ) (allocator : Nat)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (request : Interner.Request) (values : List NodeId) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ)) (reached : Frame σ)
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (initial : Valid (memory reached)) (live : Memory.SliceValid allocator (memory reached).heap normalized)
    (native : ∀ id cell, taken.world.memory.memory.heap.lookup id = some cell → (memory reached).memory.heap.lookup id = some cell)
    (registered : ∀ id block, taken.world.memory.heap id = some block → (memory reached).heap id = some block)
    (keys : (memory reached).effects.keys = taken.world.memory.effects.keys)
    (cleared : reached.item.object = none ∧ reached.item.clone.value = none ∧ reached.item.clone.execution.invalidated = false) :
    ∃ released,
      free (Publication.external ops.arguments) allocator normalized (memory reached) = (.ok (), released) ∧
      CallerPreparationFailure allocator normalized before (memory reached) (withMemory reached released) ∧
      released.effects = (if normalized.items.isEmpty then (memory reached).effects
        else (Publication.external ops.arguments).free normalized (memory reached)) ∧
      (∀ id, (memory reached).heap id = none ∧ (memory reached).memory.heap.lookup id = none →
        released.heap id = none ∧ released.memory.heap.lookup id = none) := by
  obtain ⟨released, freed, valid, post, effects⟩ :=
    free_valid (Publication.external ops.arguments) allocator normalized (memory reached) initial live
  let after := withMemory reached released
  have table := free_keys ops.arguments allocator normalized (memory reached)
  rw [freed] at table
  change released.effects.keys = (memory reached).effects.keys at table
  have finalKeys : (memory after).effects.keys = taken.world.memory.effects.keys := table.trans keys
  refine ⟨released, freed, ⟨valid, released_consumed post, post.nextId, post.nextAddress,
    finalKeys.trans entry.keys, ?_, ?_, ?_, ?_, cleared.1, cleared.2.1, cleared.2.2⟩,
    effects, free_keeps_dead _ _ _ _ _ freed post⟩
  · intro query old found
    rw [finalKeys] at found
    rcases entry.live query old found with empty | stored
    · exact Or.inl empty
    · by_cases empty : query.arguments = []
      · exact Or.inl empty
      · exact Or.inr ((post.frame old.address (entry.fresh query old found empty).symm).1.trans
          (registered old.address _ stored))
  · rw [finalKeys]; exact entry.unique
  · intro id cell found
    exact (post.frame id (entry.origin.freshNative id cell found).symm).2.trans
      (native id cell (entry.origin.memory id cell found))
  · intro id block stored
    exact (post.frame id (entry.origin.fresh id block stored).symm).1.trans
      (registered id block (entry.origin.registry id block stored))

/-- Release the selected transferred arguments using the caller's actual origin.
The existing theorem statement is unchanged; the normalized-defer path shares
the same native free and ownership derivation. -/
theorem CallerInput.transferred_argument_cleanup (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (request : Interner.Request) (values : List NodeId) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ)) (owner : Storage.State) (reached : Frame σ)
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (initial : Valid (memory reached)) (live : Memory.SliceValid allocator (memory reached).heap normalized)
    (present : arguments normalized owner reached = some normalized)
    (native : ∀ id cell, taken.world.memory.memory.heap.lookup id = some cell → (memory reached).memory.heap.lookup id = some cell)
    (registered : ∀ id block, taken.world.memory.heap id = some block → (memory reached).heap id = some block)
    (keys : (memory reached).effects.keys = taken.world.memory.effects.keys)
    (cleared : reached.item.object = none ∧ reached.item.clone.value = none ∧ reached.item.clone.execution.invalidated = false) :
    ∃ after,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).release
        .arguments owner reached = (.ok (), after) ∧
      CallerPreparationFailure allocator normalized before (memory reached) after ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory reached).effects
        else (Publication.external ops.arguments).free normalized (memory reached)) ∧
      (∀ id, (memory reached).heap id = none ∧ (memory reached).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  obtain ⟨released, freed, post, effects, dead⟩ := entry.free_incoming ops allocator source itemSource request values input key normalized lookup
    before taken reached initial live native registered keys cleared
  refine ⟨withMemory reached released, ?_, post, effects, dead⟩
  simp only [callbacks, Insertion.callbacks, present, freed, Except.mapError]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
