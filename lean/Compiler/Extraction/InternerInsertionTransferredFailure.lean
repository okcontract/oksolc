/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparationFailure
import Compiler.Extraction.StorageTransferredInsertion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Native preparation failure at the reached insertion input. Its private
frame permits consumption of the transferred owner without assuming an earlier
caller origin. History and effects belong to the actual failed preparation. -/
structure TransferredFailure (normalized : ArgumentSlice)
    (before history : Session (Publication.Effects σ)) (after : Frame σ) : Prop where
  valid : Valid (memory after)
  consumed : Consumed normalized (memory after)
  nextId : (memory after).memory.nextId = history.memory.nextId
  nextAddress : (memory after).memory.nextAddress = history.memory.nextAddress
  frame : PrivateFrame normalized before (memory after)
  object : after.item.object = none
  value : after.item.clone.value = none
  marker : after.item.clone.execution.invalidated = false

/-- The transferred argument errdefer frees its one owner. This uses the same
native free, private frame and dead-allocation proof as normalized cleanup. -/
theorem transferred_argument_cleanup (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (before : Session (Publication.Effects σ)) (cells : List Storage.Cell) (value : Word)
    (graph : Storage.State → Frame σ → Interner.Heap) (growth : Option (Growth.Registered.Callbacks σ))
    (owner : Storage.State) (reached : Frame σ)
    (valid : Valid (memory reached)) (live : SliceValid allocator (memory reached).heap normalized)
    (present : arguments normalized owner reached = some normalized)
    (retained : ∀ id cell, before.memory.heap.lookup id = some cell →
      (memory reached).memory.heap.lookup id = some cell ∧ (memory reached).heap id = before.heap id)
    (keys : (memory reached).effects.keys = before.effects.keys)
    (cleared : reached.item.object = none ∧ reached.item.clone.value = none ∧ reached.item.clone.execution.invalidated = false) :
    ∃ after,
      (callbacks ops allocate safety allocator container source address input key normalized cells value graph growth).release
        .arguments owner reached = (.ok (), after) ∧
      TransferredFailure normalized before (memory reached) after ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory reached).effects
        else (Publication.external ops.arguments).free normalized (memory reached)) ∧
      (∀ id, (memory reached).heap id = none ∧ (memory reached).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  obtain ⟨released, freed, finalValid, post, effects⟩ :=
    free_valid (Publication.external ops.arguments) allocator normalized (memory reached) valid live
  have frame := free_private_frame ops.arguments allocator normalized (memory reached) released freed post
  refine ⟨withMemory reached released, ?_,
    ⟨finalValid, released_consumed post, post.nextId, post.nextAddress, ⟨frame.keys.trans keys, ?_⟩,
      cleared.1, cleared.2.1, cleared.2.2⟩, effects, free_keeps_dead _ _ _ _ _ freed post⟩
  · simp only [callbacks, Insertion.callbacks, present, freed, Except.mapError]
  · intro id cell found apart
    have current := retained id cell found
    have kept := frame.allocations id cell current.1 apart
    exact ⟨kept.1, kept.2.trans current.2⟩

section Preparation
variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
  (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (meaning : Meaning) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
  (before : World (Publication.Effects σ)) (cells : List Storage.Cell) (growth : Option (Growth.Registered.Callbacks σ))

/-- Actual creation refusal consumes the transferred owner at an arbitrary
valid reached insertion input, preserving all other native allocations. -/
theorem transferred_create_oom_execution
    (valid : Valid before.memory) (live : SliceValid allocator before.memory.heap normalized)
    (failed : Session (Publication.Effects σ)) (room : cells.length < 2 ^ 32 - 1)
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item before.memory = (.error .outOfMemory, failed)) :
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized false cells before growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.arguments]).run transferredArguments), after) ∧
      TransferredFailure normalized before.memory failed after ∧
      (memory after).effects = (if normalized.items.isEmpty then failed.effects
        else (Publication.external ops.arguments).free normalized failed) := by
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  let reached := withMemory start failed
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
  obtain ⟨_, _, same⟩ := AssemblyItem.Creation.create_oom (observe ops.create) allocator input.item before.memory failed created
  have native : failed.memory = before.memory.memory := by rw [same]
  have heap : failed.heap = before.memory.heap := by rw [same]
  have initial : Valid failed := ⟨native ▸ valid.memory,
    by simpa only [heap, native] using valid.related,
    by simpa only [heap, native] using valid.injected⟩
  have keys := create_keys ops.create allocator input.item before.memory
  rw [created] at keys
  obtain ⟨after, argumentCall, post, effects, _⟩ :=
    transferred_argument_cleanup ops allocate runtimeSafety allocator container source itemSource input key normalized
      before.memory cells value graph growth transferredArguments reached initial (heap ▸ live) rfl
      (fun id cell found => ⟨by change failed.memory.heap.lookup id = _; rw [native]; exact found,
        by change failed.heap id = _; rw [heap]⟩) keys ⟨rfl, rfl, rfl⟩
  have createCall : ∀ owner, calls.attempt .item owner start = (.ok false, reached) := by
    intro owner
    simp only [calls, callbacks, items, AssemblyItem.Creation.NativeFields.operations, AssemblyItem.Creation.Insertion.operations,
      start, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    change (let result := AssemblyItem.Creation.create (observe ops.create) allocator input.item before.memory; _) = _
    rw [created]
    rfl
  refine ⟨after, ?_, post, effects⟩
  have executed := Storage.insert_transferred_create_oom calls start reached after createCall argumentCall
  simpa only [execution, room, decide_true] using executed

/-- Actual clone refusal derives object ownership and source reads from native
creation. It destroys the object and frees the transferred owner exactly once. -/
theorem transferred_clone_oom_execution
    (valid : Valid before.memory) (live : SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory itemSource input)
    (object : Nat) (allocated failed : Session (Publication.Effects σ)) (room : cells.length < 2 ^ 32 - 1)
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item before.memory = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.error .outOfMemory, failed)) :
    ∃ destroyed after : Frame σ,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized false cells before growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.allocation, .arguments]).run transferredCreated), after) ∧
      TransferredFailure normalized before.memory failed after ∧
      AssemblyItem.Released object failed (memory destroyed) ∧
      (memory destroyed).effects = release ops.objects object failed ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory destroyed).effects
        else (Publication.external ops.arguments).free normalized (memory destroyed)) ∧
      (memory after).heap object = none ∧ (memory after).memory.heap.lookup object = none := by
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, none⟩
  let reached := withMemory made failed
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
  have createdPost := AssemblyItem.Creation.create_verified (observe ops.create) allocator object input.item before.memory allocated
    valid created
  obtain ⟨heap, native⟩ := AssemblyClone.Physical.run_oom (observe ops.copy) allocator input allocated failed cloned
  have initial : Valid failed := ⟨native ▸ createdPost.valid.memory,
    by simpa only [heap, native] using createdPost.valid.related,
    by simpa only [heap, native] using createdPost.valid.injected⟩
  have owned : AssemblyItem.Owned allocator object failed := by simpa only [AssemblyItem.Owned, heap, native] using createdPost.owned
  have live : Memory.SliceValid allocator failed.heap normalized := by
    rw [heap]
    exact createdPost.arguments allocator object before.memory allocated valid normalized live
  obtain ⟨released, destroyedCall, releasedPost, destroyedEffects⟩ :=
    AssemblyItem.destroy_verified (release ops.objects) allocator object failed initial owned
  let destroyed : Frame σ := { withMemory reached released with item := { (withMemory reached released).item with object := none } }
  have apart (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation) (found : before.memory.memory.heap.lookup id = some cell) : id ≠ object := by
    have older := (Compiler.ZigAir.Memory.valid_lookup before.memory.memory id cell valid.memory found).1
    rw [createdPost.fresh]
    omega
  have retained (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation) (found : before.memory.memory.heap.lookup id = some cell) :
      released.memory.heap.lookup id = some cell ∧ released.heap id = before.memory.heap id :=
    ⟨(releasedPost.frame id (apart id cell found)).2.trans
      ((congrArg (fun m => m.heap.lookup id) native).trans ((createdPost.frame id (apart id cell found)).2.trans found)),
      (releasedPost.frame id (apart id cell found)).1.trans
        ((congrFun heap id).trans (createdPost.frame id (apart id cell found)).1)⟩
  have createKeys := create_keys ops.create allocator input.item before.memory
  rw [created] at createKeys
  have cloneKeys := clone_keys ops.copy allocator input allocated
  rw [cloned] at cloneKeys
  have destroyKeys := destroy_keys ops.objects allocator object failed
  rw [destroyedCall] at destroyKeys
  obtain ⟨after, argumentCall, post, effects, keptDead⟩ :=
    transferred_argument_cleanup ops allocate runtimeSafety allocator container source itemSource input key normalized
      before.memory cells value graph growth (Storage.Release.allocation.run transferredCreated) destroyed releasedPost.valid
      (releasedPost.arguments object failed released allocator owned allocator normalized live) rfl
      retained (destroyKeys.trans (cloneKeys.trans createKeys)) ⟨rfl, rfl, rfl⟩
  have sourceCreated := AssemblyItem.Creation.NativeFields.represented_after_create before.memory allocated allocator object itemSource input
    valid represented createdPost
  have createCall : ∀ owner, calls.attempt .item owner start = (.ok true, made) := by
    intro owner
    simp only [calls, callbacks, items, AssemblyItem.Creation.NativeFields.operations, AssemblyItem.Creation.Insertion.operations,
      start, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    change (let result := AssemblyItem.Creation.create (observe ops.create) allocator input.item before.memory; _) = _
    rw [created]
    rfl
  have cloneCall : ∀ owner, calls.attempt .clone owner made = (.ok false, reached) := by
    intro owner
    have called := AssemblyItem.Creation.NativeFields.clone_oom (observe ops.create) (observe ops.copy)
      (release ops.bytes) (release ops.objects) (Publication.external ops.arguments) allocator object itemSource input
      (fun _ _ => (arguments normalized owner made).getD ⟨0, []⟩)
      { attempt := fun _ _ state => (.error .missingObject, state), release := fun _ _ state => (.error .missingObject, state) }
      owner made.item failed rfl sourceCreated cloned
    change (let result := (items ops allocator itemSource input normalized owner made).attempt .clone owner made.item;
      (result.1.mapError Fault.item, { made with item := result.2 })) = _
    simp only [items]
    rw [called]
    rfl
  have allocationCall : calls.release .allocation transferredCreated reached = (.ok (), destroyed) := by
    simp only [calls, callbacks, Insertion.callbacks, itemOperations, AssemblyItem.Creation.Insertion.operations,
      reached, made, withMemory]
    change (let result := AssemblyItem.destroy (release ops.objects) allocator object failed; _) = _
    rw [destroyedCall]
    rfl
  have finalPost : TransferredFailure normalized before.memory failed after :=
    { post with
      nextId := post.nextId.trans releasedPost.nextId
      nextAddress := post.nextAddress.trans releasedPost.nextAddress }
  refine ⟨destroyed, after, ?_, finalPost, releasedPost, destroyedEffects, effects, keptDead object releasedPost.dead⟩
  have executed := Storage.insert_transferred_clone_oom calls start made reached destroyed after createCall cloneCall allocationCall argumentCall
  simpa only [execution, room, decide_true] using executed

end Preparation
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
