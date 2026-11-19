/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparationFailure
import Compiler.Extraction.InternerInsertionCleanupEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Cleanup before append transfers ownership never touches the owner or vector
as such. Its only writes/releases are the prepared object, its native payload,
and the nonempty argument footprints. Equal descriptors denote one allocation;
the cleanup execution fixes release order and counts. Empty sentinels are not allocations. -/
structure UnappendedCleanup (object : Nat) (payload : Option AssemblyItemDeinit.Bytes)
    (operands normalized : ArgumentSlice) (before after : Frame σ) : Prop where
  valid : Valid (memory after)
  nextId : (memory after).memory.nextId = (memory before).memory.nextId
  nextAddress : (memory after).memory.nextAddress = (memory before).memory.nextAddress
  keys : (memory after).effects.keys = (memory before).effects.keys
  objectCleared : after.item.object = none
  value : after.item.clone.value = none
  marker : after.item.clone.execution.invalidated = before.item.clone.execution.invalidated
  frame : ∀ id, id ≠ object → ¬AssemblyItemDeinit.Touches payload id →
    (operands.items ≠ [] → id ≠ operands.address) → (normalized.items ≠ [] → id ≠ normalized.address) →
    (memory after).heap id = (memory before).heap id ∧
    (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id
  released : ∀ id, id = object ∨ AssemblyItemDeinit.Touches payload id ∨
    (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
    (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none

/-- Empty argument sentinels frame every address; a nonempty release frames
every allocation outside its owned address. -/
theorem argument_free_frame (external : External σ) (allocator : Nat) (slice : ArgumentSlice)
    (before after : Session σ) (ran : free external allocator slice before = (.ok (), after))
    (post : Memory.Arguments.ReleasePost before.heap before.memory allocator slice after.heap after.memory)
    (id : Nat) (apart : slice.items ≠ [] → id ≠ slice.address) :
    after.heap id = before.heap id ∧ after.memory.heap.lookup id = before.memory.heap.lookup id := by
  by_cases empty : slice.items = []
  · have same := (Prod.mk.inj ((free_empty _ _ _ _ empty).symm.trans ran)).2
    rw [← same]; exact ⟨rfl, rfl⟩
  · exact post.frame id (apart empty)

/-- The common native value/object/argument cleanup executes once for the
selected argument descriptor. The repeated descriptor in the footprint denotes
one allocation; the actual sequence fixes the number and order of releases.
Any separate argument owner survives and can supply an enclosing defer. -/
theorem local_cleanup (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (ownership : Storage.State) (before : Frame σ) (initial : Valid (memory before))
    (objectPresent : before.item.object = some object) (argumentsPresent : arguments normalized ownership before = some operands)
    (itemOwned : AssemblyItem.Owned allocator object (memory before))
    (represented : AssemblyClone.NativeFields.Represents (memory before).memory ⟨object, 0⟩ stored)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory before))
    (operandLive : Memory.SliceValid allocator (memory before).heap operands) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    ∃ valueFreed destroyed after,
      calls.release .value ownership before = (.ok (), valueFreed) ∧
      calls.release .allocation (Storage.Release.value.run ownership) valueFreed = (.ok (), destroyed) ∧
      calls.release .arguments (Storage.Release.allocation.run (Storage.Release.value.run ownership)) destroyed = (.ok (), after) ∧
      (Storage.Cleanup.sequence [.value, .allocation, .arguments]).execute calls ownership before =
        ((.ok (), (Storage.Cleanup.sequence [.value, .allocation, .arguments]).run ownership), after) ∧
      UnappendedCleanup object (AssemblyClone.Physical.payload stored) operands operands before after ∧
      (∀ keptAllocator kept, Memory.SliceValid keptAllocator (memory before).heap kept →
        (operands.items ≠ [] → kept.items ≠ [] → kept.address ≠ operands.address) →
        Memory.SliceValid keptAllocator (memory after).heap kept) := by
  dsimp only
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
  obtain ⟨released, deinitialized, deinitCall, _, payloadPost, invalidated, deinitValid, deinitOwned, deinitHeap, _, _⟩ :=
    AssemblyItemDeinit.Native.run_verified (release ops.bytes) allocator object stored (memory before)
      initial itemOwned represented payloadOwned
  obtain ⟨objectState, destroyCall, objectPost, _⟩ :=
    AssemblyItem.destroy_verified (release ops.objects) allocator object deinitialized.memory deinitValid deinitOwned
  have argumentLive (keptAllocator : Nat) (slice : ArgumentSlice) (live : Memory.SliceValid keptAllocator (memory before).heap slice) :
      Memory.SliceValid keptAllocator objectState.heap slice :=
    objectPost.arguments object deinitialized.memory objectState allocator deinitOwned keptAllocator slice
      (deinitHeap ▸ payloadPost.arguments keptAllocator slice live)
  obtain ⟨argumentState, argumentCall, argumentValid, argumentPost, _⟩ :=
    free_valid (Publication.external ops.arguments) allocator operands objectState objectPost.valid (argumentLive allocator operands operandLive)
  let valueFreed : Frame σ := { withMemory before deinitialized.memory with item :=
    { (withMemory before deinitialized.memory).item with clone :=
      { (withMemory before deinitialized.memory).item.clone with value := none } } }
  let destroyed : Frame σ := { withMemory valueFreed objectState with item :=
    { (withMemory valueFreed objectState).item with object := none } }
  let after := withMemory destroyed argumentState
  have valueRun : calls.release .value ownership before = (.ok (), valueFreed) :=
    releaseValue_success ops allocator object before deinitialized objectPresent deinitCall
  have objectRun : calls.release .allocation (Storage.Release.value.run ownership) valueFreed = (.ok (), destroyed) := by
    simp only [calls, callbacks, Insertion.callbacks, itemOperations, AssemblyItem.Creation.Insertion.operations,
      valueFreed, withMemory, objectPresent]
    change (let result := AssemblyItem.destroy (release ops.objects) allocator object deinitialized.memory; _) = _
    rw [destroyCall]
    rfl
  have argumentRun : calls.release .arguments (Storage.Release.allocation.run (Storage.Release.value.run ownership)) destroyed = (.ok (), after) := by
    have aliases (state : Storage.State) (resource : Storage.Resource) (old new : Storage.Owner) :
        (state.move resource old new).aliasesNormalized = state.aliasesNormalized := by
      unfold Storage.State.move
      split <;> rfl
    have retained : (Storage.Release.allocation.run (Storage.Release.value.run ownership)).aliasesNormalized = ownership.aliasesNormalized := by
      simp only [Storage.Release.run]
      split <;> simp only [aliases]
    have present : arguments normalized (Storage.Release.allocation.run (Storage.Release.value.run ownership)) destroyed = some operands := by
      simpa only [arguments, retained] using argumentsPresent
    simp only [calls, callbacks, Insertion.callbacks, present,
      show memory destroyed = objectState from rfl, argumentCall, Except.mapError]
    rfl
  have executed : (Storage.Cleanup.sequence [.value, .allocation, .arguments]).execute calls ownership before =
      ((.ok (), (Storage.Cleanup.sequence [.value, .allocation, .arguments]).run ownership), after) := by
    simp only [Storage.Cleanup.execute, Storage.releaseAll, Storage.Release.execute, valueRun, objectRun, argumentRun]
    rfl
  have itemFrame := Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ invalidated
  refine ⟨valueFreed, destroyed, after, valueRun, objectRun, argumentRun, executed,
    ⟨argumentValid, argumentPost.nextId.trans (objectPost.nextId.trans (itemFrame.1.trans payloadPost.nextId)),
      argumentPost.nextAddress.trans (objectPost.nextAddress.trans (itemFrame.2.1.trans payloadPost.nextAddress)),
      ?_, rfl, rfl, rfl, ?_, ?_⟩, ?_⟩
  · have keys := cleanup_sequence_keys ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
      none [.value, .allocation, .arguments] ownership before
    change (memory ((Storage.Cleanup.sequence [.value, .allocation, .arguments]).execute calls ownership before).2).effects.keys = _ at keys
    rw [executed] at keys
    exact keys
  · intro id objectApart untouched operandsApart _
    have last := argument_free_frame _ _ _ _ _ argumentCall argumentPost id operandsApart
    exact ⟨last.1.trans ((objectPost.frame id objectApart).1.trans
        ((congrFun deinitHeap id).trans (payloadPost.frame id untouched).1)),
      last.2.trans ((objectPost.frame id objectApart).2.trans
        ((itemFrame.2.2 id objectApart).trans (payloadPost.frame id untouched).2))⟩
  · intro id selected
    have objectDead (target : id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id) :
        objectState.heap id = none ∧ objectState.memory.heap.lookup id = none := by
      rcases target with rfl | touched
      · exact objectPost.dead
      · obtain ⟨slice, chosen, nonempty, same⟩ := touched
        have apart : id ≠ object := same ▸ AssemblyItem.payload_ne allocator object slice (memory before) itemOwned (payloadOwned slice chosen) nonempty
        have dead := payloadPost.dead id ⟨slice, chosen, nonempty, same⟩
        exact objectPost.keeps_dead object deinitialized.memory objectState id
          ⟨(congrFun deinitHeap id).trans dead.1, (itemFrame.2.2 id apart).trans dead.2⟩
    rcases selected with item | payload | ⟨nonempty, rfl⟩ | ⟨nonempty, rfl⟩
    · exact free_keeps_dead _ _ _ _ _ argumentCall argumentPost id (objectDead (Or.inl item))
    · exact free_keeps_dead _ _ _ _ _ argumentCall argumentPost id (objectDead (Or.inr payload))
    · exact argumentPost.dead nonempty
    · exact argumentPost.dead nonempty
  · intro keptAllocator kept live separate
    exact release_keeps_arguments allocator keptAllocator operands kept objectState argumentState argumentPost
      (argumentLive keptAllocator kept live) separate

/-- Execute the source's four defers from the same prepared native value. Every
later free precondition is derived through the preceding destructor; no final
frame, released lifetime, or successful cleanup is supplied as a premise. -/
theorem unappended_cleanup (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (before : Frame σ) (initial : Valid (memory before))
    (objectPresent : before.item.object = some object) (argumentsPresent : before.duplicate = some operands)
    (itemOwned : AssemblyItem.Owned allocator object (memory before))
    (represented : AssemblyClone.NativeFields.Represents (memory before).memory ⟨object, 0⟩ stored)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory before))
    (operandLive : Memory.SliceValid allocator (memory before).heap operands)
    (normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    ∃ valueFreed destroyed freed after,
      calls.release .value preparationOwnership before = (.ok (), valueFreed) ∧
      calls.release .allocation (Storage.Release.value.run preparationOwnership) valueFreed = (.ok (), destroyed) ∧
      calls.release .arguments (Storage.Release.allocation.run (Storage.Release.value.run preparationOwnership)) destroyed = (.ok (), freed) ∧
      (∀ owner, calls.release .normalized owner freed = (.ok (), after)) ∧
      (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).execute calls preparationOwnership before =
        ((.ok (), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) ∧
      UnappendedCleanup object (AssemblyClone.Physical.payload stored) operands normalized before after := by
  dsimp only
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
  obtain ⟨valueFreed, destroyed, freed, valueRun, objectRun, argumentRun, _, post, retained⟩ :=
    local_cleanup ops allocate runtimeSafety allocator container object source itemSource input stored key normalized operands cells value graph
      preparationOwnership before initial objectPresent argumentsPresent itemOwned represented payloadOwned operandLive
  change calls.release .value preparationOwnership before = _ at valueRun
  change calls.release .allocation (Storage.Release.value.run preparationOwnership) valueFreed = _ at objectRun
  change calls.release .arguments (Storage.Release.allocation.run (Storage.Release.value.run preparationOwnership)) destroyed = _ at argumentRun
  obtain ⟨finalState, normalizedCall, finalValid, normalizedPost, _⟩ :=
    free_valid (Publication.external ops.arguments) allocator normalized (memory freed) post.valid
      (retained allocator normalized normalizedLive separate)
  let after := withMemory freed finalState
  have normalizedRun : ∀ owner, calls.release .normalized owner freed = (.ok (), after) := by
    intro owner
    simp only [calls, callbacks, Insertion.callbacks, normalizedCall, Except.mapError]
    rfl
  have executed : (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).execute calls preparationOwnership before =
      ((.ok (), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) := by
    simp only [Storage.Cleanup.execute, Storage.releaseAll, Storage.Release.execute, valueRun, objectRun, argumentRun, normalizedRun]
    rfl
  refine ⟨valueFreed, destroyed, freed, after, valueRun, objectRun, argumentRun, normalizedRun, executed,
    finalValid, normalizedPost.nextId.trans post.nextId, normalizedPost.nextAddress.trans post.nextAddress,
    ?_, post.objectCleared, post.value, post.marker, ?_, ?_⟩
  · have keys := cleanup_sequence_keys ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
      none [.value, .allocation, .arguments, .normalized] preparationOwnership before
    change (memory ((Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).execute calls preparationOwnership before).2).effects.keys = _ at keys
    rw [executed] at keys
    exact keys
  · intro id objectApart untouched operandsApart normalizedApart
    have first := post.frame id objectApart untouched operandsApart operandsApart
    have last := argument_free_frame _ _ _ _ _ normalizedCall normalizedPost id normalizedApart
    exact ⟨last.1.trans first.1, last.2.trans first.2⟩
  · intro id selected
    rcases selected with item | payload | operand | ⟨nonempty, rfl⟩
    · exact free_keeps_dead _ _ _ _ _ normalizedCall normalizedPost id (post.released id (Or.inl item))
    · exact free_keeps_dead _ _ _ _ _ normalizedCall normalizedPost id (post.released id (Or.inr (Or.inl payload)))
    · exact free_keeps_dead _ _ _ _ _ normalizedCall normalizedPost id (post.released id (Or.inr (Or.inr (Or.inl operand))))
    · exact normalizedPost.dead nonempty

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
