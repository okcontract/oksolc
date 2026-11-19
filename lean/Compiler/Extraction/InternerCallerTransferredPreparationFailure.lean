/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTransferredCleanup
import Compiler.Extraction.InternerInsertionTransferredFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Specialize the reached private frame to the actual caller's origin. Old
keys and pre-caller allocations are separated from the consumed normalized owner
by the existing caller facts, not by a new final-state observation. -/
theorem TransferredFailure.caller
    {allocator : Nat} {source : View} {address : Compiler.ZigAir.Memory.Address}
    {request : Interner.Request} {values : List NodeId} {input : AssemblyClone.NativeFields.ItemValue}
    {key : Key} {before : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
    {normalized : ArgumentSlice} {lookup : Handle} {history : Session (Publication.Effects σ)} {after : Frame σ}
    (post : TransferredFailure normalized taken.world.memory history after)
    (entry : CallerInput allocator source address request values input key before taken normalized lookup) :
    CallerPreparationFailure allocator normalized before history after := by
  refine ⟨post.valid, post.consumed, post.nextId, post.nextAddress, post.frame.keys.trans entry.keys,
    ?_, ?_, ?_, ?_, post.object, post.value, post.marker⟩
  · intro query old found
    rw [post.frame.keys] at found
    rcases entry.live query old found with empty | stored
    · exact Or.inl empty
    · by_cases empty : query.arguments = []
      · exact Or.inl empty
      · obtain ⟨cell, native, _⟩ := entry.origin.held.1.1.injected _ _ stored
        exact Or.inr ((post.frame.allocations _ cell native (fun _ => (entry.fresh query old found empty).symm)).2.trans stored)
  · rw [post.frame.keys]; exact entry.unique
  · intro id cell found
    exact (post.frame.allocations id cell (entry.origin.memory id cell found)
      (fun _ => (entry.origin.freshNative id cell found).symm)).1
  · intro id block stored
    have current := entry.origin.registry id block stored
    obtain ⟨cell, native, _⟩ := entry.origin.held.1.1.injected _ _ current
    exact (post.frame.allocations id cell native (fun _ => (entry.origin.fresh id block stored).symm)).2.trans current

section Preparation
variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
  (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (meaning : Meaning) (request : Interner.Request) (values : List NodeId)
  (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
  (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
  (cells : List Storage.Cell) (growth : Option (Growth.Registered.Callbacks σ))

/-- Creation OOM uses the caller's transferred owner. The actual source program
never reaches cloning, append or publication, and its one free preserves all
pre-caller allocations and keys. -/
theorem CallerInput.transferred_create_oom
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (failed : Session (Publication.Effects σ)) (room : cells.length < 2 ^ 32 - 1)
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory = (.error .outOfMemory, failed)) :
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized false cells taken.world growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.arguments]).run transferredArguments), after) ∧
      CallerPreparationFailure allocator normalized before failed after ∧
      (memory after).effects = (if normalized.items.isEmpty then failed.effects
        else (Publication.external ops.arguments).free normalized failed) := by
  obtain ⟨after, ran, post, effects⟩ := transferred_create_oom_execution ops allocate runtimeSafety allocator container
    source itemSource meaning input key normalized taken.world cells growth entry.origin.held.1.1 entry.origin.held.2.1 failed room created
  exact ⟨after, ran, post.caller entry, effects⟩

/-- Clone OOM derives object ownership from actual creation and native source
readback. It destroys that object before releasing the transferred arguments;
the failed clone creates no payload owner and allocation history is retained. -/
theorem CallerInput.transferred_clone_oom
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (object : Nat) (allocated failed : Session (Publication.Effects σ)) (room : cells.length < 2 ^ 32 - 1)
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.error .outOfMemory, failed)) :
    ∃ destroyed after : Frame σ,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized false cells taken.world growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.allocation, .arguments]).run transferredCreated), after) ∧
      CallerPreparationFailure allocator normalized before failed after ∧
      AssemblyItem.Released object failed (memory destroyed) ∧
      (memory destroyed).effects = release ops.objects object failed ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory destroyed).effects
        else (Publication.external ops.arguments).free normalized (memory destroyed)) ∧
      (memory after).heap object = none ∧ (memory after).memory.heap.lookup object = none := by
  obtain ⟨destroyed, after, ran, post, released, destroyEffects, effects, dead⟩ := transferred_clone_oom_execution
    ops allocate runtimeSafety allocator container source itemSource meaning input key normalized taken.world cells growth
    entry.origin.held.1.1 entry.origin.held.2.1 entry.item object allocated failed room created cloned
  exact ⟨destroyed, after, ran, post.caller entry, released, destroyEffects, effects, dead⟩

end Preparation
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
