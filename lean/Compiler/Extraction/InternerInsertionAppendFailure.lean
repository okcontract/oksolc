/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparedRollback
import Compiler.Extraction.InternerInsertionUnappendedCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Compose successful preparation, a source-proved append refusal and the
existing four defers. The refusal retains native memory and only changes private
allocator effects. Cleanup preserves every reached allocation except the
nonempty normalized owner, which may predate this call. Branch adapters derive
the refusal from their capacity and allocator observations. -/
theorem append_oom_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (allocator container object : Nat)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (admitted : Admitted ops.arguments) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ) (growth : Option (Growth.Registered.Callbacks σ))
    (refused : ∀ installed,
      AssemblyClone.NativeFields.Installed allocator object copied middle installed →
      AssemblyClone.NativeFields.install copied object middle = .ok installed →
      (∀ id cell, world.memory.memory.heap.lookup id = some cell →
        installed.memory.heap.lookup id = some cell ∧ installed.heap id = world.memory.heap id) →
      append runtimeSafety allocate allocator container cells input key normalized
        ((key.eval meaning world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed) growth =
          (.ok false, withMemory (preparedFrame object copied operands installed)
            { installed with effects := { installed.effects with allocator := allocationEffects } })) :
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells world growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) ∧
      Valid (memory after) ∧ PrivateFrame normalized world.memory (memory after) ∧
      Consumed normalized (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧
      (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = false ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  let value := (key.eval meaning world.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, _, operandsLive,
      normalizedLive, separate, frame, keys, _, _, _⟩ :=
    prepare_owned ops allocate runtimeSafety allocator container object source itemSource input copied key
      normalized operands cells value graph start duplicated allocated middle remaining initial live represented rfl
      admitted duplicateCall createCall cloneCall
  let ready := preparedFrame object copied operands installed
  let failed := withMemory ready { installed with effects := { installed.effects with allocator := allocationEffects } }
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
  change ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe) at duplicateRun
  change ∀ owner, calls.attempt .item owner dupe = (.ok true, made) at createRun
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneRun
  have appendRun : calls.attempt .append preparationOwnership ready = (.ok false, failed) :=
    refused installed installedPost assigned frame
  obtain ⟨valueFreed, destroyed, freed, after, valueRun, objectRun, argumentRun, normalizedRun, _, post⟩ :=
    unappended_cleanup ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands cells value graph
      failed ⟨installedPost.valid.memory, installedPost.valid.related, installedPost.valid.injected⟩ rfl rfl
      installedPost.owned installedPost.reads installedPost.payload operandsLive normalizedLive separate
  change calls.release .value preparationOwnership failed = _ at valueRun
  change calls.release .allocation (Storage.Release.value.run preparationOwnership) valueFreed = _ at objectRun
  change calls.release .arguments (Storage.Release.allocation.run (Storage.Release.value.run preparationOwnership)) destroyed = _ at argumentRun
  change ∀ owner, calls.release .normalized owner freed = _ at normalizedRun
  have fresh := preparation_cleanup_apart ops allocator object input copied normalized operands remaining world.memory
    duplicated allocated middle initial live admitted duplicateCall createCall cloneCall
  have retained : PrivateFrame normalized world.memory (memory after) := by
    refine ⟨post.keys.trans keys, ?_⟩
    intro id native found normalizedApart
    have apart := fresh id native found
    have kept := post.frame id apart.1 apart.2.1 (fun _ => apart.2.2) normalizedApart
    exact ⟨kept.2.trans (frame id native found).1, kept.1.trans (frame id native found).2⟩
  have consumed : Consumed normalized (memory after) := by
    by_cases empty : normalized.items = []
    · exact Or.inl empty
    · exact Or.inr (post.released normalized.address (Or.inr (Or.inr (Or.inr ⟨empty, rfl⟩))))
  refine ⟨after, ?_, post.valid, retained, consumed,
    post.nextId.trans installedPost.written.nextId, post.nextAddress.trans installedPost.written.nextAddress,
    post.objectCleared, post.value, post.marker, post.released⟩
  have executed := Storage.insert_append_oom calls start dupe made ready failed valueFreed destroyed freed after
    duplicateRun createRun cloneRun appendRun valueRun objectRun argumentRun normalizedRun
  simpa only [execution, room, decide_true] using executed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
