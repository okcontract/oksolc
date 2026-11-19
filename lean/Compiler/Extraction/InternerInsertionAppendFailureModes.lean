/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendFailure
import Compiler.Extraction.StorageTransferredInsertion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Actual source selection before item creation. The transferred branch skips
argument duplication and uses the reached session and existing owner directly. -/
def PreparationInput (ops : Operations σ) (allocator : Nat) (normalized operands : ArgumentSlice)
    (remaining : Handle) (deterministic : Bool) (before duplicated : Session (Publication.Effects σ)) : Prop :=
  if deterministic then takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
    ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), duplicated)
  else operands = normalized ∧ duplicated = before

def preparedFrameAt (deterministic : Bool) (object : Nat) (copied : AssemblyClone.NativeFields.ItemValue)
    (operands : ArgumentSlice) (installed : Session (Publication.Effects σ)) : Frame σ :=
  ⟨⟨⟨⟨installed, false⟩, some copied⟩, some object⟩, if deterministic then some operands else none⟩

def preparationOwnershipAt (deterministic : Bool) : Storage.State :=
  if deterministic then preparationOwnership else transferredPreparation

def appendFailureState (deterministic : Bool) : Storage.State :=
  if deterministic then (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership
  else (Storage.Cleanup.sequence [.value, .allocation, .arguments]).run transferredPreparation

theorem prepared_arguments (ops : Operations σ) (allocator object : Nat) (normalized operands : ArgumentSlice)
    (remaining : Handle) (deterministic : Bool) (before duplicated installed : Session (Publication.Effects σ))
    (copied : AssemblyClone.NativeFields.ItemValue)
    (selected : PreparationInput ops allocator normalized operands remaining deterministic before duplicated) :
    arguments normalized (preparationOwnershipAt deterministic) (preparedFrameAt deterministic object copied operands installed) =
      some operands := by
  cases deterministic with
  | true => rfl
  | false => exact congrArg some selected.1.symm

/-- Source-selected preparation and append refusal derive the same private
frame. The duplicated branch reuses its existing proof; the transferred branch
uses the common native preparation and local cleanup with one argument owner. -/
theorem append_oom_reached_at (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety deterministic : Bool) (allocator container object : Nat)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (admitted : deterministic = true → Admitted ops.arguments) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : PreparationInput ops allocator normalized operands remaining deterministic world.memory duplicated)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ) (growth : Option (Growth.Registered.Callbacks σ))
    (refused : ∀ installed,
      AssemblyClone.NativeFields.Installed allocator object copied middle installed →
      AssemblyClone.NativeFields.install copied object middle = .ok installed →
      (∀ id cell, world.memory.memory.heap.lookup id = some cell →
        installed.memory.heap.lookup id = some cell ∧ installed.heap id = world.memory.heap id) →
      append runtimeSafety allocate allocator container cells input key normalized
        ((key.eval meaning world.graph.read).getD 0) (preparationOwnershipAt deterministic) (preparedFrameAt deterministic object copied operands installed) growth =
          (.ok false, withMemory (preparedFrameAt deterministic object copied operands installed)
            { installed with effects := { installed.effects with allocator := allocationEffects } })) :
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells world growth =
        ((.ok (some .allocationFailure), appendFailureState deterministic), after) ∧
      Valid (memory after) ∧ PrivateFrame normalized world.memory (memory after) ∧
      Consumed normalized (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧
      (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = false ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  cases deterministic with
  | true =>
    exact append_oom_reached ops allocate runtimeSafety allocator container object source itemSource meaning input copied key
      normalized operands remaining world cells duplicated allocated middle initial live represented (admitted rfl) room
      duplicateCall createCall cloneCall allocationEffects growth refused
  | false =>
    change operands = normalized ∧ duplicated = world.memory at duplicateCall
    obtain ⟨operandsEq, duplicatedEq⟩ := duplicateCall
    subst operands
    subst duplicated
    let value := (key.eval meaning world.graph.read).getD 0
    let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
      (cell input key normalized value owner state) key owner
    let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
    obtain ⟨installed, createRun, cloneRun, installedPost, assigned, frame, keys, _, _⟩ :=
      prepare_item ops allocate runtimeSafety allocator container object source itemSource input copied key normalized cells value graph
        start allocated middle initial represented rfl createCall cloneCall
    let ready := preparedFrameAt false object copied normalized installed
    let failed := withMemory ready { installed with effects := { installed.effects with allocator := allocationEffects } }
    let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, none⟩
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth
    change ∀ owner, calls.attempt .item owner start = (.ok true, made) at createRun
    change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneRun
    have appendRun : calls.attempt .append transferredPreparation ready = (.ok false, failed) :=
      refused installed installedPost assigned frame
    have normalizedLive := arguments_retained world.memory installed initial
      (fun id cell found => (frame id cell found).2) allocator normalized live
    obtain ⟨valueFreed, destroyed, after, valueRun, objectRun, argumentRun, _, post, _⟩ :=
      local_cleanup ops allocate runtimeSafety allocator container object source itemSource input copied key normalized normalized cells value graph
        transferredPreparation failed ⟨installedPost.valid.memory, installedPost.valid.related, installedPost.valid.injected⟩ rfl rfl
        installedPost.owned installedPost.reads installedPost.payload normalizedLive
    change calls.release .value transferredPreparation failed = _ at valueRun
    change calls.release .allocation (Storage.Release.value.run transferredPreparation) valueFreed = _ at objectRun
    change calls.release .arguments (Storage.Release.allocation.run (Storage.Release.value.run transferredPreparation)) destroyed = _ at argumentRun
    have fresh := item_cleanup_apart ops allocator object input copied world.memory allocated middle initial createCall cloneCall
    have retained : PrivateFrame normalized world.memory (memory after) := by
      refine ⟨post.keys.trans keys, ?_⟩
      intro id native found normalizedApart
      have apart := fresh id native found
      have kept := post.frame id apart.1 apart.2 normalizedApart normalizedApart
      exact ⟨kept.2.trans (frame id native found).1, kept.1.trans (frame id native found).2⟩
    have consumed : Consumed normalized (memory after) := by
      by_cases empty : normalized.items = []
      · exact Or.inl empty
      · exact Or.inr (post.released normalized.address (Or.inr (Or.inr (Or.inr ⟨empty, rfl⟩))))
    refine ⟨after, ?_, post.valid, retained, consumed,
      post.nextId.trans installedPost.written.nextId, post.nextAddress.trans installedPost.written.nextAddress,
      post.objectCleared, post.value, post.marker, post.released⟩
    have executed := Storage.insert_transferred_append_oom calls start made ready failed valueFreed destroyed after
      createRun cloneRun appendRun valueRun objectRun argumentRun
    simpa only [execution, room, decide_true] using executed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
