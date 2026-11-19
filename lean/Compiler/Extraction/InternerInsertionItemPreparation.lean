/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparationEffects
import Compiler.Extraction.InternerInsertionAppendOwnership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Native creation and cloning allocate their cleanup owners after every
allocation at the reached input, independently of argument ownership mode. -/
theorem item_cleanup_apart (ops : Operations σ) (allocator object : Nat)
    (input copied : AssemblyClone.NativeFields.ItemValue)
    (before allocated middle : Session (Publication.Effects σ)) (initial : Valid before)
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item before = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    ∀ id cell, before.memory.heap.lookup id = some cell →
      id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id := by
  have createdPost := AssemblyItem.Creation.create_verified (observe ops.create) allocator object input.item before allocated initial created
  have copiedPost := AssemblyClone.Physical.run_valid (observe ops.copy) allocator input copied allocated middle createdPost.valid cloned
  intro id cell found
  have beforeObject := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell initial.memory found).1
  have apartObject : id ≠ object := by rw [createdPost.fresh]; omega
  have allocatedFound := (createdPost.frame id apartObject).2.trans found
  have beforePayload := (Compiler.ZigAir.Memory.valid_lookup allocated.memory id cell createdPost.valid.memory allocatedFound).1
  refine ⟨apartObject, ?_⟩
  rintro ⟨slice, selected, nonempty, same⟩
  have fresh := copiedPost.fresh slice selected nonempty
  exact (Nat.ne_of_lt beforePayload) (same.trans fresh)

/-- Item creation and clone installation are shared by duplicated and transferred
argument ownership. Their actual native executions derive installed fields,
object ownership and the frame for all preexisting allocations. -/
theorem prepare_item (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (before : Frame σ) (allocated middle : Session (Publication.Effects σ))
    (initial : Valid (memory before))
    (represented : AssemblyClone.NativeFields.Represents (memory before).memory itemSource input)
    (absent : before.item.object = none)
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item (memory before) = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    let made : Frame σ := { withMemory before allocated with item := { (withMemory before allocated).item with object := some object } }
    ∃ installed,
      let ready : Frame σ := { withMemory made installed with item := { (withMemory made installed).item with clone :=
        { (withMemory made installed).item.clone with value := some copied } } }
      (∀ owner, calls.attempt .item owner before = (.ok true, made)) ∧
      (∀ owner, calls.attempt .clone owner made = (.ok true, ready)) ∧
      AssemblyClone.NativeFields.Installed allocator object copied middle (memory ready) ∧
      AssemblyClone.NativeFields.install copied object middle = .ok (memory ready) ∧
      (∀ id cell, (memory before).memory.heap.lookup id = some cell →
        (memory ready).memory.heap.lookup id = some cell ∧ (memory ready).heap id = (memory before).heap id) ∧
      (memory ready).effects.keys = (memory before).effects.keys ∧
      (memory ready).heap object = some ⟨allocator, .item copied.item⟩ ∧ copied.item = input.item := by
  dsimp only
  let made : Frame σ := { withMemory before allocated with item := { (withMemory before allocated).item with object := some object } }
  have createdPost := AssemblyItem.Creation.create_verified (observe ops.create) allocator object input.item (memory before) allocated initial created
  have copiedPost := AssemblyClone.Physical.run_valid (observe ops.copy) allocator input copied allocated middle createdPost.valid cloned
  have sourceCreated := AssemblyItem.Creation.NativeFields.represented_after_create (memory before) allocated allocator object itemSource input
    initial represented createdPost
  let rest : Storage.Operations (AssemblyItem.Creation.NativeFields.State (Publication.Effects σ)) AssemblyItem.Creation.Insertion.Fault :=
    { attempt := fun _ _ state => (.error .missingObject, state), release := fun _ _ state => (.error .missingObject, state) }
  obtain ⟨installed, cloneCall, installedPost, assigned⟩ := AssemblyItem.Creation.NativeFields.clone_callback_installed (observe ops.create) (observe ops.copy)
    (release ops.bytes) (release ops.objects) (Publication.external ops.arguments) allocator object itemSource input copied
    (fun _ _ => (arguments normalized {} made).getD ⟨0, []⟩) rest {} made.item middle rfl createdPost.valid
    sourceCreated createdPost.owned cloned
  have originalFrame : ∀ id cell, (memory before).memory.heap.lookup id = some cell →
      installed.memory.heap.lookup id = some cell ∧ installed.heap id = (memory before).heap id := by
    intro id cell found
    have beforeObject := (Compiler.ZigAir.Memory.valid_lookup (memory before).memory id cell initial.memory found).1
    have apartObject : id ≠ object := by rw [createdPost.fresh]; omega
    have createdFrame := createdPost.frame id apartObject
    have allocatedFound := createdFrame.2.trans found
    have beforePayload := (Compiler.ZigAir.Memory.valid_lookup allocated.memory id cell createdPost.valid.memory allocatedFound).1
    have cloneFrame := copiedPost.frame id (by omega)
    exact ⟨(installedPost.written.frame id apartObject).trans (cloneFrame.2.trans allocatedFound),
      by rw [installedPost.heap]; exact cloneFrame.1.trans createdFrame.1⟩
  have keys : installed.effects.keys = (memory before).effects.keys := by
    have createKeys := create_keys ops.create allocator input.item (memory before)
    rw [created] at createKeys
    have cloneKeys := clone_keys ops.copy allocator input allocated
    rw [cloned] at cloneKeys
    rw [installedPost.effects]
    exact cloneKeys.trans createKeys
  refine ⟨installed, ?_, ?_, installedPost, ?_, originalFrame, keys, ?_, copiedPost.same.1⟩
  · intro owner
    simp only [callbacks, items, AssemblyItem.Creation.NativeFields.operations, AssemblyItem.Creation.Insertion.operations,
      withMemory, absent, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    change AssemblyItem.Creation.create (observe ops.create) allocator input.item before.item.clone.execution.memory = _ at created
    rw [created]
    rfl
  · intro owner
    change (let result := (items ops allocator itemSource input normalized {} made).attempt .clone {} made.item;
      (result.1.mapError Fault.item, { made with item := result.2 })) = _
    simp only [items]
    rw [cloneCall]
    rfl
  · exact assigned
  · change installed.heap object = some ⟨allocator, .item copied.item⟩
    rw [installedPost.heap, copiedPost.same.1]
    exact copiedPost.registered createdPost.valid object _ (AssemblyItem.Creation.create_registered _ _ _ _ _ _ created)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
