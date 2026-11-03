/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionPreparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Compose reached preparation with a proved append/refusal/rollback suffix.
The continuation receives only facts derived by preparation, including the full
old-allocation frame and publication admission. Its postcondition is internal
to this sequential composition rule: native callers discharge the continuation
from actual capacity, allocation and probe observations. No final graph or
constructor correspondence is provided by this rule. -/
theorem prepare_publication_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator container object : Nat) (source : View)
    (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (publication : Publication.Input allocator source key normalized world) (admitted : Admitted ops.arguments)
    (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (post : Frame σ → Prop)
    (finish :
      let value := (key.eval meaning world.graph.read).getD 0
      let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
        (cell input key normalized value owner state) key owner
      let calls := callbacks ops allocate safety allocator container source itemSource input key normalized cells value graph growth
      ∀ installed,
        AssemblyClone.NativeFields.Installed allocator object copied middle installed →
        AssemblyClone.NativeFields.install copied object middle = .ok installed →
        operands.items = normalized.items →
        Memory.SliceValid allocator installed.heap operands →
        Memory.SliceValid allocator installed.heap normalized →
        (operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) →
        (∀ id native, world.memory.memory.heap.lookup id = some native →
          installed.memory.heap.lookup id = some native ∧ installed.heap id = world.memory.heap id) →
        installed.effects.keys = world.memory.effects.keys →
        Publication.Input allocator source key normalized
          ⟨graph preparationOwnership (preparedFrame object copied operands installed), installed⟩ →
        ∃ appended failed popped after,
          calls.attempt .append preparationOwnership (preparedFrame object copied operands installed) = (.ok true, appended) ∧
          calls.attempt .publish Storage.publicationOwnership appended = (.ok false, failed) ∧
          (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls Storage.publicationOwnership failed =
            ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run Storage.publicationOwnership), popped) ∧
          (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls Storage.publicationOwnership failed =
            ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
          post after) :
    ∃ after,
      execution ops allocate safety allocator container source itemSource meaning input key normalized true cells world growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
      post after := by
  let value := (key.eval meaning world.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, sameValues, operandsLive,
      normalizedLive, separate, frame, keys, _, _, _⟩ :=
    prepare_owned ops allocate safety allocator container object source itemSource input copied key normalized operands cells value graph
      start duplicated allocated middle remaining initial live represented rfl admitted duplicateCall createCall cloneCall
  have publicationInput := Publication.Input.frame allocator source key normalized world
    ⟨graph preparationOwnership (preparedFrame object copied operands installed), installed⟩ publication keys
    (arguments_retained world.memory installed initial (fun id native found => (frame id native found).2) allocator)
  obtain ⟨appended, failed, popped, after, appendedRun, publicationRun, rolled, cleaned, result⟩ :=
    finish installed installedPost assigned sameValues operandsLive normalizedLive separate frame keys publicationInput
  let ready := preparedFrame object copied operands installed
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  let calls := callbacks ops allocate safety allocator container source itemSource input key normalized cells value graph growth
  change ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe) at duplicateRun
  change ∀ owner, calls.attempt .item owner dupe = (.ok true, made) at createRun
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneRun
  refine ⟨after, ?_, result⟩
  have executed := Storage.insert_prepared_oom calls start dupe made ready appended failed popped after
    duplicateRun createRun cloneRun appendedRun publicationRun rolled cleaned
  simpa only [execution, room, decide_true] using executed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
