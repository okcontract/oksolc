/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparation
import Compiler.Extraction.StoragePreparedRollback

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

def preparedFrame (object : Nat) (copied : AssemblyClone.NativeFields.ItemValue) (operands : ArgumentSlice)
    (state : Session (Publication.Effects σ)) : Frame σ :=
  ⟨⟨⟨⟨state, false⟩, some copied⟩, some object⟩, some operands⟩

/-- Complete deterministic source execution on the spare-capacity/publication-OOM
path. Successful duplication, creation and clone observations are actual calls,
not final ownership assumptions. Initialization, other failure paths, growth and
native hash-map refinement remain separate obligations. -/
theorem deterministic_spare_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity object : Nat) (ownerCell backing : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid before.memory) (normalizedLive : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory itemSource input)
    (admitted : Admitted ops.arguments)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingFound : before.memory.memory.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator before.memory.heap lifetime cells)
    (rows : DescriptorRelation.Prefix before.memory.memory lifetime cells)
    (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1)
    (publication : Publication.Input allocator source key normalized before)
    (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before.memory = (.ok (operands, remaining), duplicated))
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container cells input key normalized
        ((key.eval meaning before.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (false, probeEffects)) :
    let handed := Storage.publicationOwnership
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells before =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap lifetime cells ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true := by
  dsimp only
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨installed, duplicateCall, createCall, cloneCall, installedPost, assigned, values, operandLive,
      normalizedKept, separate, frame, keys, _, _, _⟩ :=
    prepare_owned ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands cells value graph
      start duplicated allocated middle remaining initial normalizedLive represented rfl admitted taken created cloned
  let ready := preparedFrame object copied operands installed
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  change ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe) at duplicateCall
  change ∀ owner, calls.attempt .item owner dupe = (.ok true, made) at createCall
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneCall
  change installed.effects.keys = before.memory.effects.keys at keys
  change ∀ id cell, before.memory.memory.heap.lookup id = some cell →
    installed.memory.heap.lookup id = some cell ∧ installed.heap id = before.memory.heap id at frame
  have ownerFrame := (frame container ownerCell ownerFound).1.trans ownerFound.symm
  have backingFrame := (frame lifetime backing backingFound).1.trans backingFound.symm
  have publicationInput := Publication.Input.frame allocator source key normalized before
    ⟨graph preparationOwnership ready, memory ready⟩ publication keys
    (arguments_retained before.memory installed initial (fun id cell found => (frame id cell found).2) allocator)
  have argumentBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized before.memory initial normalizedLive).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound before.memory.memory (view normalized) normalized.items represented
    rw [values]
    omega
  obtain ⟨appended, failed, popped, after, appendedRun, publicationRun, _, rolled, cleaned, _, valid, vector, finalHeader,
      _, _, _, _, objectCleared, valueCleared, invalidated⟩ :=
    spare_publication_oom_cleanup ops allocate runtimeSafety allocator container lifetime capacity object ownerCell backing input copied key
      normalized operands cells value preparationOwnership middle ready source itemSource graph installedPost rfl rfl rfl
      (ownerFrame.trans ownerFound) ownerTyped ownerWritable (backingFrame.trans backingFound) backingTyped backingWritable
      ((readField_eq_of_lookup before.memory.memory installed.memory (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup before.memory.memory installed.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      ((frame lifetime backing backingFound).2.trans registered) (DescriptorRelation.frame _ _ lifetime cells rows backingFrame)
      spare room argumentBound operandLive normalizedKept separate publicationInput probeEffects (response installed assigned)
  refine ⟨after, ?_, valid, vector, finalHeader, objectCleared, valueCleared, invalidated⟩
  have roomTrue : decide (cells.length < 2 ^ 32 - 1) = true := by simp only [room, decide_true]
  let handed := Storage.publicationOwnership
  change calls.attempt .append preparationOwnership ready = (.ok true, appended) at appendedRun
  change calls.attempt .publish handed appended = (.ok false, failed) at publicationRun
  change (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls handed failed =
    ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), popped) at rolled
  change (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls handed failed =
    ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) at cleaned
  change Storage.insertProgram.execute ⟨true, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ calls {} start = _
  rw [roomTrue]
  exact Storage.insert_prepared_oom calls start dupe made ready appended failed popped after
    duplicateCall createCall cloneCall appendedRun publicationRun rolled cleaned

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
