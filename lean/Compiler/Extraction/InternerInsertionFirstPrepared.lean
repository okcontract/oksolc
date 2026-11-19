/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparedRollback
import Compiler.Extraction.InternerInsertionFirstOwnership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Complete deterministic source execution through first backing allocation,
publication OOM and outer normalized cleanup. Actual preparation derives the
owners. The external backing response is bound to the reached installed state;
its freshness is the existing host-allocation precondition, not a final owner.
Cleanup preserves the new empty backing and its advanced allocation history. -/
theorem deterministic_first_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object base : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (sentinel : Compiler.ZigAir.Memory.Address)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (before : World (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid before.memory) (normalizedLive : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory itemSource input)
    (admitted : Admitted ops.arguments)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 0)))
    (publication : Publication.Input allocator source key normalized before)
    (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before.memory = (.ok (operands, remaining), duplicated))
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base)
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container [] input key normalized
        ((key.eval meaning before.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (false, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let handed := Storage.publicationOwnership
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true [] before =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap middle.memory.nextId [] ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ 0, .scalar (.int false 64 5)) ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + 160) ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true := by
  dsimp only
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project [] before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨installed, duplicateCall, createCall, cloneCall, installedPost, assigned, values, operandLive,
      normalizedKept, separate, frame, keys, _, _, _⟩ :=
    prepare_owned ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands [] value graph
      start duplicated allocated middle remaining initial normalizedLive represented rfl admitted taken created cloned
  let ready := preparedFrame object copied operands installed
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized [] value graph
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  change ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe) at duplicateCall
  change ∀ owner, calls.attempt .item owner dupe = (.ok true, made) at createCall
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneCall
  change installed.effects.keys = before.memory.effects.keys at keys
  change ∀ id cell, before.memory.memory.heap.lookup id = some cell →
    installed.memory.heap.lookup id = some cell ∧ installed.heap id = before.memory.heap id at frame
  have ownerFrame := (frame container ownerCell ownerFound).1.trans ownerFound.symm
  have publicationInput := Publication.Input.frame allocator source key normalized before
    ⟨graph preparationOwnership ready, memory ready⟩ publication keys
    (arguments_retained before.memory installed initial (fun id cell found => (frame id cell found).2) allocator)
  have argumentBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized before.memory initial normalizedLive).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound before.memory.memory (view normalized) normalized.items represented
    rw [values]
    omega
  obtain ⟨appended, failed, popped, after, appendedRun, publicationRun, _, rolled, cleaned, _, valid, vector, finalHeader,
      _, _, finalId, finalAddress, objectCleared, valueCleared, invalidated⟩ :=
    first_publication_oom_cleanup ops allocate runtimeSafety allocator container object base ownerCell sentinel input copied key
      normalized operands value preparationOwnership middle ready source itemSource graph installedPost rfl rfl rfl
      (ownerFrame.trans ownerFound) ownerTyped ownerWritable
      ((readField_eq_of_lookup before.memory.memory installed.memory (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup before.memory.memory installed.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      argumentBound allocationEffects (backing installed assigned).1 (backing installed assigned).2
      operandLive normalizedKept separate publicationInput probeEffects (response installed assigned)
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  change Memory.Vector allocator (memory after).heap installed.memory.nextId [] at vector
  change (memory after).memory.nextId = installed.memory.nextId + 1 at finalId
  change (memory after).memory.nextAddress = max installed.memory.nextAddress (base + 160) at finalAddress
  change readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
    .ok (.slice itemsType ⟨installed.memory.nextId, 0⟩ 0, .scalar (.int false 64 5)) at finalHeader
  have installedId : installed.memory.nextId = middle.memory.nextId := installedPost.written.nextId
  have installedAddress : installed.memory.nextAddress = middle.memory.nextAddress := installedPost.written.nextAddress
  rw [installedId] at vector finalId finalHeader
  rw [installedAddress] at finalAddress
  refine ⟨after, ?_, valid, vector, finalHeader, finalId, finalAddress, objectCleared, valueCleared, invalidated⟩
  let handed := Storage.publicationOwnership
  change calls.attempt .append preparationOwnership ready = (.ok true, appended) at appendedRun
  change calls.attempt .publish handed appended = (.ok false, failed) at publicationRun
  change (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls handed failed =
    ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), popped) at rolled
  change (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls handed failed =
    ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) at cleaned
  change Storage.insertProgram.execute ⟨true, decide (([] : List Storage.Cell).length < 2 ^ 32 - 1), fun _ => false⟩ calls {} start = _
  change Storage.insertProgram.execute ⟨true, true, fun _ => false⟩ calls {} start = _
  exact Storage.insert_prepared_oom calls start dupe made ready appended failed popped after
    duplicateCall createCall cloneCall appendedRun publicationRun rolled cleaned


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
