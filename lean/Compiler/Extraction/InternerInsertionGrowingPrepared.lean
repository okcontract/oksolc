/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparedRollback
import Compiler.Extraction.InternerInsertionGrowingOwnership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Deterministic insertion through nonempty growth, publication OOM and
outer normalized cleanup. Actual preparation establishes the cloned object's
owners, and growth transports them into the cleanup call. Initial native graph
correspondence and the captured remap identity remain explicit obligations. -/
theorem deterministic_growing_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid before.memory) (normalizedLive : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory itemSource input)
    (admitted : Admitted ops.arguments)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (oldOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity before.memory)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 oldCapacity)))
    (registered : Memory.Vector allocator before.memory.heap oldLifetime cells)
    (rows : DescriptorRelation.Prefix before.memory.memory oldLifetime cells)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (publication : Publication.Input allocator source key normalized before)
    (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before.memory = (.ok (operands, remaining), duplicated))
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base)
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container cells input key normalized
        ((key.eval meaning before.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)
        (some ⟨.noRemap context returnAddress, freeBacking⟩)).2)) =
        (false, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let handed := Storage.publicationOwnership
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells before (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap middle.memory.nextId cells ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ capacity (memory after) ∧
      DescriptorRelation.Prefix (memory after).memory middle.memory.nextId cells ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨container, 0⟩) id =
        .ok ((Storage.representativeProgram.run cells id).map (DescriptorRelation.values id.toNat))) := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  let value := (key.eval meaning before.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let start : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨installed, duplicateCall, createCall, cloneCall, installedPost, assigned, values, operandLive,
      normalizedKept, separate, frame, keys, _, _, _⟩ :=
    prepare_owned ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands cells value graph
      start duplicated allocated middle remaining initial normalizedLive represented rfl admitted taken created cloned
  let ready := preparedFrame object copied operands installed
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph (some growth)
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  change ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe) at duplicateCall
  change ∀ owner, calls.attempt .item owner dupe = (.ok true, made) at createCall
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneCall
  change installed.effects.keys = before.memory.effects.keys at keys
  change ∀ id cell, before.memory.memory.heap.lookup id = some cell →
    installed.memory.heap.lookup id = some cell ∧ installed.heap id = before.memory.heap id at frame
  obtain ⟨ownerKept, oldOwned, headerKept, capacityKept, vectorKept, rowsKept, publicationInput⟩ :=
    preparation_graph_frame allocator container oldLifetime oldCapacity ownerCell source key normalized cells before
      ⟨graph preparationOwnership ready, memory ready⟩ initial frame keys ownerFound oldOwned header capacityRead registered rows publication
  have argumentBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized before.memory initial normalizedLive).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound before.memory.memory (view normalized) normalized.items represented
    rw [values]
    omega
  obtain ⟨appended, failed, popped, after, appendedRun, publicationRun, _, rolled, cleaned, _, valid, vector, finalHeader,
      _, _, finalId, finalAddress, objectCleared, valueCleared, invalidated, owned, finalRows, oldDead, nativeDead, _, _⟩ :=
    growing_publication_oom_cleanup ops allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity object base context returnAddress ownerCell input copied key
      normalized operands cells value preparationOwnership middle ready source itemSource graph installedPost rfl rfl rfl
      ownerKept ownerTyped ownerWritable oldOwned headerKept capacityKept vectorKept rowsKept
      oldNonempty full selected size room argumentBound allocationEffects (backing installed assigned).1 (backing installed assigned).2
      operandLive normalizedKept separate publicationInput probeEffects (response installed assigned)
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped (ownerKept.trans ownerFound.symm)).trans unlocked)
  change Memory.Vector allocator (memory after).heap installed.memory.nextId cells at vector
  change (memory after).memory.nextId = installed.memory.nextId + 1 at finalId
  change (memory after).memory.nextAddress = max installed.memory.nextAddress (base + capacity * 32) at finalAddress
  change readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
    .ok (.slice itemsType ⟨installed.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) at finalHeader
  change Backing.Release.Owned allocator ⟨installed.memory.nextId, 0⟩ capacity (memory after) at owned
  change DescriptorRelation.Prefix (memory after).memory installed.memory.nextId cells at finalRows
  have installedId : installed.memory.nextId = middle.memory.nextId := installedPost.written.nextId
  have installedAddress : installed.memory.nextAddress = middle.memory.nextAddress := installedPost.written.nextAddress
  rw [installedId] at vector finalId finalHeader owned finalRows
  rw [installedAddress] at finalAddress
  have queries (id : NodeId) : representativeFields (memory after).memory (Owner.headerAddress ⟨container, 0⟩) id =
      .ok ((Storage.representativeProgram.run cells id).map (DescriptorRelation.values id.toNat)) := by
    obtain ⟨_, _, backing, found, typed, writable, _⟩ := owned
    have width : Append.nextLength cells.length < Compiler.ZigAir.Memory.addressLimit := by
      simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega
    have enough : Append.nextLength cells.length ≤ capacity := selected ▸ Capacity.grow_sufficient _ width
    exact DescriptorRelation.query (memory after).memory (Owner.headerAddress ⟨container, 0⟩) middle.memory.nextId capacity backing
      cells id valid.memory (readHeader_items _ _ _ _ finalHeader) found typed writable
      (by simp only [Append.nextLength] at enough; omega) finalRows
  refine ⟨after, ?_, valid, vector, finalHeader, finalId, finalAddress, objectCleared, valueCleared, invalidated,
    owned, finalRows, oldDead, nativeDead, queries⟩
  let handed := Storage.publicationOwnership
  change calls.attempt .append preparationOwnership ready = (.ok true, appended) at appendedRun
  change calls.attempt .publish handed appended = (.ok false, failed) at publicationRun
  change (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls handed failed =
    ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), popped) at rolled
  change (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls handed failed =
    ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) at cleaned
  change Storage.insertProgram.execute ⟨true, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ calls {} start = _
  rw [show decide (cells.length < 2 ^ 32 - 1) = true from decide_eq_true room]
  exact Storage.insert_prepared_oom calls start dupe made ready appended failed popped after
    duplicateCall createCall cloneCall appendedRun publicationRun rolled cleaned
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
