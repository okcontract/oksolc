/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionGrowingPrepared
import Compiler.Extraction.InternerInsertionPublicationSuccess

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Complete deterministic insertion through nonempty growth and successful
publication, including existing-key replacement. Preparation establishes the
incoming owners; the same append and publication executions derive the reached
rows, transfer of the normalized key, retired lifetimes and allocation history.
Initial graph correspondence and native probe/vtable binding remain explicit. -/
theorem deterministic_growing_success (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
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
        (true, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let value := (key.eval meaning before.graph.read).getD 0
    let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ installed appended after,
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      append runtimeSafety allocate allocator container cells input key normalized value preparationOwnership
        (preparedFrame object copied operands installed) (some growth) = (.ok true, appended) ∧
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells before (some growth) =
        ((.ok (some .success), Storage.publishedOwnership), after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap middle.memory.nextId (cells ++ [row]) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) ∧
      Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ capacity (memory after) ∧
      DescriptorRelation.Prefix (memory after).memory middle.memory.nextId (cells ++ [row]) ∧
      (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨container, 0⟩) id =
        .ok ((Storage.representativeProgram.run (cells ++ [row]) id).map (DescriptorRelation.values id.toNat))) ∧
      Memory.SliceValid allocator (memory after).heap normalized ∧
      (memory after).effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      (memory after).effects.allocator = (match before.memory.effects.keys key with
        | none => probeEffects
        | some old => if key.arguments.isEmpty then probeEffects else
            ops.arguments.free (OwnedKeys.slice key old) { Publication.forget (memory appended) with effects := probeEffects }) ∧
      (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
        (memory after).heap old.address = none ∧ (memory after).memory.heap.lookup old.address = none) ∧
      (∀ id, (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).heap id = (memory appended).heap id ∧
        (memory after).memory.heap.lookup id = (memory appended).memory.heap.lookup id) := by
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
  obtain ⟨oldCell, appended, finalOwner, _, appendedRun, appendValid, appendEffects, finalOwnerFound, finalOwnerTyped,
      _, backingOwned, vector, finalHeader, _, _, _, _, _, argumentsKept, _, nextId, nextAddress, oldDead, nativeDead, appendedRows, _, _⟩ :=
    growing_append_owned allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity object base context returnAddress
      ownerCell input copied key normalized operands cells value preparationOwnership middle ready allocationEffects installedPost rfl rfl rfl
      ownerKept ownerTyped ownerWritable oldOwned headerKept capacityKept vectorKept rowsKept oldNonempty full selected size room argumentBound
      (backing installed assigned).1 (backing installed assigned).2
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped (ownerKept.trans ownerFound.symm)).trans unlocked)
  have appendedKeys : (memory appended).effects.keys = before.memory.effects.keys :=
    (congrArg Publication.Effects.keys appendEffects).trans keys
  have publicationInput := Publication.Input.frame allocator source key normalized
    ⟨graph preparationOwnership ready, memory ready⟩ ⟨graph publicationOwnership appended, memory appended⟩ publicationInput
    (appendedKeys.trans keys.symm) (argumentsKept allocator)
  have width : Append.nextLength cells.length < Compiler.ZigAir.Memory.addressLimit := by
    simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega
  have enough : Append.nextLength cells.length ≤ capacity := selected ▸ Capacity.grow_sufficient _ width
  have probe : ops.probe key (Publication.forget (memory appended)) = (true, probeEffects) := by
    have reached := response installed assigned
    rw [appendedRun] at reached
    exact reached
  let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
  obtain ⟨after, published, valid, owned, vector, header, rows, queries, normalizedLive, finalKeys, finalId, finalAddress,
      effects, replaced, deadKept, frame, _, _⟩ :=
    publication_rows ops allocate runtimeSafety allocator container installed.memory.nextId capacity finalOwner source itemSource input key normalized
      cells (cells ++ [row]) value graph publicationOwnership appended (some growth) probeEffects appendValid finalOwnerFound finalOwnerTyped
      backingOwned vector (by simpa only [List.length_append, List.length_singleton] using finalHeader) appendedRows
      (by simpa only [List.length_append, List.length_singleton, Append.nextLength] using enough)
      (argumentsKept allocator normalized normalizedKept) publicationInput probe
  have retired := deadKept oldLifetime ⟨oldDead, nativeDead⟩
  have finalId := finalId.trans nextId
  have finalAddress := finalAddress.trans nextAddress
  have installedId : installed.memory.nextId = middle.memory.nextId := installedPost.written.nextId
  have installedAddress : installed.memory.nextAddress = middle.memory.nextAddress := installedPost.written.nextAddress
  change (memory after).memory.nextId = installed.memory.nextId + 1 at finalId
  change (memory after).memory.nextAddress = max installed.memory.nextAddress (base + capacity * 32) at finalAddress
  rw [installedId] at vector header owned rows finalId
  rw [installedAddress] at finalAddress
  rw [appendedKeys] at finalKeys effects replaced frame
  refine ⟨installed, appended, after, assigned, appendedRun, ?_, valid, vector, ?_, owned, rows, queries, normalizedLive,
    finalKeys, finalId, finalAddress, retired.1, retired.2, effects, replaced, frame⟩
  · change calls.attempt .append preparationOwnership ready = (.ok true, appended) at appendedRun
    change calls.attempt .publish publicationOwnership appended = (.ok true, after) at published
    change Storage.insertProgram.execute ⟨true, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ calls {} start = _
    rw [show decide (cells.length < 2 ^ 32 - 1) = true from decide_eq_true room]
    exact Storage.insert_prepared_success calls start dupe made ready appended after
      duplicateCall createCall cloneCall appendedRun published
  · simpa only [List.length_append, List.length_singleton] using header

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
