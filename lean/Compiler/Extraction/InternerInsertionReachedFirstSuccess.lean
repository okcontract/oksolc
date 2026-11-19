/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionPreparation
import Compiler.Extraction.InternerCallerGraphCustody
import Compiler.Extraction.InternerInsertionFirstOwnership
import Compiler.Extraction.InternerInsertionPublicationSuccess
import Compiler.Extraction.InternerInsertionNativeProjection
import Compiler.Extraction.RepresentativeBorrowedQuery
import Compiler.Extraction.RepresentativeRegisteredFirstAppend

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- First deterministic insertion from an arbitrary reached world. Empty
storage imposes no restriction on the sentinel's offset or allocation identity,
and publication may replace a live old key. Preparation and the existing first
append establish the native owners; the shared publication proofs retain the
new row and payload. No caller origin or empty key table is assumed. -/
theorem first_success_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object base : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (sentinel : Compiler.ZigAir.Memory.Address) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (custody : Caller.GraphCustody allocator normalized [] world.memory)
    (publication : Publication.Input allocator source key normalized world)
    (live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩)
    (unique : OwnedKeys.Unique world.memory.effects.keys)
    (admitted : Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (header : readItems world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base)
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container [] input key normalized
        ((key.eval meaning world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (true, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ())
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    let value := (key.eval meaning world.graph.read).getD 0
    let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ installed appended after finalOwner,
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      append runtimeSafety allocate allocator container [] input key normalized value preparationOwnership
        (preparedFrame object copied operands installed) growth = (.ok true, appended) ∧
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true [] world growth =
        ((.ok (some .success), Storage.publishedOwnership), after) ∧
      Valid (memory after) ∧
      (memory after).memory.heap.lookup container = some finalOwner ∧ finalOwner.type = Owner.viewType runtimeSafety ∧
      finalOwner.writable = true ∧
      Memory.Vector allocator (memory after).heap middle.memory.nextId [row] ∧
      Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ 5 (memory after) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ 1, .scalar (.int false 64 5)) ∧
      DescriptorRelation.Prefix (memory after).memory middle.memory.nextId [row] ∧
      (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨container, 0⟩) id =
        .ok ((Storage.representativeProgram.run [row] id).map (DescriptorRelation.values id.toNat))) ∧
      Memory.GraphResident allocator (memory after).heap [row] ∧
      AssemblyItem.Owned allocator object (memory after) ∧
      AssemblyClone.NativeFields.Represents (memory after).memory ⟨object, 0⟩ copied ∧
      (∀ slice, AssemblyClone.Physical.payload copied = some slice → AssemblyItemDeinit.Owned allocator slice (memory after)) ∧
      (∀ payload, copied.verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
      Memory.SliceValid allocator (memory after).heap normalized ∧
      OwnedKeys.Live allocator ⟨(memory after).effects.keys, (memory after).heap⟩ ∧
      OwnedKeys.Unique (memory after).effects.keys ∧
      (memory after).effects.keys = OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, 0⟩ ∧
      (memory after).effects.allocator = (match world.memory.effects.keys key with
        | none => probeEffects
        | some old => if key.arguments.isEmpty then probeEffects else
            ops.arguments.free (OwnedKeys.slice key old) { Publication.forget (memory appended) with effects := probeEffects }) ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + 160) ∧
      (∀ id cell, world.memory.memory.heap.lookup id = some cell → id ≠ container →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).memory.heap.lookup id = some cell) ∧
      ((input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues →
        BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) [row] (memory after)) ∧
      OwnedKeys.Apart (memory after).effects.keys (fun id => operands.items ≠ [] ∧ id = operands.address) ∧
      cell input key normalized value Storage.publishedOwnership after = row ∧
      ((input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues →
        ∀ logical ∈ [row], ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
          native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical) ∧
      (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] →
        (memory after).heap old.address = none ∧ (memory after).memory.heap.lookup old.address = none) ∧
      (∀ id block, world.memory.heap id = some block →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).heap id = some block) := by
  dsimp only
  let value := (key.eval meaning world.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project [] world.graph.table
    (cell input key normalized value owner state) key owner
  obtain ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, sameValues, operandsLive,
      normalizedLive, separate, publicationInput, allLive, unique, keys, nativeFrame, preparedRegistry, registered, sameItem, freshOperands⟩ :=
    prepare_reached ops allocate runtimeSafety allocator container object source itemSource input copied key
      normalized operands remaining world [] value graph duplicated allocated middle
      initial custody.live represented publication live unique admitted duplicateCall createCall cloneCall
  let ready := preparedFrame object copied operands installed
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized [] value graph growth
  change ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe) at duplicateRun
  change ∀ owner, calls.attempt .item owner dupe = (.ok true, made) at createRun
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneRun
  have ownerFrame := (nativeFrame container ownerCell ownerFound).trans ownerFound.symm
  have argumentBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized world.memory initial custody.live).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound world.memory.memory (view normalized) normalized.items represented
    rw [sameValues]; omega
  obtain ⟨appended, finalOwner, appendedRun, appendValid, appendEffects, finalOwnerFound, finalOwnerTyped,
      finalOwnerWritable, backingOwned, vector, finalHeader, _, _, itemOwned, itemReads, payloadOwned,
      argumentsKept, nextId, nextAddress, rows, contents, registryFrame, appendFrame⟩ :=
    first_append_owned allocate runtimeSafety allocator container object base ownerCell sentinel input copied key normalized operands
      value preparationOwnership middle ready allocationEffects installedPost rfl rfl rfl (nativeFrame _ _ ownerFound)
      ownerTyped ownerWritable
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      argumentBound (backing installed assigned).1 (backing installed assigned).2
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety world.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  have originalAppend := appendedRun
  have same : append runtimeSafety allocate allocator container [] input key normalized value preparationOwnership ready growth =
      append runtimeSafety allocate allocator container [] input key normalized value preparationOwnership ready := by
    cases growth with
    | none => rfl
    | some growthCalls =>
      have reached : memory ready = installed := rfl
      have preparedCell : cell input key normalized value preparationOwnership ready =
          ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩ := rfl
      simp only [append, reached]
      rw [Append.Registered.first_same runtimeSafety (growthCallbacks growthCalls) (allocation allocate)
        allocator container base installed ownerCell sentinel (cell input key normalized value preparationOwnership ready)
        { installed.effects with allocator := allocationEffects } installedPost.valid (nativeFrame _ _ ownerFound) ownerTyped ownerWritable
        ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
        ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
        (by simpa only [preparedCell] using argumentBound)
        (by simp only [allocation, (backing installed assigned).1]) (backing installed assigned).2
        ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety world.memory.memory installed.memory container ownerCell
          installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked)]
  have appendedRun := same.trans appendedRun
  have appendedKeys : (memory appended).effects.keys = world.memory.effects.keys :=
    (congrArg Publication.Effects.keys appendEffects).trans keys
  have publicationInput := Publication.Input.frame allocator source key normalized
    ⟨graph preparationOwnership ready, memory ready⟩ ⟨graph publicationOwnership appended, memory appended⟩ publicationInput
    (appendedKeys.trans keys.symm) (argumentsKept allocator)
  have probe : ops.probe key (Publication.forget (memory appended)) = (true, probeEffects) := by
    have reached := response installed assigned
    rw [originalAppend] at reached
    exact reached
  let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
  obtain ⟨after, published, valid, owned, vector, header, rows, queries, normalizedKept, finalKeys, finalId, finalAddress,
      effects, retired, _, frame, preservation, graphPreservation⟩ :=
    publication_rows ops allocate runtimeSafety allocator container installed.memory.nextId 5 finalOwner source itemSource input key normalized
      [] [row] value graph publicationOwnership appended growth probeEffects appendValid finalOwnerFound finalOwnerTyped
      backingOwned vector finalHeader rows (by simp) (argumentsKept allocator normalized normalizedLive) publicationInput probe
  obtain ⟨itemCell, itemFound, _⟩ := installedPost.valid.injected object _ registered
  have itemOlder := (Compiler.ZigAir.Memory.valid_lookup installed.memory object itemCell installedPost.valid.memory itemFound).1
  change ∀ id, id ≠ installed.memory.nextId → (memory appended).heap id = installed.heap id at registryFrame
  change ∀ id, id ≠ container → id ≠ installed.memory.nextId →
    (memory appended).memory.heap.lookup id = installed.memory.heap.lookup id at appendFrame
  have rowResident : Memory.GraphResident allocator (memory appended).heap [row] := by
    intro logical member
    have same := List.mem_singleton.mp member
    subst logical
    exact ⟨(registryFrame object (by omega)).trans registered, argumentsKept allocator operands operandsLive⟩
  have separation := extended_arguments_apart allocator world normalized operands key [] row initial live custody publication.aligned
    (by intro query old found nonempty borrowed; simp at borrowed) rfl rfl freshOperands separate
  have apart : OwnedKeys.Apart (memory appended).effects.keys
      (fun address => ∃ logical ∈ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress) := by
    rw [appendedKeys]
    exact separation.1
  obtain ⟨resident, pointees⟩ := graphPreservation [row] rowResident apart
  have itemFrame := (pointees row (List.mem_singleton_self _)).1
  have ownedItem : AssemblyItem.Owned allocator object (memory after) := by
    obtain ⟨_, native, found, typed, writable, stack⟩ := itemOwned
    exact ⟨⟨copied.item, (resident row (List.mem_singleton_self _)).1⟩,
      native, itemFrame.trans found, typed, writable, stack⟩
  obtain ⟨ownedPayload, payloadReads⟩ := publication_payload allocator key copied (memory appended) (memory after)
    publicationInput.live payloadOwned contents frame
  have finalTable : (memory after).effects.keys = OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, 0⟩ := by
    simpa only [appendedKeys] using finalKeys
  have preserved := preservation
    (fun address => ∃ logical ∈ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress)
    (by intro query old found; rw [congrArg Publication.Effects.keys appendEffects] at found; exact argumentsKept allocator _ (allLive query old found))
    (by rw [congrArg Publication.Effects.keys appendEffects]; exact unique)
    (by
      intro query old found nonempty oldNonempty alias
      rw [appendedKeys] at found
      exact custody.apart query old found oldNonempty ⟨by simpa only [publication.aligned] using nonempty, alias.symm⟩)
    apart separation.2
  have typedItems (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) :
      ∀ logical ∈ [row], ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical := by
    intro logical member
    have same := List.mem_singleton.mp member
    subst logical
    obtain ⟨_, native, found, typed, _⟩ := ownedItem
    refine ⟨native, found, typed, ?_⟩
    exact (itemReads.frame itemFrame).query row native valid.memory found typed rfl rfl
      (by simpa only [sameItem] using domain)
  have accepted (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) :
      BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) [row] (memory after) := by
    apply BorrowedQuery.Native.of_resident allocator _ [row] (memory after) valid resident
    obtain ⟨_, _, backing, found, typed, writable, _⟩ := owned
    intro id opcode
    exact Operation.query (memory after).memory _ installed.memory.nextId 5 backing [row] id opcode valid.memory
      (readHeader_items _ _ _ _ header) found typed writable (by simp) rows
      (fun logical member => (typedItems domain logical member).choose_spec.2.2)
  have installedId := installedPost.written.nextId
  have installedAddress := installedPost.written.nextAddress
  have finalId := finalId.trans nextId
  have finalAddress := finalAddress.trans nextAddress
  change (memory after).memory.nextId = installed.memory.nextId + 1 at finalId
  change (memory after).memory.nextAddress = max installed.memory.nextAddress (base + 160) at finalAddress
  rw [installedId] at owned vector header rows finalId
  rw [installedAddress] at finalAddress
  have ownerApart (old : OwnedKeys.Entry) (found : (memory appended).effects.keys key = some old)
      (nonempty : key.arguments ≠ []) : container ≠ old.address := by
    have stored := (publicationInput.live old found).resolve_left nonempty
    obtain ⟨⟨native, found, typed, _⟩, _⟩ := appendValid.related allocator old.address key.arguments nonempty stored
    exact (memory appended).memory.heap.lookup_ne_of_type_ne container old.address finalOwner native finalOwnerFound found
      (by simp [finalOwnerTyped, typed, Owner.viewType])
  refine ⟨installed, appended, after, finalOwner, assigned, appendedRun, ?_, valid, (frame container ownerApart).2.trans finalOwnerFound,
    finalOwnerTyped, finalOwnerWritable, vector, owned, header, rows, queries, resident, ownedItem,
    itemReads.frame itemFrame, ownedPayload, payloadReads, normalizedKept, preserved.live, preserved.unique, finalTable, ?_,
    finalId, finalAddress, ?_, accepted, ?_,
    prepared_publication_cell ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands [] value graph
      growth installed appended after appendedRun published, typedItems, ?_, ?_⟩
  · change calls.attempt .append preparationOwnership ready = (.ok true, appended) at appendedRun
    change calls.attempt .publish publicationOwnership appended = (.ok true, after) at published
    exact Storage.insert_prepared_success calls start dupe made ready appended after duplicateRun createRun cloneRun appendedRun published
  · simpa only [appendedKeys] using effects
  · intro id cell found ownerApart keyApart
    have kept := nativeFrame id cell found
    have older := (Compiler.ZigAir.Memory.valid_lookup installed.memory id cell installedPost.valid.memory kept).1
    exact (frame id (by simpa only [appendedKeys] using keyApart)).2.trans ((appendFrame id ownerApart (by omega)).trans kept)
  · simpa only [List.mem_singleton, exists_eq_left, row] using preserved.apart
  · intro old found nonempty
    exact retired old (by rw [appendedKeys]; exact found) nonempty
  · intro id block stored keyApart
    have kept := preparedRegistry id block stored
    obtain ⟨cell, found, _⟩ := installedPost.valid.injected id block kept
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ installedPost.valid.memory found).1
    exact (frame id (by simpa only [appendedKeys] using keyApart)).1.trans
      ((registryFrame id (by omega)).trans kept)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
