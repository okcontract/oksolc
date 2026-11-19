/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionPreparation
import Compiler.Extraction.InternerCallerGraphCustody
import Compiler.Extraction.InternerInsertionPublicationSuccess
import Compiler.Extraction.InternerInsertionNativeProjection
import Compiler.Extraction.InternerInsertionGrowingOwnership
import Compiler.Extraction.AssemblyItemGraphFrame
import Compiler.Extraction.RepresentativeBorrowedQuery

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Actual deterministic insertion through nonempty relocation at the reached
world. Preparation, backing replacement and publication derive the new native
row and preserve old pointees. The allocator response and refusing-remap identity
are explicit source observations; no rebased caller origin or final frame is assumed. -/
theorem growing_success_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (remaining : Handle)
    (world : World (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (custody : Caller.GraphCustody allocator normalized cells world.memory)
    (publication : Publication.Input allocator source key normalized world)
    (live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩)
    (unique : OwnedKeys.Unique world.memory.effects.keys)
    (admitted : Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity world.memory)
    (header : readItems world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (registered : Memory.Vector allocator world.memory.heap oldLifetime cells)
    (rows : DescriptorRelation.Prefix world.memory.memory oldLifetime cells)
    (resident : Memory.GraphResident allocator world.memory.heap cells)
    (keyApart : OwnedKeys.Apart world.memory.effects.keys
      (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress))
    (oldItems : ∀ cell ∈ cells, ∃ native, world.memory.memory.heap.lookup cell.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item world.memory.memory cell)
    (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base)
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container cells input key normalized
        ((key.eval meaning world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)
        (some ⟨.noRemap context returnAddress, freeBacking⟩)).2)) =
        (true, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let value := (key.eval meaning world.graph.read).getD 0
    let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ installed appended after finalOwner,
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      append runtimeSafety allocate allocator container cells input key normalized value preparationOwnership
        (preparedFrame object copied operands installed) (some growth) = (.ok true, appended) ∧
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells world (some growth) =
        ((.ok (some .success), Storage.publishedOwnership), after) ∧
      Valid (memory after) ∧ (memory after).memory.heap.lookup container = some finalOwner ∧
      finalOwner.type = Owner.viewType runtimeSafety ∧ finalOwner.writable = true ∧
      Memory.Vector allocator (memory after).heap middle.memory.nextId (cells ++ [row]) ∧
      Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ capacity (memory after) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix (memory after).memory middle.memory.nextId (cells ++ [row]) ∧
      Memory.GraphResident allocator (memory after).heap (cells ++ [row]) ∧
      AssemblyItem.Owned allocator object (memory after) ∧
      AssemblyClone.NativeFields.Represents (memory after).memory ⟨object, 0⟩ copied ∧
      (∀ slice, AssemblyClone.Physical.payload copied = some slice → AssemblyItemDeinit.Owned allocator slice (memory after)) ∧
      (∀ payload, copied.verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
      Memory.SliceValid allocator (memory after).heap normalized ∧
      OwnedKeys.Live allocator ⟨(memory after).effects.keys, (memory after).heap⟩ ∧
      OwnedKeys.Unique (memory after).effects.keys ∧
      OwnedKeys.Apart (memory after).effects.keys
        (fun address => ∃ cell ∈ cells ++ [row], cell.arguments ≠ [] ∧ address = cell.argumentsAddress) ∧
      BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) (cells ++ [row]) (memory after) ∧
      (memory after).effects.keys = OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ ∧
      (memory after).effects.allocator = (match world.memory.effects.keys key with
        | none => probeEffects
        | some old => if key.arguments.isEmpty then probeEffects else
            ops.arguments.free (OwnedKeys.slice key old) { Publication.forget (memory appended) with effects := probeEffects }) ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] →
        (memory after).heap old.address = none ∧ (memory after).memory.heap.lookup old.address = none) ∧
      (∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ container → id ≠ oldLifetime →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).memory.heap.lookup id = some native) ∧
      (∀ id block, world.memory.heap id = some block → id ≠ oldLifetime →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).heap id = some block) ∧
      (∀ logical ∈ cells ++ [row], ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical) ∧
      cell input key normalized value Storage.publishedOwnership after = row ∧
      operands.address = world.memory.memory.nextId := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  let value := (key.eval meaning world.graph.read).getD 0
  let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
    (cell input key normalized value owner state) key owner
  obtain ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, sameValues, operandsLive,
      normalizedLive, separate, publicationInput, allLive, unique, keys, nativeFrame, registryFrame, objectRegistered, sameItem, freshOperands⟩ :=
    prepare_reached ops allocate runtimeSafety allocator container object source itemSource input copied key
      normalized operands remaining world cells value graph duplicated allocated middle
      initial custody.live represented publication live unique admitted duplicateCall createCall cloneCall
  let ready := preparedFrame object copied operands installed
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph (some growth)
  change ∀ owner, calls.attempt .arguments owner start = (.ok true, dupe) at duplicateRun
  change ∀ owner, calls.attempt .item owner dupe = (.ok true, made) at createRun
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneRun
  obtain ⟨_, _, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have ownerFrame := (nativeFrame container ownerCell ownerFound).trans ownerFound.symm
  have preparedVector : Memory.Vector allocator installed.heap oldLifetime cells := registryFrame _ _ registered
  have argumentBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized world.memory initial custody.live).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound world.memory.memory (view normalized) normalized.items represented
    rw [sameValues]; omega
  have preparedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity installed :=
    ⟨rfl, ⟨cells, preparedVector⟩, backingCell, nativeFrame _ _ backingFound, backingTyped, backingWritable, backingPersistent⟩
  obtain ⟨oldCell, appended, finalOwner, _, appendedRun, appendValid, appendEffects, finalOwnerFound, finalOwnerTyped,
      finalOwnerWritable, backingOwned, vector, finalHeader, _, _, itemOwned, itemReads, payloadOwned,
      argumentsKept, contents, nextId, nextAddress, oldDead, nativeDead, extended, appendRegistry, appendFrame, _⟩ :=
    growing_append_owned allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity object base context returnAddress
      ownerCell input copied key normalized operands cells value preparationOwnership middle ready allocationEffects installedPost rfl rfl rfl
      (nativeFrame _ _ ownerFound) ownerTyped ownerWritable preparedOwned
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      preparedVector (DescriptorRelation.frame _ _ oldLifetime cells rows ((nativeFrame _ _ backingFound).trans backingFound.symm))
      oldNonempty full selected size room argumentBound (backing installed assigned).1 (backing installed assigned).2
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety world.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  have freshApart (id : Nat) (native : Compiler.ZigAir.Memory.Allocation)
      (found : world.memory.memory.heap.lookup id = some native) : id ≠ installed.memory.nextId := by
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ native installedPost.valid.memory (nativeFrame _ _ found)).1
    omega
  have appendedKeys : (memory appended).effects.keys = world.memory.effects.keys := (congrArg Publication.Effects.keys appendEffects).trans keys
  have publicationInput := Publication.Input.frame allocator source key normalized
    ⟨graph preparationOwnership ready, installed⟩ ⟨graph publicationOwnership appended, memory appended⟩ publicationInput
    (appendedKeys.trans keys.symm) (argumentsKept allocator)
  have probe : ops.probe key (Publication.forget (memory appended)) = (true, probeEffects) := by
    have reached := response installed assigned
    rw [appendedRun] at reached
    exact reached
  have preparedResident : Memory.GraphResident allocator installed.heap cells := by
    intro logical member
    refine ⟨registryFrame _ _ (resident logical member).1, ?_⟩
    rcases (resident logical member).2 with empty | stored
    · exact Or.inl empty
    · exact Or.inr (registryFrame _ _ stored)
  have appendResident (logical : Storage.Cell) (owned : Memory.Resident allocator installed.heap logical) :
      Memory.Resident allocator (memory appended).heap logical := by
    have apart : logical.itemAddress ≠ oldLifetime := by
      intro same
      have stored := owned.1
      rw [same, preparedVector] at stored
      cases stored
    have fresh : logical.itemAddress ≠ installed.memory.nextId := by
      intro same
      have stored := owned.1
      rw [same, installedPost.valid.injected.fresh installedPost.valid.memory] at stored
      cases stored
    exact ⟨(appendRegistry logical.itemAddress apart fresh).trans owned.1, argumentsKept allocator _ owned.2⟩
  have residentExtended : Memory.GraphResident allocator (memory appended).heap (cells ++ [row]) := by
    intro logical member
    rcases List.mem_append.mp member with old | new
    · exact appendResident logical (preparedResident logical old)
    · have same := List.mem_singleton.mp new
      subst logical
      exact appendResident row ⟨objectRegistered, operandsLive⟩
  have separation := extended_arguments_apart allocator world normalized operands key cells row initial live custody publication.aligned
    keyApart rfl rfl freshOperands separate
  have apartExtended : OwnedKeys.Apart (memory appended).effects.keys
      (fun address => ∃ logical ∈ cells ++ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress) := by
    rw [appendedKeys]
    exact separation.1
  have enough : cells.length + 1 ≤ capacity := by
    have width : Append.nextLength cells.length < Compiler.ZigAir.Memory.addressLimit := by
      simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega
    exact selected ▸ Capacity.grow_sufficient _ width
  obtain ⟨after, published, valid, owned, vector, header, finalRows, _, normalizedKept, finalKeys, finalId, finalAddress,
      effects, retired, deadKept, publicationFrame, preservation, graphPreservation⟩ :=
    publication_rows ops allocate runtimeSafety allocator container installed.memory.nextId capacity finalOwner source itemSource input key normalized
      cells (cells ++ [row]) value graph publicationOwnership appended (some growth) probeEffects appendValid finalOwnerFound finalOwnerTyped
      backingOwned vector (by simpa only [List.length_append, List.length_singleton] using finalHeader) extended
      (by simp only [List.length_append, List.length_singleton]; omega)
      (argumentsKept allocator normalized normalizedLive) publicationInput probe
  have preserved := preservation (fun address => ∃ logical ∈ cells ++ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress)
    (by intro query old found; rw [congrArg Publication.Effects.keys appendEffects] at found; exact argumentsKept allocator _ (allLive query old found))
    (by rw [congrArg Publication.Effects.keys appendEffects]; exact unique)
    (by
      intro query old found nonempty oldNonempty alias
      rw [appendedKeys] at found
      exact custody.apart query old found oldNonempty ⟨by simpa only [publication.aligned] using nonempty, alias.symm⟩)
    apartExtended separation.2
  obtain ⟨finalResident, pointeeFrames⟩ := graphPreservation (cells ++ [row]) residentExtended apartExtended
  have newMember : row ∈ cells ++ [row] := List.mem_append.mpr (Or.inr (List.mem_singleton_self _))
  have itemFrame := (pointeeFrames row newMember).1
  have ownedItem : AssemblyItem.Owned allocator object (memory after) := by
    obtain ⟨_, native, found, typed, writable, stack⟩ := itemOwned
    exact ⟨⟨copied.item, (finalResident row newMember).1⟩, native, itemFrame.trans found, typed, writable, stack⟩
  obtain ⟨ownedPayload, payloadReads⟩ := publication_payload allocator key copied (memory appended) (memory after)
    publicationInput.live payloadOwned contents publicationFrame
  have typedItems : ∀ logical ∈ cells ++ [row], ∃ native,
      (memory after).memory.heap.lookup logical.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical := by
    intro logical member
    rcases List.mem_append.mp member with previous | added
    · obtain ⟨native, found, typed, query⟩ := oldItems logical previous
      have ownerApart := installed.memory.heap.lookup_ne_of_type_ne logical.itemAddress container native ownerCell
        (nativeFrame _ _ found) (nativeFrame _ _ ownerFound) (by simp [typed, ownerTyped, AssemblyItem.viewType, Owner.viewType])
      have backingApart := installed.memory.heap.lookup_ne_of_type_ne logical.itemAddress oldLifetime native backingCell
        (nativeFrame _ _ found) (nativeFrame _ _ backingFound) (by simp [typed, backingTyped, AssemblyItem.viewType, Backing.type])
      have same := (pointeeFrames logical member).1.trans
        ((appendFrame logical.itemAddress backingApart (freshApart _ _ found) ownerApart).trans ((nativeFrame _ _ found).trans found.symm))
      exact ⟨native, same.trans found, typed, AssemblyItem.Query.frame world.memory.memory (memory after).memory logical same query⟩
    · have same := List.mem_singleton.mp added
      subst logical
      obtain ⟨_, native, found, typed, _⟩ := ownedItem
      refine ⟨native, found, typed, ?_⟩
      exact (itemReads.frame itemFrame).query row native valid.memory found typed rfl rfl
        (by simpa only [sameItem] using domain)
  have finalItems (logical : Storage.Cell) (member : logical ∈ cells ++ [row]) : Operation.Item (memory after).memory logical := by
    obtain ⟨_, _, _, represented⟩ := typedItems logical member
    exact represented
  have accepted : BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) (cells ++ [row]) (memory after) := by
    apply BorrowedQuery.Native.of_resident allocator _ _ (memory after) valid finalResident
    obtain ⟨_, _, backing, found, typed, writable, _⟩ := owned
    intro id opcode
    exact Operation.query (memory after).memory _ installed.memory.nextId capacity backing (cells ++ [row]) id opcode valid.memory
      (readHeader_items _ _ _ _ header) found typed writable (by simp only [List.length_append, List.length_singleton]; omega) finalRows finalItems
  have ownerApart (old : OwnedKeys.Entry) (found : (memory appended).effects.keys key = some old) (nonempty : key.arguments ≠ []) : container ≠ old.address := by
    have stored := (publicationInput.live old found).resolve_left nonempty
    obtain ⟨⟨native, found, typed, _⟩, _⟩ := appendValid.related allocator old.address key.arguments nonempty stored
    exact (memory appended).memory.heap.lookup_ne_of_type_ne container old.address finalOwner native finalOwnerFound found
      (by simp [finalOwnerTyped, typed, Owner.viewType])
  have finalRegistry (id : Nat) (block : Memory.Allocation) (stored : world.memory.heap id = some block)
      (backingApart : id ≠ oldLifetime)
      (keyApart : ∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) :
      (memory after).heap id = some block := by
    exact (publicationFrame id (by simpa only [appendedKeys] using keyApart)).1.trans
      ((appendRegistry id backingApart (by
        change id ≠ installed.memory.nextId
        obtain ⟨native, found, _⟩ := installedPost.valid.injected id block (registryFrame _ _ stored)
        have older := (Compiler.ZigAir.Memory.valid_lookup _ _ native installedPost.valid.memory found).1
        omega)).trans (registryFrame _ _ stored))
  refine ⟨installed, appended, after, finalOwner, assigned, appendedRun, ?_, valid, (publicationFrame container ownerApart).2.trans finalOwnerFound,
    finalOwnerTyped, finalOwnerWritable, ?_, ?_, ?_, ?_, finalResident, ownedItem, itemReads.frame itemFrame,
    ownedPayload, payloadReads, normalizedKept, preserved.live, preserved.unique, preserved.apart, accepted, ?_, ?_,
    (finalId.trans nextId).trans (congrArg (· + 1) installedPost.written.nextId),
    (finalAddress.trans nextAddress).trans (congrArg (fun address => max address (base + capacity * 32)) installedPost.written.nextAddress),
    (deadKept oldLifetime ⟨oldDead, nativeDead⟩).1, (deadKept oldLifetime ⟨oldDead, nativeDead⟩).2, ?_, ?_, finalRegistry, typedItems,
    prepared_publication_cell ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands cells value graph
      (some growth) installed appended after appendedRun published, freshOperands⟩
  · change calls.attempt .append preparationOwnership ready = (.ok true, appended) at appendedRun
    change calls.attempt .publish publicationOwnership appended = (.ok true, after) at published
    have executed := Storage.insert_prepared_success calls start dupe made ready appended after duplicateRun createRun cloneRun appendedRun published
    simpa only [execution, room, decide_true] using executed
  · simpa only [installedPost.written.nextId] using vector
  · simpa only [installedPost.written.nextId] using owned
  · simpa only [List.length_append, List.length_singleton, installedPost.written.nextId] using header
  · simpa only [installedPost.written.nextId] using finalRows
  · simpa only [appendedKeys] using finalKeys
  · simpa only [appendedKeys] using effects
  · intro old found nonempty
    exact retired old (by rw [appendedKeys]; exact found) nonempty
  · intro id native found ownerApart backingApart keyApart
    exact (publicationFrame id (by simpa only [appendedKeys] using keyApart)).2.trans
      ((appendFrame id backingApart (freshApart _ _ found) ownerApart).trans (nativeFrame _ _ found))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
