/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionTransferredPreparation
import Compiler.Extraction.InternerInsertionNativeProjection
import Compiler.Extraction.InternerInsertionGrowingOwnership
import Compiler.Extraction.AssemblyItemGraphFrame
import Compiler.Extraction.RepresentativeBorrowedQuery
import Compiler.Extraction.InternerCallerCustody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Actual transferred insertion at an arbitrary reached world. Native preparation
and nonempty relocation derive queries, ownership and frames without a caller
origin, duplicate allocation or publication callback. -/
theorem transferred_growing_success_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice)
    (world : World (Publication.Effects σ)) (cells : List Storage.Cell)
    (allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (custody : Caller.Custody allocator normalized world.memory)
    (live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩)
    (unique : OwnedKeys.Unique world.memory.effects.keys)
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
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item world.memory = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base)

    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let value := (key.eval meaning world.graph.read).getD 0
    let row : Storage.Cell := ⟨copied.item, value, object, normalized.items, key.sequence, normalized.address⟩
    ∃ installed after finalOwner,
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      append runtimeSafety allocate allocator container cells input key normalized value transferredPreparation
        (transferredFrame object copied installed) (some growth) = (.ok true, after) ∧
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized false cells world (some growth) =
        ((.ok (some .success), Storage.transferredOwnership), after) ∧
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
      (memory after).effects.keys = world.memory.effects.keys ∧
      (∃ oldCell, world.memory.memory.heap.lookup oldLifetime = some oldCell ∧
        (memory after).effects.allocator = freeBacking allocator oldCell.base (oldCapacity * 32) 8 allocationEffects) ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      (∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ container → id ≠ oldLifetime →
        (memory after).memory.heap.lookup id = some native) ∧
      (∀ id block, world.memory.heap id = some block → id ≠ oldLifetime → (memory after).heap id = some block) ∧
      (∀ logical ∈ cells ++ [row], ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical) ∧
      cell input key normalized value Storage.transferredOwnership after = row := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  let value := (key.eval meaning world.graph.read).getD 0
  let row : Storage.Cell := ⟨copied.item, value, object, normalized.items, key.sequence, normalized.address⟩
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
    (cell input key normalized value owner state) key owner
  obtain ⟨installed, createRun, cloneRun, installedPost, assigned, normalizedLive, allLive, unique, keys,
      nativeFrame, registryFrame, objectRegistered, sameItem⟩ :=
    prepare_transferred_reached ops allocate runtimeSafety allocator container object source itemSource input copied key
      normalized world cells value graph allocated middle initial represented custody.live live unique createCall cloneCall
  let ready := transferredFrame object copied installed
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, none⟩
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph (some growth)
  change ∀ owner, calls.attempt .item owner start = (.ok true, made) at createRun
  change ∀ owner, calls.attempt .clone owner made = (.ok true, ready) at cloneRun
  obtain ⟨_, _, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have ownerFrame := (nativeFrame container ownerCell ownerFound).trans ownerFound.symm
  have preparedVector : Memory.Vector allocator installed.heap oldLifetime cells := registryFrame _ _ registered
  have argumentBound : normalized.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized world.memory initial custody.live).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound world.memory.memory (view normalized) normalized.items represented
    omega
  have preparedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity installed :=
    ⟨rfl, ⟨cells, preparedVector⟩, backingCell, nativeFrame _ _ backingFound, backingTyped, backingWritable, backingPersistent⟩
  obtain ⟨oldCell, after, finalOwner, oldFound, appendedRun, valid, effects, finalOwnerFound, finalOwnerTyped,
      finalOwnerWritable, owned, vector, header, _, _, itemOwned, itemReads, payloadOwned,
      argumentsKept, contents, nextId, nextAddress, oldDead, nativeDead, extended, appendRegistry, appendFrame, _⟩ :=
    growing_append_owned allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity object base context returnAddress
      ownerCell input copied key normalized normalized cells value transferredPreparation middle ready allocationEffects installedPost rfl rfl rfl
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
  have finalKeys : (memory after).effects.keys = world.memory.effects.keys := (congrArg Publication.Effects.keys effects).trans keys
  have appendResident (logical : Storage.Cell) (live : Memory.Resident allocator installed.heap logical) :
      Memory.Resident allocator (memory after).heap logical := by
    have apart : logical.itemAddress ≠ oldLifetime := by
      intro same
      have stored := live.1
      rw [same, preparedVector] at stored
      cases stored
    have fresh : logical.itemAddress ≠ installed.memory.nextId := by
      intro same
      have stored := live.1
      rw [same, installedPost.valid.injected.fresh installedPost.valid.memory] at stored
      cases stored
    exact ⟨(appendRegistry logical.itemAddress apart fresh).trans live.1, argumentsKept allocator _ live.2⟩
  have residentExtended : Memory.GraphResident allocator (memory after).heap (cells ++ [row]) := by
    intro logical member
    apply appendResident
    rcases List.mem_append.mp member with old | new
    · refine ⟨registryFrame _ _ (resident logical old).1, ?_⟩
      rcases (resident logical old).2 with empty | stored
      · exact Or.inl empty
      · exact Or.inr (registryFrame _ _ stored)
    · have same := List.mem_singleton.mp new
      subst logical
      exact ⟨objectRegistered, normalizedLive⟩
  have apartExtended : OwnedKeys.Apart (memory after).effects.keys
      (fun address => ∃ logical ∈ cells ++ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress) := by
    rw [finalKeys]
    intro query old found nonempty kept
    obtain ⟨logical, member, nonemptyArguments, aliases⟩ := kept
    rcases List.mem_append.mp member with previous | added
    · exact keyApart query old found nonempty ⟨logical, previous, nonemptyArguments, aliases⟩
    · have same := List.mem_singleton.mp added
      subst logical
      exact custody.apart query old found nonempty ⟨nonemptyArguments, aliases⟩
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
      have same := (appendFrame logical.itemAddress backingApart (freshApart _ _ found) ownerApart).trans ((nativeFrame _ _ found).trans found.symm)
      exact ⟨native, same.trans found, typed, AssemblyItem.Query.frame world.memory.memory (memory after).memory logical same query⟩
    · have same := List.mem_singleton.mp added
      subst logical
      obtain ⟨_, native, found, typed, _⟩ := itemOwned
      refine ⟨native, found, typed, ?_⟩
      apply AssemblyItem.Query.of_members (memory after).memory row native valid.memory found typed
      · simpa only [row, sameItem] using domain
      · simpa only [row, (AssemblyClone.NativeFields.key_fields copied).1] using itemReads .kind
      · simpa only [row, (AssemblyClone.NativeFields.key_fields copied).2.1] using itemReads .instruction
  have enough : cells.length + 1 ≤ capacity := by
    have width : Append.nextLength cells.length < Compiler.ZigAir.Memory.addressLimit := by
      simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega
    exact selected ▸ Capacity.grow_sufficient _ width
  have accepted : BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) (cells ++ [row]) (memory after) := by
    apply BorrowedQuery.Native.of_resident allocator _ _ (memory after) valid residentExtended
    obtain ⟨_, _, backing, found, typed, writable, _⟩ := owned
    intro id opcode
    exact Operation.query (memory after).memory _ installed.memory.nextId capacity backing (cells ++ [row]) id opcode valid.memory
      (readHeader_items _ _ _ _ (by simpa only [List.length_append, List.length_singleton] using header)) found typed writable (by simp only [List.length_append, List.length_singleton]; omega) extended
      (fun logical member => (typedItems logical member).choose_spec.2.2)
  have installedId : (memory ready).memory.nextId = middle.memory.nextId := installedPost.written.nextId
  refine ⟨installed, after, finalOwner, assigned, appendedRun, ?_, valid, finalOwnerFound, finalOwnerTyped, finalOwnerWritable,
    ?_, ?_, ?_, ?_, residentExtended, itemOwned, itemReads, payloadOwned, contents, argumentsKept allocator _ normalizedLive,
    ?_, ?_, apartExtended, accepted, finalKeys, ?_, ?_, ?_, oldDead, nativeDead, ?_, ?_, typedItems, ?_⟩
  · change calls.attempt .append transferredPreparation ready = (.ok true, after) at appendedRun
    have executed := Storage.insert_transferred_success calls start made ready after createRun cloneRun appendedRun
    simpa only [execution, room, decide_true] using executed
  · simpa only [installedId] using vector
  · simpa only [installedId] using owned
  · simpa only [installedId] using header
  · simpa only [installedId] using extended
  · intro query old found
    rw [congrArg Publication.Effects.keys effects] at found
    exact argumentsKept allocator _ (allLive query old found)
  · rw [congrArg Publication.Effects.keys effects]; exact unique
  · have same : oldCell = backingCell := Option.some.inj (oldFound.symm.trans (nativeFrame _ _ backingFound))
    refine ⟨backingCell, backingFound, ?_⟩
    simpa only [same] using congrArg Publication.Effects.allocator effects
  · exact nextId.trans (congrArg (· + 1) installedPost.written.nextId)
  · exact nextAddress.trans (congrArg (fun address => max address (base + capacity * 32)) installedPost.written.nextAddress)
  · intro id native found ownerApart backingApart
    exact (appendFrame id backingApart (freshApart _ _ found) ownerApart).trans (nativeFrame _ _ found)
  · intro id block stored backingApart
    have fresh : id ≠ installed.memory.nextId := by
      obtain ⟨native, found, _⟩ := installedPost.valid.injected id block (registryFrame _ _ stored)
      have older := (Compiler.ZigAir.Memory.valid_lookup _ _ native installedPost.valid.memory found).1
      omega
    exact (appendRegistry id backingApart fresh).trans (registryFrame _ _ stored)
  · have projected := append_cell runtimeSafety allocate allocator container cells input key normalized value transferredPreparation
      transferredOwnership ready (some growth)
    rw [appendedRun] at projected
    exact projected

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
