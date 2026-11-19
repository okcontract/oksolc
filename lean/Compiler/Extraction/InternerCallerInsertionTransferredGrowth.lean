/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedTransferredGrowth
import Compiler.Extraction.InternerInsertionNativeProjection
import Compiler.Extraction.InternerInsertionGrowingOwnership
import Compiler.Extraction.AssemblyItemGraphFrame
import Compiler.Extraction.RepresentativeBorrowedQuery

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Caller-connected nondeterministic insertion transfers the normalized buffer
into a new representative through actual nonempty relocation. No duplicate or
publication callback is required or executed. Initial native correspondence and
allocator binding remain explicit; reached queries, owners and frames are derived. -/
theorem CallerInput.transferred_growing_success (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (request : Interner.Request) (values : List NodeId) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ)) (cells : List Storage.Cell)
    (allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity before.memory)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (registered : Memory.Vector allocator before.memory.heap oldLifetime cells)
    (rows : DescriptorRelation.Prefix before.memory.memory oldLifetime cells)
    (resident : Memory.GraphResident allocator before.memory.heap cells)
    (keyApart : OwnedKeys.Apart before.memory.effects.keys
      (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress))
    (oldItems : ∀ cell ∈ cells, ∃ native, before.memory.memory.heap.lookup cell.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item before.memory.memory cell)
    (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base)

    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let value := (key.eval meaning taken.world.graph.read).getD 0
    let row : Storage.Cell := ⟨copied.item, value, object, normalized.items, key.sequence, normalized.address⟩
    ∃ installed after finalOwner,
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      append runtimeSafety allocate allocator container cells input key normalized value transferredPreparation
        (transferredFrame object copied installed) (some growth) = (.ok true, after) ∧
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized false cells taken.world (some growth) =
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
      (memory after).effects.keys = before.memory.effects.keys ∧
      (∃ oldCell, before.memory.memory.heap.lookup oldLifetime = some oldCell ∧
        (memory after).effects.allocator = freeBacking allocator oldCell.base (oldCapacity * 32) 8 allocationEffects) ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      (∀ id native, before.memory.memory.heap.lookup id = some native → id ≠ container → id ≠ oldLifetime →
        (memory after).memory.heap.lookup id = some native) ∧
      (∀ id block, before.memory.heap id = some block → id ≠ oldLifetime → (memory after).heap id = some block) ∧
      (∀ logical ∈ cells ++ [row], ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical) ∧
      cell input key normalized value Storage.transferredOwnership after = row := by
  dsimp only
  obtain ⟨root, vector, backingCell, backingFound, backingTyped, backingWritable, persistent⟩ := backingOwned
  obtain ⟨oldRows, oldVector⟩ := vector
  have reachedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity taken.world.memory :=
    ⟨root, ⟨oldRows, entry.origin.registry _ _ oldVector⟩, backingCell,
      entry.origin.memory _ _ backingFound, backingTyped, backingWritable, persistent⟩
  have ownerFrame := entry.native_frame container ownerCell ownerFound
  have backingFrame := entry.native_frame oldLifetime backingCell backingFound
  have residentTaken : Memory.GraphResident allocator taken.world.memory.heap cells := by
    intro logical member
    refine ⟨entry.origin.registry _ _ (resident logical member).1, ?_⟩
    rcases (resident logical member).2 with empty | stored
    · exact Or.inl empty
    · exact Or.inr (entry.origin.registry _ _ stored)
  have itemsTaken : ∀ logical ∈ cells, ∃ native,
      taken.world.memory.memory.heap.lookup logical.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item taken.world.memory.memory logical := by
    intro logical member
    obtain ⟨native, found, typed, queried⟩ := oldItems logical member
    exact ⟨native, entry.origin.memory _ _ found, typed,
      AssemblyItem.Query.frame _ _ logical (entry.native_frame _ _ found) queried⟩
  obtain ⟨installed, after, finalOwner, assigned, appended, executed, valid, finalOwnerFound, finalOwnerTyped,
    finalOwnerWritable, vector, owned, finalHeader, descriptors, resident, itemOwned, itemReads, payload, contents,
    normalizedLive, live, unique, apart, accepted, keys, effects, nextId, nextAddress, oldDead, nativeDead,
    native, registry, items, candidate⟩ :=
    transferred_growing_success_reached ops allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity
      object base context returnAddress ownerCell source itemSource meaning input copied key normalized taken.world cells allocated middle
      entry.origin.held.1.1 entry.item entry.custody entry.live entry.unique
      (entry.origin.memory _ _ ownerFound) ownerTyped ownerWritable reachedOwned
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      (entry.origin.registry _ _ registered) (DescriptorRelation.frame _ _ oldLifetime cells rows backingFrame)
      residentTaken (entry.keys.symm ▸ keyApart) itemsTaken domain oldNonempty full selected size room
      createCall cloneCall allocationEffects backing
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory taken.world.memory.memory container ownerCell
        entry.origin.held.1.1.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  refine ⟨installed, after, finalOwner, assigned, appended, executed, valid, finalOwnerFound, finalOwnerTyped,
    finalOwnerWritable, vector, owned, finalHeader, descriptors, resident, itemOwned, itemReads, payload, contents,
    normalizedLive, live, unique, apart, accepted, keys.trans entry.keys, ?_, nextId, nextAddress, oldDead, nativeDead,
    ?_, ?_, items, candidate⟩
  · obtain ⟨cell, found, observed⟩ := effects
    have same := Option.some.inj (found.symm.trans (entry.origin.memory _ _ backingFound))
    exact ⟨backingCell, backingFound, same ▸ observed⟩
  · exact fun id cell found ownerApart backingApart => native id cell (entry.origin.memory _ _ found) ownerApart backingApart
  · exact fun id block stored backingApart => registry id block (entry.origin.registry _ _ stored) backingApart

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
