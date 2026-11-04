/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedGrowingRollback
import Compiler.Extraction.AssemblyItemGraphFrame
import Compiler.Extraction.RepresentativeBorrowedQuery

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Caller-connected publication OOM after successful nonempty relocation.
The actual preparation and rollback derive survival of every old pointee outside
the owner/backing writes, the resident graph, all native queries and global key
ownership. The normalized outer release is part of the same execution. -/
theorem CallerInput.growing_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (request : Interner.Request) (values : List NodeId) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (lookup remaining : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (admitted : Admitted ops.arguments)
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
    (initial : Valid before.memory)
    (oldKeys : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ taken.world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base)
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container cells input key normalized
        ((key.eval meaning taken.world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)
        (some ⟨.noRemap context returnAddress, freeBacking⟩)).2)) =
        (false, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells taken.world (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap middle.memory.nextId cells ∧
      Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ capacity (memory after) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix (memory after).memory middle.memory.nextId cells ∧
      Memory.GraphResident allocator (memory after).heap cells ∧
      (memory after).effects.keys = before.memory.effects.keys ∧
      OwnedKeys.Live allocator ⟨(memory after).effects.keys, (memory after).heap⟩ ∧
      OwnedKeys.Unique (memory after).effects.keys ∧
      OwnedKeys.Apart (memory after).effects.keys
        (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress) ∧
      BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) cells (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      (∀ id native, before.memory.memory.heap.lookup id = some native → id ≠ container → id ≠ oldLifetime →
        (memory after).memory.heap.lookup id = some native) ∧
      (∀ id block, before.memory.heap id = some block → id ≠ container → id ≠ oldLifetime →
        (memory after).heap id = some block) ∧
      (∀ logical ∈ cells, ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical) ∧
      (∃ finalOwner, (memory after).memory.heap.lookup container = some finalOwner ∧ ownerCell.SameShape finalOwner) ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  dsimp only
  obtain ⟨root, ⟨oldRows, oldVector⟩, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have reachedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity taken.world.memory :=
    ⟨root, ⟨oldRows, entry.origin.registry _ _ oldVector⟩, backingCell,
      entry.origin.memory _ _ backingFound, backingTyped, backingWritable, backingPersistent⟩
  have ownerFrame := entry.native_frame container ownerCell ownerFound
  obtain ⟨after, executed, valid, vector, owned, finalHeader, finalRows, finalKeys, finalId, finalAddress,
      oldDead, nativeDead, objectCleared, valueCleared, invalidated, retained, finalOwner, destroyed⟩ :=
    growing_publication_oom_reached ops allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity
      object base context returnAddress ownerCell source itemSource meaning input copied key normalized operands remaining taken.world cells
      duplicated allocated middle entry.origin.held.1.1 entry.origin.held.2.1 entry.item entry.publication admitted
      (entry.origin.memory _ _ ownerFound) ownerTyped ownerWritable reachedOwned
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      (entry.origin.registry _ _ registered)
      (DescriptorRelation.frame _ _ oldLifetime cells rows (entry.native_frame _ _ backingFound))
      oldNonempty full selected size room duplicateCall createCall cloneCall allocationEffects backing probeEffects response
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory taken.world.memory.memory container ownerCell
        entry.origin.held.1.1.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  have finalFrame (id : Nat) (native : Compiler.ZigAir.Memory.Allocation)
      (found : before.memory.memory.heap.lookup id = some native) (ownerApart : id ≠ container) (oldApart : id ≠ oldLifetime) :=
    retained id native (entry.origin.memory id native found) ownerApart oldApart
      (fun _ => (entry.origin.freshNative id native found).symm)
  have registeredFrame (id : Nat) (block : Memory.Allocation) (stored : before.memory.heap id = some block)
      (ownerApart : id ≠ container) (oldApart : id ≠ oldLifetime) : (memory after).heap id = some block := by
    obtain ⟨native, found, _⟩ := initial.injected id block stored
    exact (finalFrame id native found ownerApart oldApart).2.trans (entry.origin.registry id block stored)
  have argumentsKept (slice : ArgumentSlice) (live : Memory.SliceValid allocator before.memory.heap slice) :
      Memory.SliceValid allocator (memory after).heap slice := by
    rcases live with empty | stored
    · exact Or.inl empty
    · by_cases empty : slice.items = []
      · exact Or.inl empty
      · obtain ⟨⟨native, found, typed, _⟩, _⟩ := initial.related allocator slice.address slice.items empty stored
        have ownerApart := before.memory.memory.heap.lookup_ne_of_type_ne slice.address container native ownerCell found ownerFound
          (by simp [typed, ownerTyped, Owner.viewType])
        have oldApart : slice.address ≠ oldLifetime := by intro same; rw [same, registered] at stored; cases stored
        exact Or.inr (registeredFrame _ _ stored ownerApart oldApart)
  have itemApart (logical : Storage.Cell) (member : logical ∈ cells) (native : Compiler.ZigAir.Memory.Allocation)
      (found : before.memory.memory.heap.lookup logical.itemAddress = some native) (typed : native.type = AssemblyItem.viewType) :
      logical.itemAddress ≠ container ∧ logical.itemAddress ≠ oldLifetime := by
    refine ⟨before.memory.memory.heap.lookup_ne_of_type_ne _ _ native ownerCell found ownerFound
      (by simp [typed, ownerTyped, Owner.viewType, AssemblyItem.viewType]), ?_⟩
    intro same
    have stored := (resident logical member).1
    rw [same, registered] at stored
    cases stored
  have finalResident : Memory.GraphResident allocator (memory after).heap cells := by
    intro logical member
    obtain ⟨native, found, typed, _⟩ := oldItems logical member
    have apart := itemApart logical member native found typed
    exact ⟨registeredFrame _ _ (resident logical member).1 apart.1 apart.2, argumentsKept _ (resident logical member).2⟩
  have typedItems : ∀ logical ∈ cells, ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical := by
    intro logical member
    obtain ⟨native, found, typed, query⟩ := oldItems logical member
    have apart := itemApart logical member native found typed
    have kept := (finalFrame _ _ found apart.1 apart.2).1
    exact ⟨native, kept, typed, AssemblyItem.Query.frame before.memory.memory (memory after).memory logical (kept.trans found.symm) query⟩
  have accepted : BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) cells (memory after) := by
    apply BorrowedQuery.Native.of_resident allocator _ _ (memory after) valid finalResident
    obtain ⟨_, _, backing, found, typed, writable, _⟩ := owned
    have width : Append.nextLength cells.length < Compiler.ZigAir.Memory.addressLimit := by
      simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega
    have enough : Append.nextLength cells.length ≤ capacity := selected ▸ Capacity.grow_sufficient _ width
    intro id opcode
    exact Operation.query (memory after).memory _ middle.memory.nextId capacity backing cells id opcode valid.memory
      (readHeader_items _ _ _ _ finalHeader) found typed writable
      (by simp only [Append.nextLength] at enough; omega) finalRows (fun logical member => (typedItems logical member).choose_spec.2.2)
  have keysUnchanged : (memory after).effects.keys = before.memory.effects.keys := finalKeys.trans entry.keys
  refine ⟨after, executed, valid, vector, owned, finalHeader, finalRows, finalResident, keysUnchanged, ?_, ?_, ?_, accepted,
    finalId, finalAddress, oldDead, nativeDead, objectCleared, valueCleared, invalidated,
    (fun id native found ownerApart oldApart => (finalFrame id native found ownerApart oldApart).1), registeredFrame, typedItems,
    finalOwner, destroyed⟩
  · intro query old found
    exact argumentsKept _ (oldKeys query old (keysUnchanged ▸ found))
  · rw [keysUnchanged, ← entry.keys]; exact entry.unique
  · rw [keysUnchanged]; exact keyApart

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
