/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedRollback
import Compiler.Extraction.InternerInsertionGrowingOwnership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Publication refusal after nonempty no-remap relocation at the actual reached
world. Preparation and rollback derive the final backing, old row contents,
retained pointees and destruction of the new owners. No normalization origin,
final graph invariant, logical word coherence or callback-preservation premise
is needed. The allocation history includes the retained new backing. -/
theorem growing_publication_oom_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (remaining : Handle)
    (world : World (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (publication : Publication.Input allocator source key normalized world)
    (admitted : Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity world.memory)
    (header : readItems world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (registered : Memory.Vector allocator world.memory.heap oldLifetime cells)
    (rows : DescriptorRelation.Prefix world.memory.memory oldLifetime cells)
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
        (false, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells world (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership), after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap middle.memory.nextId cells ∧
      Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ capacity (memory after) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix (memory after).memory middle.memory.nextId cells ∧
      (memory after).effects.keys = world.memory.effects.keys ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      (∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ container → id ≠ oldLifetime →
        (normalized.items ≠ [] → id ≠ normalized.address) →
        (memory after).memory.heap.lookup id = some native ∧ (memory after).heap id = world.memory.heap id) ∧
      (∃ finalOwner, (memory after).memory.heap.lookup container = some finalOwner ∧ ownerCell.SameShape finalOwner) ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  let value := (key.eval meaning world.graph.read).getD 0
  let graph : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells world.graph.table
    (cell input key normalized value owner state) key owner
  refine prepare_publication_oom ops allocate runtimeSafety allocator container object source itemSource meaning
    input copied key normalized operands remaining world cells duplicated allocated middle (some growth)
    initial live represented publication admitted room duplicateCall createCall cloneCall _ ?_
  dsimp only
  intro installed installedPost assigned sameValues operandsLive normalizedLive separate frame keys publicationInput
  have nativeFrame := fun id cell found => (frame id cell found).1
  have registryFrame (id : Nat) (block : Memory.Allocation) (stored : world.memory.heap id = some block) : installed.heap id = some block := by
    obtain ⟨native, found, _⟩ := initial.injected id block stored
    exact (frame id native found).2.trans stored
  let ready := preparedFrame object copied operands installed
  obtain ⟨_, _, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have ownerFrame := (nativeFrame container ownerCell ownerFound).trans ownerFound.symm
  have preparedVector : Memory.Vector allocator installed.heap oldLifetime cells := registryFrame _ _ registered
  have argumentBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized world.memory initial live).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound world.memory.memory (view normalized) normalized.items represented
    rw [sameValues]; omega
  have preparedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity installed :=
    ⟨rfl, ⟨cells, preparedVector⟩, backingCell, nativeFrame _ _ backingFound, backingTyped, backingWritable, backingPersistent⟩
  obtain ⟨appended, failed, popped, after, appendedRun, publicationRun, _, rolled, cleaned, _, valid, vector,
      finalHeader, _, _, finalId, finalAddress, objectCleared, valueCleared, invalidated, owned, finalRows,
      oldDead, nativeDead, finalKeys, cleanupFrame, finalOwner, destroyed⟩ :=
    growing_publication_oom_cleanup ops allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity object base context returnAddress
      ownerCell input copied key normalized operands cells value preparationOwnership middle ready source itemSource graph installedPost rfl rfl rfl
      (nativeFrame _ _ ownerFound) ownerTyped ownerWritable preparedOwned
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      preparedVector (DescriptorRelation.frame _ _ oldLifetime cells rows ((nativeFrame _ _ backingFound).trans backingFound.symm))
      oldNonempty full selected size room argumentBound allocationEffects (backing installed assigned).1 (backing installed assigned).2
      operandsLive normalizedLive separate publicationInput probeEffects (response installed assigned)
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety world.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  have fresh := preparation_cleanup_apart ops allocator object input copied normalized operands remaining
    world.memory duplicated allocated middle initial live admitted duplicateCall createCall cloneCall
  refine ⟨appended, failed, popped, after, appendedRun, publicationRun, rolled, cleaned, valid, ?_, ?_, ?_, ?_, finalKeys.trans keys,
    finalId.trans (congrArg (· + 1) installedPost.written.nextId),
    finalAddress.trans (congrArg (fun address => max address (base + capacity * 32)) installedPost.written.nextAddress),
    oldDead, nativeDead, objectCleared, valueCleared, invalidated, ?_, finalOwner, destroyed⟩
  · change Memory.Vector allocator (memory after).heap installed.memory.nextId cells at vector
    simpa only [installedPost.written.nextId] using vector
  · change Backing.Release.Owned allocator ⟨installed.memory.nextId, 0⟩ capacity (memory after) at owned
    simpa only [installedPost.written.nextId] using owned
  · change readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨installed.memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) at finalHeader
    simpa only [installedPost.written.nextId] using finalHeader
  · change DescriptorRelation.Prefix (memory after).memory installed.memory.nextId cells at finalRows
    simpa only [installedPost.written.nextId] using finalRows
  · intro id native found ownerApart oldApart normalizedApart
    have newer := (Compiler.ZigAir.Memory.valid_lookup installed.memory id native installedPost.valid.memory (nativeFrame _ _ found)).1
    have apart := fresh id native found
    have kept := cleanupFrame id ownerApart oldApart (by change id ≠ installed.memory.nextId; omega)
      apart.1 apart.2.1 (fun _ => apart.2.2) normalizedApart
    exact ⟨kept.2.trans (nativeFrame _ _ found), kept.1.trans (frame id native found).2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
