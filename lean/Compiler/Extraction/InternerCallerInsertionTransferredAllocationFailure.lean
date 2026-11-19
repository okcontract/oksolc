/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionTransferredPreparation
import Compiler.Extraction.InternerInsertionUnappendedCleanup
import Compiler.Extraction.InternerInsertionReachedGrowthAllocationFailure
import Compiler.Extraction.InternerCallerTransferredPreparationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Ordinary backing-allocation OOM from the caller's actual preparation. No
row is appended or published. The same execution derives all cleanup owners,
retains every old allocation (including parent borrows and container storage),
and releases the clone and the single nonempty argument owner in source order.
The normalized defer was disabled before creation and must not release it again. -/
theorem CallerInput.transferred_growing_allocation_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object context returnAddress : Nat)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (request : Interner.Request) (values : List NodeId)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (lookup : Handle) (before : World (Publication.Effects σ))
    (taken : OwnedCall.State (Publication.Effects σ)) (cells : List Storage.Cell)
    (allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (initial : Valid before.memory)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (backingOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity before.memory)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (oldKeys : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized false cells taken.world (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments]).run transferredPreparation), after) ∧
      Valid (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧
      (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      (memory after).effects.keys = before.memory.effects.keys ∧
      OwnedKeys.Live allocator ⟨(memory after).effects.keys, (memory after).heap⟩ ∧
      OwnedKeys.Unique (memory after).effects.keys ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = false ∧
      (∀ id native, before.memory.memory.heap.lookup id = some native → (memory after).memory.heap.lookup id = some native) ∧
      (∀ id block, before.memory.heap id = some block → (memory after).heap id = some block) ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  dsimp only
  obtain ⟨root, ⟨oldRows, oldVector⟩, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have reachedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity taken.world.memory :=
    ⟨root, ⟨oldRows, entry.origin.registry _ _ oldVector⟩, backingCell,
      entry.origin.memory _ _ backingFound, backingTyped, backingWritable, backingPersistent⟩
  have ownerFrame := entry.native_frame container ownerCell ownerFound
  obtain ⟨after, executed, valid, retained, consumed, nextId, nextAddress, objectCleared, valueCleared, marker, released⟩ :=
    growing_allocation_oom_reached_at ops allocate freeBacking runtimeSafety false allocator container oldLifetime oldCapacity capacity
      object context returnAddress ownerCell source itemSource meaning input copied key normalized normalized lookup taken.world cells
      taken.world.memory allocated middle entry.origin.held.1.1 entry.origin.held.2.1 entry.item (by intro h; contradiction)
      (entry.origin.memory _ _ ownerFound) ownerTyped reachedOwned
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      oldNonempty full selected size room ⟨rfl, rfl⟩ createCall cloneCall allocationEffects response
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory taken.world.memory.memory container ownerCell
        entry.origin.held.1.1.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  have post : TransferredFailure normalized taken.world.memory middle after :=
    ⟨valid, consumed, nextId, nextAddress, retained, objectCleared, valueCleared, marker⟩
  have caller := post.caller entry
  refine ⟨after, executed, caller.valid, caller.nextId, caller.nextAddress, caller.keys, ?_,
    caller.unique, caller.object, caller.value, caller.marker, caller.native, caller.registry, ?_⟩
  · intro query old found
    rcases oldKeys query old (caller.keys ▸ found) with empty | stored
    · exact Or.inl empty
    · obtain ⟨native, found, _⟩ := initial.injected _ _ stored
      exact Or.inr ((retained.allocations _ native (entry.origin.memory _ _ found)
        (fun _ => (entry.origin.freshNative _ _ found).symm)).2.trans (entry.origin.registry _ _ stored))
  · simpa only [or_self] using released

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
