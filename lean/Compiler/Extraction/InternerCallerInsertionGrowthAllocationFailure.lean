/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionPreparation
import Compiler.Extraction.InternerInsertionReachedGrowthAllocationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Ordinary backing-allocation OOM from the caller's actual preparation. No
row is appended or published. The same execution derives all cleanup owners,
retains every old allocation (including parent borrows and container storage),
and releases the clone and both nonempty argument owners in source order. -/
theorem CallerInput.growing_allocation_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object context returnAddress : Nat)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (request : Interner.Request) (values : List NodeId)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (lookup remaining : Handle) (before : World (Publication.Effects σ))
    (taken : OwnedCall.State (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (admitted : Admitted ops.arguments) (initial : Valid before.memory)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (backingOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity before.memory)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (oldKeys : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ taken.world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells taken.world (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) ∧
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
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  dsimp only
  obtain ⟨root, ⟨oldRows, oldVector⟩, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have reachedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity taken.world.memory :=
    ⟨root, ⟨oldRows, entry.origin.registry _ _ oldVector⟩, backingCell,
      entry.origin.memory _ _ backingFound, backingTyped, backingWritable, backingPersistent⟩
  have ownerFrame := entry.native_frame container ownerCell ownerFound
  obtain ⟨after, executed, valid, retained, _, nextId, nextAddress, objectCleared, valueCleared, marker, released⟩ :=
    growing_allocation_oom_reached ops allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity
      object context returnAddress ownerCell source itemSource meaning input copied key normalized operands remaining taken.world cells
      duplicated allocated middle entry.origin.held.1.1 entry.origin.held.2.1 entry.item admitted
      (entry.origin.memory _ _ ownerFound) ownerTyped reachedOwned
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      oldNonempty full selected size room duplicateCall createCall cloneCall allocationEffects response
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory taken.world.memory.memory container ownerCell
        entry.origin.held.1.1.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  have finalFrame (id : Nat) (native : Compiler.ZigAir.Memory.Allocation)
      (found : before.memory.memory.heap.lookup id = some native) :=
    retained.allocations id native (entry.origin.memory id native found)
      (fun _ => (entry.origin.freshNative id native found).symm)
  have registeredFrame (id : Nat) (block : Memory.Allocation) (stored : before.memory.heap id = some block) :
      (memory after).heap id = some block := by
    obtain ⟨native, found, _⟩ := initial.injected id block stored
    exact (finalFrame id native found).2.trans (entry.origin.registry id block stored)
  have keysUnchanged := retained.keys.trans entry.keys
  refine ⟨after, executed, valid, nextId, nextAddress, keysUnchanged, ?_, ?_, objectCleared, valueCleared, marker,
    (fun id native found => (finalFrame id native found).1), registeredFrame, released⟩
  · intro query old found
    rcases oldKeys query old (keysUnchanged ▸ found) with empty | live
    · exact Or.inl empty
    · exact Or.inr (registeredFrame _ _ live)
  · rw [keysUnchanged, ← entry.keys]; exact entry.unique

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
