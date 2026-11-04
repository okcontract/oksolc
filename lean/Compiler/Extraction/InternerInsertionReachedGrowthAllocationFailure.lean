/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendFailureModes
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Nonempty no-remap growth OOM at the actual reached world. The source
allocator refusal derives the append outcome, then shared preparation and
cleanup retain old allocations outside the consumed normalized owner.
Neither the caller's original state nor a final native frame is a premise. -/
theorem growing_allocation_oom_reached_at (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety deterministic : Bool)
    (allocator container oldLifetime oldCapacity capacity object context returnAddress : Nat)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key)
    (normalized operands : ArgumentSlice) (remaining : Handle) (world : World (Publication.Effects σ))
    (cells : List Storage.Cell) (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (admitted : deterministic = true → Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (backingOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity world.memory)
    (header : readItems world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : PreparationInput ops allocator normalized operands remaining deterministic world.memory duplicated)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic cells world (some growth) =
        ((.ok (some .allocationFailure), appendFailureState deterministic), after) ∧
      Valid (memory after) ∧ PrivateFrame normalized world.memory (memory after) ∧
      Consumed normalized (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧
      (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = false ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  apply append_oom_reached_at ops allocate runtimeSafety deterministic allocator container object source itemSource meaning input copied key
    normalized operands remaining world cells duplicated allocated middle initial live represented admitted room
    duplicateCall createCall cloneCall allocationEffects (some growth)
  intro installed installedPost assigned frame
  obtain ⟨_, ⟨oldRows, oldVector⟩, backingCell, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have preparedOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity installed :=
    ⟨rfl, ⟨oldRows, (frame _ _ backingFound).2.trans oldVector⟩, backingCell,
      (frame _ _ backingFound).1, backingTyped, backingWritable, backingPersistent⟩
  have ownerFrame := (frame container ownerCell ownerFound).1.trans ownerFound.symm
  have allocatedResponse : allocation allocate allocator (capacity * 32) 8 installed.effects =
      (none, { installed.effects with allocator := allocationEffects }) := by simp only [allocation, response installed assigned]
  have oom := Append.Registered.growing_oom runtimeSafety (allocation allocate) (growthCallbacks growth).release
    allocator container oldLifetime oldCapacity capacity context returnAddress installed _ ownerCell cells
    ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩ installedPost.valid
    (frame _ _ ownerFound).1 ownerTyped preparedOwned oldNonempty full selected size room allocatedResponse
    ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
    ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
    ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety world.memory.memory installed.memory container ownerCell
      installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  change Append.Registered.runWithGrowth (growthCallbacks growth) runtimeSafety (allocation allocate) allocator container cells
    ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩ installed = _ at oom
  let ready := preparedFrameAt deterministic object copied operands installed
  have selectedArguments : arguments normalized (preparationOwnershipAt deterministic) ready = some operands :=
    prepared_arguments ops allocator object normalized operands remaining deterministic world.memory duplicated installed copied duplicateCall
  change (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells
    ((key.eval meaning world.graph.read).getD 0) (fun _ _ => world.graph) (some growth)).attempt .append (preparationOwnershipAt deterministic) ready = _
  rw [append_growth_callback ops allocate runtimeSafety allocator container source itemSource input key normalized cells
    ((key.eval meaning world.graph.read).getD 0) (fun _ _ => world.graph) (preparationOwnershipAt deterministic) ready growth object copied operands rfl rfl selectedArguments]
  rw [show memory ready = installed from rfl, oom]
  rfl


/-- The original deterministic interface specializes the shared ownership-mode proof. -/
theorem growing_allocation_oom_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object context returnAddress : Nat)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key)
    (normalized operands : ArgumentSlice) (remaining : Handle) (world : World (Publication.Effects σ))
    (cells : List Storage.Cell) (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (admitted : Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (backingOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity world.memory)
    (header : readItems world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)))
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells world (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) ∧
      Valid (memory after) ∧ PrivateFrame normalized world.memory (memory after) ∧
      Consumed normalized (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧
      (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = false ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) :=
  growing_allocation_oom_reached_at ops allocate freeBacking runtimeSafety true allocator container oldLifetime oldCapacity capacity object context returnAddress
    ownerCell source itemSource meaning input copied key normalized operands remaining world cells duplicated allocated middle initial live
    represented (fun _ => admitted) ownerFound ownerTyped backingOwned header capacityRead oldNonempty full selected size room duplicateCall createCall
    cloneCall allocationEffects response unlocked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
