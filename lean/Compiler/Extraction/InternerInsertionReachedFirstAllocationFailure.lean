/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendFailureModes
import Compiler.Extraction.RepresentativeFirstAllocationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- First backing-allocation OOM uses the same reached preparation and cleanup
as nonempty growth. The empty sentinel and optional growth callbacks are
arbitrary; neither heap changes before the prepared owners are released. -/
theorem first_allocation_oom_reached_at (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety deterministic : Bool) (allocator container object : Nat)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (sentinel : Compiler.ZigAir.Memory.Address)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (admitted : deterministic = true → Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (header : readItems world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (duplicateCall : PreparationInput ops allocator normalized operands remaining deterministic world.memory duplicated)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator 160 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ())
    (growth : Option (Growth.Registered.Callbacks σ)) :
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized deterministic [] world growth =
        ((.ok (some .allocationFailure), appendFailureState deterministic), after) ∧
      Valid (memory after) ∧ PrivateFrame normalized world.memory (memory after) ∧
      Consumed normalized (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧
      (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = false ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  apply append_oom_reached_at ops allocate runtimeSafety deterministic allocator container object source itemSource meaning input copied key
    normalized operands remaining world [] duplicated allocated middle initial live represented admitted (by decide)
    duplicateCall createCall cloneCall allocationEffects growth
  intro installed installedPost assigned frame
  have ownerFrame := (frame container ownerCell ownerFound).1.trans ownerFound.symm
  have allocatedResponse : allocation allocate allocator 160 8 installed.effects =
      (none, { installed.effects with allocator := allocationEffects }) := by simp only [allocation, response installed assigned]
  have refused (calls : Growth.Registered.Callbacks (Publication.Effects σ)) :=
    Append.Registered.first_refused runtimeSafety calls (allocation allocate) allocator container installed ownerCell sentinel
      ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩
      { installed.effects with allocator := allocationEffects } installedPost.valid (frame _ _ ownerFound).1 ownerTyped
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      allocatedResponse
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety world.memory.memory installed.memory container ownerCell
        installedPost.valid.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  let ready := preparedFrameAt deterministic object copied operands installed
  have selectedArguments : arguments normalized (preparationOwnershipAt deterministic) ready = some operands :=
    prepared_arguments ops allocator object normalized operands remaining deterministic world.memory duplicated installed copied duplicateCall
  cases growth with
  | none =>
    change (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized []
      ((key.eval meaning world.graph.read).getD 0) (fun _ _ => world.graph)).attempt .append (preparationOwnershipAt deterministic) ready = _
    rw [append_callback ops allocate runtimeSafety allocator container source itemSource input key normalized []
      ((key.eval meaning world.graph.read).getD 0) (fun _ _ => world.graph) (preparationOwnershipAt deterministic) ready object copied operands rfl rfl selectedArguments]
    rw [show memory ready = installed from rfl, (refused ⟨.unsupported, fun _ _ _ _ effects => effects⟩).1]
    rfl
  | some growth =>
    change (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized []
      ((key.eval meaning world.graph.read).getD 0) (fun _ _ => world.graph) (some growth)).attempt .append (preparationOwnershipAt deterministic) ready = _
    rw [append_growth_callback ops allocate runtimeSafety allocator container source itemSource input key normalized []
      ((key.eval meaning world.graph.read).getD 0) (fun _ _ => world.graph) (preparationOwnershipAt deterministic) ready growth object copied operands rfl rfl selectedArguments]
    rw [show memory ready = installed from rfl, (refused (growthCallbacks growth)).2]
    rfl


/-- The original deterministic interface specializes the shared ownership-mode proof. -/
theorem first_allocation_oom_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (allocator container object : Nat)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (sentinel : Compiler.ZigAir.Memory.Address)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (live : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (admitted : Admitted ops.arguments)
    (ownerFound : world.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (header : readItems world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator 160 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ())
    (growth : Option (Growth.Registered.Callbacks σ)) :
    ∃ after,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true [] world growth =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) ∧
      Valid (memory after) ∧ PrivateFrame normalized world.memory (memory after) ∧
      Consumed normalized (memory after) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧
      (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = false ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) :=
  first_allocation_oom_reached_at ops allocate runtimeSafety true allocator container object ownerCell sentinel source itemSource meaning
    input copied key normalized operands remaining world duplicated allocated middle initial live represented (fun _ => admitted) ownerFound ownerTyped
    header capacityRead duplicateCall createCall cloneCall allocationEffects response unlocked growth

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
