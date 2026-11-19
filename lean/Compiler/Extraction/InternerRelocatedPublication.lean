/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionPreparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Actual source observations for nonempty no-remap relocation followed by a
publication probe. Success and OOM share preparation and backing allocation;
the probe result selects publication or rollback. Installation existence and
all preservation conclusions are derived by the consuming proofs. -/
def RelocatedPublication (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (growth : Option (Growth.Registered.Callbacks σ)) (accepted : Bool) (world : World (Publication.Effects σ)) : Prop :=
  ∃ oldCapacity capacity : Nat,
    readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)) ∧
    oldCapacity ≠ 0 ∧ oldCapacity < Append.nextLength (world.graph.representatives.getD []).length ∧
    capacity = Capacity.grow (Append.nextLength (world.graph.representatives.getD []).length) ∧
    capacity * 32 < Compiler.ZigAir.Memory.addressLimit ∧
    ∃ context returnAddress freeBacking, growth = some ⟨.noRemap context returnAddress, freeBacking⟩ ∧
    ∃ operands remaining duplicated object allocated copied middle base allocationEffects probeEffects,
      takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
        ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated) ∧
      AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated) ∧
      AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle) ∧
      (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        allocate allocator (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
          Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base) ∧
      (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        ops.probe key (Publication.forget (memory (append safety allocate allocator owner
          (world.graph.representatives.getD []) input key normalized ((key.eval meaning world.graph.read).getD 0)
          preparationOwnership (preparedFrame object copied operands installed)
          (some ⟨.noRemap context returnAddress, freeBacking⟩)).2)) = (accepted, probeEffects)) ∧
      Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
