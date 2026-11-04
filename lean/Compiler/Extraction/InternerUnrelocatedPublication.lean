/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparedRollback

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Source observations for first allocation and publication. Installation
existence and native preservation are derived by the consuming proof. -/
def FirstPublication (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (accepted : Bool) (world : World (Publication.Effects σ)) : Prop :=
  readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)) ∧
  ∃ operands remaining duplicated object allocated copied middle base allocationEffects probeEffects,
    takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated) ∧
    AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated) ∧
    AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle) ∧
    (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base) ∧
    (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append safety allocate allocator owner []
        input key normalized ((key.eval meaning world.graph.read).getD 0)
        preparationOwnership (preparedFrame object copied operands installed)).2)) = (accepted, probeEffects)) ∧
    Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()

/-- Source observations for spare append and publication. Success and refusal
share the reached preparation and differ only in the actual probe response. -/
def SparePublication (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (accepted : Bool) (world : World (Publication.Effects σ)) : Prop :=
  ∃ capacity : Nat,
    readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)) ∧
    (world.graph.representatives.getD []).length < capacity ∧
    ∃ operands remaining duplicated object allocated copied middle probeEffects,
      takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
        ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated) ∧
      AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated) ∧
      AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle) ∧
      ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        ops.probe key (Publication.forget (memory (append safety allocate allocator owner
          (world.graph.representatives.getD []) input key normalized ((key.eval meaning world.graph.read).getD 0)
          preparationOwnership (preparedFrame object copied operands installed)).2)) = (accepted, probeEffects)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
