/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionGrowthAllocationFailure
import Compiler.Extraction.InternerNativeGraphFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Empty borrowed arguments require no allocation; constructor inputs carry
no verbatim owner. Derive their actual duplicate/create/clone observations and
feed the existing general growth-OOM and cleanup theorem. -/
theorem CallerInput.growing_empty_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (safety : Bool)
    (allocator owner oldBacking oldCapacity capacity context returnAddress base : Nat)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (request : Interner.Request) (values : List NodeId) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (constructed : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (rows : List Storage.Cell)
    (entry : CallerInput allocator source address request values input key constructed taken normalized lookup)
    (facts : NativeGraph.Facts safety allocator owner ⟨oldBacking, 0⟩ oldCapacity constructed rows)
    (admitted : Admitted ops.arguments) (empty : normalized.items = []) (noPayload : input.verbatim = none)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength rows.length)
    (selected : capacity = Capacity.grow (Append.nextLength rows.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : rows.length < 2 ^ 32 - 1)
    (createEffects allocationEffects : σ)
    (createResponse : ops.create AssemblyItem.Creation.layout (Publication.forget taken.world.memory) = (some base, createEffects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits taken.world.memory.memory AssemblyItem.Creation.layout base)
    (allocation : ∀ installed,
      AssemblyClone.NativeFields.install input taken.world.memory.memory.nextId
        (AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory).2 = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader constructed.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let created := (AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory).2
    ∃ after,
      execution ops allocate safety allocator owner source address meaning input key normalized true rows taken.world (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) ∧
      Valid (memory after) ∧ (memory after).memory.nextId = created.memory.nextId ∧
      (memory after).memory.nextAddress = created.memory.nextAddress ∧
      (memory after).effects.keys = constructed.memory.effects.keys ∧
      (∀ id native, constructed.memory.memory.heap.lookup id = some native → (memory after).memory.heap.lookup id = some native) ∧
      (∀ id block, constructed.memory.heap id = some block → (memory after).heap id = some block) ∧
      (memory after).heap taken.world.memory.memory.nextId = none ∧
      (memory after).memory.heap.lookup taken.world.memory.memory.nextId = none := by
  dsimp only
  let operands : ArgumentSlice := ⟨taken.world.memory.memory.nextId, []⟩
  let remaining : Handle := ⟨view normalized, normalized.items, none⟩
  let created := (AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory).2
  have duplicated : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ taken.world.memory = (.ok (operands, remaining), taken.world.memory) := by
    simp only [takeOwned, empty]
    rw [Duplication.run_empty _ _ _ _ _ _ (by simp only [view, empty, List.length_nil])]
    simp only [operands, remaining, empty]
  have createdRun : AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory =
      (.ok taken.world.memory.memory.nextId, created) := by
    have response : observe ops.create AssemblyItem.Creation.layout taken.world.memory =
        (some base, { taken.world.memory.effects with allocator := createEffects }) := by
      simp only [observe, createResponse]
    have complete := AssemblyItem.Creation.create_from_response (observe ops.create) allocator base input.item
      taken.world.memory _ entry.origin.held.1.1 response fits
    have result : (AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory).1 =
        .ok taken.world.memory.memory.nextId := congrArg Prod.fst complete.1
    exact Prod.ext result rfl
  have cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input created = (.ok input, created) := by
    simp only [AssemblyClone.Physical.run, AssemblyClone.CloneCode.run, noPayload]
  obtain ⟨ownerCell, found, typed, _⟩ := facts.ownerLive
  obtain ⟨after, ran, valid, nextId, nextAddress, keys, _, _, _, _, _, native, registry, released⟩ :=
    entry.growing_allocation_oom ops allocate freeBacking safety allocator owner oldBacking oldCapacity capacity
      taken.world.memory.memory.nextId context returnAddress ownerCell source address meaning request values input input key
      normalized operands lookup remaining constructed taken rows taken.world.memory created created admitted facts.valid
      found typed (facts.storage oldNonempty).1 (readHeader_items _ _ _ _ facts.header) (readHeader_capacity _ _ _ _ facts.header) facts.live
      oldNonempty full selected size room duplicated createdRun cloned allocationEffects allocation unlocked
  exact ⟨after, ran, valid, nextId, nextAddress, keys, native, registry, released _ (Or.inl rfl)⟩


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
