/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedGrowingSuccess
import Compiler.Extraction.InternerNativeGraphInsertion
import Compiler.Extraction.InternerRelocatedPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Successful relocation additionally admits the new item's tag for future
native queries. OOM destroys that item and needs no such retained-item premise. -/
def RelocatedPublished (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (growth : Option (Growth.Registered.Callbacks σ)) (world : World (Publication.Effects σ)) : Prop :=
  (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues ∧
  RelocatedPublication ops allocate safety allocator owner meaning input key normalized growth true world

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native

/-- Derive the native graph after actual nonempty relocation from reached graph
facts and custody. Both spare and relocated insertion use the same final graph
construction; old backing retirement and new allocation counters remain exact. -/
theorem Facts.growing_success (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (safety : Bool)
    (allocator owner lifetime oldCapacity capacity object base context returnAddress : Nat)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (facts : Facts safety allocator owner ⟨lifetime, 0⟩ oldCapacity world rows)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory address input)
    (custody : Caller.GraphCustody allocator normalized rows world.memory)
    (aligned : key.arguments = normalized.items) (privateSource : Caller.SourcePrivate source world.memory.effects.keys)
    (admitted : Admitted ops.arguments) (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength rows.length)
    (selected : capacity = Capacity.grow (Append.nextLength rows.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : rows.length < 2 ^ 32 - 1)
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
      ops.probe key (Publication.forget (memory (append safety allocate allocator owner rows input key normalized
        ((key.eval meaning world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)
        (some ⟨.noRemap context returnAddress, freeBacking⟩)).2)) = (true, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    let row : Storage.Cell := ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning input key normalized true
      (some ⟨.noRemap context returnAddress, freeBacking⟩) world
    actual.1 = .ok (Storage.idFor rows) ∧
      Facts safety allocator owner ⟨middle.memory.nextId, 0⟩ capacity actual.2 (rows ++ [row]) ∧
      actual.2.memory.effects.keys = OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, Storage.idFor rows⟩ ∧
      actual.2.memory.heap lifetime = none ∧ actual.2.memory.memory.heap.lookup lifetime = none ∧
      actual.2.memory.memory.nextId = middle.memory.nextId + 1 ∧
      actual.2.memory.memory.nextAddress = max middle.memory.nextAddress (base + capacity * 32) ∧
      (∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ owner → id ≠ lifetime →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        actual.2.memory.memory.heap.lookup id = some native) ∧
      (∀ id block, world.memory.heap id = some block → id ≠ lifetime →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        actual.2.memory.heap id = some block) := by
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  obtain ⟨backingOwned, vector, descriptors⟩ := facts.storage oldNonempty
  have fields := Append.readHeader_parts world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) _ _ facts.header
  obtain ⟨installed, appended, after, finalOwner, _, _, executed, valid, finalOwnerFound, finalOwnerTyped,
      finalOwnerWritable, vector, owned, header, finalRows, resident, _, itemReads, _, _, _, live, unique,
      apart, _, keys, _, nextId, nextAddress, oldDead, nativeDead, _, native, registry, items, candidate, _⟩ :=
    growing_success_reached ops allocate freeBacking safety allocator owner lifetime oldCapacity capacity object base context returnAddress
      ownerCell source address meaning input copied key normalized operands remaining world rows duplicated allocated middle
      facts.valid represented custody (custody.publication source key aligned privateSource facts.live)
      facts.live facts.unique admitted ownerFound ownerTyped ownerWritable backingOwned fields.1 fields.2 vector descriptors
      facts.resident facts.apart facts.items domain oldNonempty full selected size room duplicateCall createCall cloneCall
      allocationEffects backing probeEffects response unlocked
  have width : Append.nextLength rows.length < Compiler.ZigAir.Memory.addressLimit := by
    simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]
    omega
  have enough : rows.length + 1 ≤ capacity := selected ▸ Capacity.grow_sufficient _ width
  have completed := facts.insert_published ops allocate (some ⟨.noRemap context returnAddress, freeBacking⟩)
    source address meaning input key normalized after
    ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩
    middle.memory.nextId capacity executed candidate valid
    ⟨finalOwner, finalOwnerFound, finalOwnerTyped, finalOwnerWritable⟩ header enough owned vector finalRows
    resident items live unique apart keys (by intro _; exact itemReads .data) native
  dsimp only
  refine ⟨congrArg Prod.fst completed.1, completed.2, ?_⟩
  rw [completed.1]
  exact ⟨keys, oldDead, nativeDead, nextId, nextAddress, native, registry⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
