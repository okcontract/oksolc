/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedFirstSuccess
import Compiler.Extraction.InternerNativeGraphInsertion
import Compiler.Extraction.InternerUnrelocatedPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Actual observations selecting first publication. Capacity zero selects
empty storage through the reached graph invariant; no sentinel shape, empty
key table, callback identity or final native graph is assumed. -/
def FirstPublished (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (world : World (Publication.Effects σ)) : Prop :=
  (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues ∧
  FirstPublication ops allocate safety allocator owner meaning input key normalized true world

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native

/-- First successful insertion derives the graph from reached empty storage
with an arbitrary sentinel. Both capacity adapters use the same physical
execution and graph reconstruction. Existing keys may be replaced; the native
frame excludes only the owner and the actually retired key allocation. -/
theorem Facts.first_success (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner object base : Nat) (sentinel : Compiler.ZigAir.Memory.Address)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ))
    (facts : Facts safety allocator owner sentinel 0 world [])
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory address input)
    (custody : Caller.GraphCustody allocator normalized [] world.memory)
    (aligned : key.arguments = normalized.items) (privateSource : Caller.SourcePrivate source world.memory.effects.keys)
    (admitted : Admitted ops.arguments) (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base)
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append safety allocate allocator owner [] input key normalized
        ((key.eval meaning world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (true, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ())
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    let row : Storage.Cell := ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning input key normalized true growth world
    actual.1 = .ok 0 ∧
      Facts safety allocator owner ⟨middle.memory.nextId, 0⟩ 5 actual.2 [row] ∧
      actual.2.memory.effects.keys = OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, 0⟩ ∧
      actual.2.memory.memory.nextId = middle.memory.nextId + 1 ∧
      actual.2.memory.memory.nextAddress = max middle.memory.nextAddress (base + 160) ∧
      (∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ owner →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        actual.2.memory.memory.heap.lookup id = some native) ∧
      (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] →
        actual.2.memory.heap old.address = none ∧ actual.2.memory.memory.heap.lookup old.address = none) ∧
      (∀ id block, world.memory.heap id = some block →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        actual.2.memory.heap id = some block) := by
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  have fields := Append.readHeader_parts world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) _ _ facts.header
  obtain ⟨installed, appended, after, finalOwner, _, _, executed, valid, finalOwnerFound,
      finalOwnerTyped, finalOwnerWritable, vector, owned, header, descriptors, _, resident, _, itemReads,
      _, _, _, live, unique, keys, _, nextId, nextAddress, native, _, apart, candidate, items, retired, registry⟩ :=
    first_success_reached ops allocate safety allocator owner object base ownerCell sentinel source address
      meaning input copied key normalized operands remaining world duplicated allocated middle
      facts.valid represented custody (custody.publication source key aligned privateSource facts.live)
      facts.live facts.unique admitted ownerFound ownerTyped ownerWritable fields.1 fields.2
      duplicateCall createCall cloneCall allocationEffects backing probeEffects response unlocked growth
  have completed := facts.insert_published ops allocate growth source address meaning input key normalized after
    ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩
    middle.memory.nextId 5 executed candidate valid ⟨finalOwner, finalOwnerFound, finalOwnerTyped, finalOwnerWritable⟩
    header (by decide) owned vector descriptors resident (items domain) live unique
    (by simpa only [List.nil_append, List.mem_singleton, exists_eq_left] using apart) keys
    (by intro _; exact itemReads .data) (fun id cell found ownerApart _ => native id cell found ownerApart)
  dsimp only
  refine ⟨congrArg Prod.fst completed.1, completed.2, ?_⟩
  rw [completed.1]
  exact ⟨keys, nextId, nextAddress, native, retired, registry⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
