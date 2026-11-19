/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionSpareSuccess
import Compiler.Extraction.InternerNativeGraphInsertion
import Compiler.Extraction.InternerUnrelocatedPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Successful spare publication is identified solely by reached capacity and
actual preparation/probe observations. The installation exists by preparation
soundness; no native preservation or final graph is part of this predicate. -/
def SparePublished (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner : Nat) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (world : World (Publication.Effects σ)) : Prop :=
  (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues ∧
  SparePublication ops allocate safety allocator owner meaning input key normalized true world

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native

/-- Reached native graph facts and custody suffice for successful insertion
into spare storage. Derive the extended graph, old/new item data and exact key
relation through the actual preparation, publication and native caller adapter.
The allocator, owner, row count, payload and effects are arbitrary. -/
theorem Facts.spare_success (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (allocator owner lifetime capacity object : Nat)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (facts : Facts safety allocator owner ⟨lifetime, 0⟩ capacity world rows)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory address input)
    (custody : Caller.GraphCustody allocator normalized rows world.memory)
    (aligned : key.arguments = normalized.items) (privateSource : Caller.SourcePrivate source world.memory.effects.keys)
    (admitted : Admitted ops.arguments) (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (spare : rows.length < capacity) (room : rows.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append safety allocate allocator owner rows input key normalized
        ((key.eval meaning world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (true, probeEffects))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    let row : Storage.Cell := ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning input key normalized true growth world
    actual.1 = .ok (Storage.idFor rows) ∧
      Facts safety allocator owner ⟨lifetime, 0⟩ capacity actual.2 (rows ++ [row]) ∧
      actual.2.memory.effects.keys = OwnedKeys.store world.memory.effects.keys key ⟨normalized.address, Storage.idFor rows⟩ ∧
      (∀ id native, world.memory.memory.heap.lookup id = some native → id ≠ owner → id ≠ lifetime →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        actual.2.memory.memory.heap.lookup id = some native) ∧
      (∀ id block, world.memory.heap id = some block → id ≠ lifetime →
        (∀ old, world.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        actual.2.memory.heap id = some block) := by
  have positive : capacity ≠ 0 := by omega
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  obtain ⟨backingOwned, vector, descriptors⟩ := facts.storage positive
  have fields := Append.readHeader_parts world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) _ _ facts.header
  obtain ⟨installed, appended, after, finalOwner, _, _, executed, valid, finalOwnerFound, finalOwnerTyped,
      finalOwnerWritable, vector, owned, header, finalRows, resident, _, itemReads, _, _, _, live, unique,
      apart, _, keys, _, _, _, _, native, registry, items, candidate, _⟩ :=
    spare_success_reached ops allocate safety allocator owner lifetime capacity object ownerCell source address meaning
      input copied key normalized operands remaining world rows duplicated allocated middle facts.valid represented custody
      (custody.publication source key aligned privateSource facts.live) facts.live facts.unique admitted ownerFound ownerTyped ownerWritable
      backingOwned fields.1 fields.2 vector descriptors facts.resident facts.apart facts.items domain spare room
      duplicateCall createCall cloneCall probeEffects response growth
  have completed := facts.insert_published ops allocate growth source address meaning input key normalized after
    ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩ lifetime capacity
    executed candidate valid ⟨finalOwner, finalOwnerFound, finalOwnerTyped, finalOwnerWritable⟩ header
    (by omega) owned vector finalRows resident items live unique apart keys (by intro _; exact itemReads .data) native
  dsimp only
  refine ⟨congrArg Prod.fst completed.1, completed.2, ?_, ?_, ?_⟩
  · simpa only [completed.1] using keys
  · rw [completed.1]
    exact native
  · rw [completed.1]
    exact registry

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
