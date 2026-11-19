/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursivePublicationTests
import Compiler.Extraction.InternerCallerInsertionGrowingSuccess

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth releaseBacking GraphFacts)

/-- Actual duplicate/create/clone outcomes derive validity of the installed
item before a backing response is admitted. -/
theorem installed_facts (call : Call) (allocate : Backing.Registry.Allocate Nat) (safety : Bool)
    (object : Nat) (rows : List Storage.Cell) (operands : ArgumentSlice)
    (constructed : World (Publication.Effects Nat)) (taken : OwnedCall.State (Publication.Effects Nat))
    (duplicateMemory createMemory cloneMemory : Session (Publication.Effects Nat))
    (entry : CallerInput 7 call.source call.address call.request call.request.arguments call.native call.key
      constructed taken call.normalized call.lookup)
    (duplicated : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
      ⟨view call.normalized, call.normalized.items, none⟩ taken.world.memory =
        (.ok (operands, ⟨view call.normalized, call.normalized.items, none⟩), duplicateMemory))
    (created : AssemblyItem.Creation.create (observe ops.create) 7 call.native.item duplicateMemory = (.ok object, createMemory))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) 7 call.native createMemory = (.ok call.native, cloneMemory)) :
    Valid (call.installed object cloneMemory) ∧
    (call.installed object cloneMemory).memory.nextAddress = cloneMemory.memory.nextAddress := by
  let value := (call.key.eval Insertion.Tests.model taken.world.graph.read).getD 0
  let graph : Storage.State → Native.Frame Nat → Interner.Heap := fun owner state => Interner.InsertionExecution.project
    rows taken.world.graph.table (cell call.native call.key call.normalized value owner state) call.key owner
  obtain ⟨installed, _, _, _, established, assigned, _⟩ :=
    entry.prepare ops allocate safety 7 6 object call.source call.address call.request call.request.arguments
      call.native call.native call.key call.normalized operands call.lookup
      ⟨view call.normalized, call.normalized.items, none⟩ constructed taken rows value graph
      duplicateMemory createMemory cloneMemory (Normalization.Tests.external_admitted _) duplicated created cloned
  have same : call.installed object cloneMemory = installed :=
    congrArg (fun result => result.toOption.getD cloneMemory) assigned
  rw [same]
  exact ⟨established.valid, established.written.nextAddress⟩

/-- Derive the same reached graph and selective frame for an operation or Push
child that relocates nonempty backing and publishes its actual key. -/
theorem growing_native (call : Call) (allocate : Backing.Registry.Allocate Nat) (safety : Bool)
    (oldBacking oldCapacity capacity object base : Nat) (rows : List Storage.Cell) (operands : ArgumentSlice)
    (constructed : World (Publication.Effects Nat)) (taken : OwnedCall.State (Publication.Effects Nat))
    (duplicateMemory createMemory cloneMemory : Session (Publication.Effects Nat))
    (entry : CallerInput 7 call.source call.address call.request call.request.arguments call.native call.key
      constructed taken call.normalized call.lookup)
    (constructedFacts : GraphFacts safety oldBacking oldCapacity constructed rows)
    (takenFacts : GraphFacts safety oldBacking oldCapacity taken.world rows)
    (domain : (call.request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength rows.length)
    (selected : capacity = Capacity.grow (Append.nextLength rows.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : rows.length < 2 ^ 32 - 1)
    (duplicated : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
      ⟨view call.normalized, call.normalized.items, none⟩ taken.world.memory =
        (.ok (operands, ⟨view call.normalized, call.normalized.items, none⟩), duplicateMemory))
    (created : AssemblyItem.Creation.create (observe ops.create) 7 call.native.item duplicateMemory = (.ok object, createMemory))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) 7 call.native createMemory = (.ok call.native, cloneMemory))
    (allocationEffects : Nat)
    (backing : ∀ installed, AssemblyClone.NativeFields.install call.native object cloneMemory = .ok installed →
      allocate 7 (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader constructed.memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok ()) :
    ∃ after,
    Native.insert ops allocate safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true (some growth) taken.world =
        (.ok (Storage.idFor rows), call.publicationWorld rows object operands taken.world after) ∧
    GraphFacts safety cloneMemory.memory.nextId capacity (call.publicationWorld rows object operands taken.world after)
      (rows ++ [call.publicationRow object operands taken.world]) ∧
    (memory after).heap oldBacking = none ∧ (memory after).memory.heap.lookup oldBacking = none ∧
    (memory after).effects.keys = OwnedKeys.store constructed.memory.effects.keys call.key
      ⟨call.normalized.address, Storage.idFor rows⟩ ∧
    (∀ id native, constructed.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ oldBacking →
      (∀ old, constructed.memory.effects.keys call.key = some old → call.key.arguments ≠ [] → id ≠ old.address) →
      (memory after).memory.heap.lookup id = some native) ∧
    (∀ id block, constructed.memory.heap id = some block → id ≠ oldBacking →
      (∀ old, constructed.memory.effects.keys call.key = some old → call.key.arguments ≠ [] → id ≠ old.address) →
      (memory after).heap id = some block) ∧
    (∀ parent, Caller.GraphCustody 7 parent rows constructed.memory →
      Caller.GraphCustody 7 parent (rows ++ [call.publicationRow object operands taken.world]) (memory after)) ∧
    (∀ source values, Good source values constructed → Caller.SourcePrivate source constructed.memory.effects.keys →
      Caller.SourcePrivate source (memory after).effects.keys) ∧
    AssemblyClone.NativeFields.Represents (memory after).memory ⟨object, 0⟩ call.native := by
  obtain ⟨owner, found, typed, writable⟩ := constructedFacts.owner
  let probeEffects := (memory (append safety allocate 7 6 rows call.native call.key call.normalized
    ((call.key.eval Insertion.Tests.model taken.world.graph.read).getD 0) preparationOwnership
    (preparedFrame object call.native operands (call.installed object cloneMemory)) (some growth)).2).effects.allocator * 10 + 8
  obtain ⟨_, _, after, finalOwner, _, _, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header,
      descriptors, resident, _, itemReads, _, _, _, live, unique, apart, accepted, keys, _, _, _, oldDead,
      nativeDead, _, frame, registry, items, _, custody, privateSource, candidate⟩ :=
    entry.growing_success ops allocate releaseBacking safety 7 6 oldBacking oldCapacity capacity object base 17 23 owner
      call.source call.address Insertion.Tests.model call.request call.request.arguments call.native call.native call.key
      call.normalized operands call.lookup ⟨view call.normalized, call.normalized.items, none⟩ constructed taken rows
      duplicateMemory createMemory cloneMemory (Normalization.Tests.external_admitted _) found typed writable
      constructedFacts.owned (readHeader_items _ _ _ _ constructedFacts.header)
      constructedFacts.capacity_read constructedFacts.vector constructedFacts.descriptors constructedFacts.resident
      constructedFacts.apart constructedFacts.items domain oldNonempty full selected size room
      duplicated created cloned allocationEffects backing probeEffects (by
        intro installed assigned
        have same : call.installed object cloneMemory = installed :=
          congrArg (fun result => result.toOption.getD cloneMemory) assigned
        rw [← same]; rfl) unlocked
  have checked := entry.checked_execution ops allocate safety 7 6 call.source call.address
    Insertion.Tests.model call.request call.request.arguments call.native call.key call.normalized call.lookup
    constructed taken true rows (some growth) owner ⟨oldBacking, 0⟩ found
    (readHeader_items _ _ _ _ constructedFacts.header)
  change Native.execution ops allocate safety 7 6 call.source call.address Insertion.Tests.model
    call.native call.key call.normalized true rows taken.world (some growth) =
      ((.ok (some .success), Storage.publishedOwnership), after) at ran
  rw [ran] at checked
  have inserted : Native.insert ops allocate safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true (some growth) taken.world =
        (.ok (Storage.idFor rows), call.publicationWorld rows object operands taken.world after) := by
    simp only [Native.insert, takenFacts.projected, Native.body, checked, candidate,
      Interner.insertionOutcome, Except.mapError]
    rfl
  have facts : GraphFacts safety cloneMemory.memory.nextId capacity (call.publicationWorld rows object operands taken.world after)
      (rows ++ [call.publicationRow object operands taken.world]) := by
    obtain ⟨native, located, inputTyped, inputReads⟩ := constructedFacts.nativeInput
    obtain ⟨_, _, array, arrayFound, arrayTyped, _⟩ := constructedFacts.owned
    have different : AssemblyItem.Creation.NativeFields.Tests.source.allocation ≠ oldBacking :=
      constructed.memory.memory.heap.lookup_ne_of_type_ne _ _ native array located arrayFound
        (by simp [inputTyped, arrayTyped, AssemblyItem.viewType, Backing.type])
    have kept := frame _ native located (by decide) different (constructedFacts.input_apart call.key)
    refine ⟨rfl, ?_, valid, ⟨finalOwner, ownerFound, ownerTyped, ownerWritable⟩, owned, vector, ?_,
      descriptors, resident, items, ⟨native, kept, inputTyped, inputReads.frame (kept.trans located.symm)⟩,
      live, unique, apart, accepted, ?_⟩
    · change Cache.put equalityFields taken.world.graph.table call.key (Storage.idFor rows) =
        OwnedKeys.view (memory after).effects.keys
      rw [keys, OwnedKeys.view_store, entry.origin.graph, constructedFacts.linked]
      rfl
    · simpa only [List.length_append, List.length_singleton] using header
    · intro logical member
      rcases List.mem_append.mp member with old | added
      · exact constructedFacts.data_after call.key (memory after).memory frame logical old
      · have same := List.mem_singleton.mp added
        subst logical
        intro _
        exact itemReads .data
  exact ⟨after, inserted, facts, oldDead, nativeDead, keys, frame, registry, custody, privateSource, itemReads⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
