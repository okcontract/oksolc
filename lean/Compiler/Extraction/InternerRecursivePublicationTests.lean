/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveCallReturnTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops GraphFacts)

/-- Shared actual publication stages for complete constructor calls. -/
def duplicate (call : Call) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
  ⟨view call.normalized, call.normalized.items, none⟩ call.taken.2.world.memory
def create (call : Call) := AssemblyItem.Creation.create (observe ops.create) 7 call.native.item call.duplicate.2
def clone (call : Call) := AssemblyClone.Physical.run (observe ops.copy) 7 call.native call.create.2
def installed (call : Call) (object : Nat) (memory : Session (Publication.Effects Nat)) :=
  (AssemblyClone.NativeFields.install call.native object memory).toOption.getD memory
def publicationRow (call : Call) (object : Nat) (operands : ArgumentSlice) (world : World (Publication.Effects Nat)) : Storage.Cell :=
  ⟨call.native.item, (call.key.eval Insertion.Tests.model world.graph.read).getD 0,
    object, operands.items, call.key.sequence, operands.address⟩
def publicationWorld (call : Call) (rows : List Storage.Cell) (object : Nat) (operands : ArgumentSlice) (world : World (Publication.Effects Nat)) (after : Native.Frame Nat) :=
  Insertion.projected rows world call.key (call.publicationRow object operands world) Storage.publishedOwnership after

private theorem probe_response (query : Key) (session : Session (Publication.Effects Nat)) :
    ops.probe query (Publication.forget session) = (true, session.effects.allocator * 10 + 8) := rfl

/-- Native publication works on the explicit reached caller states. Keeping
those states as parameters avoids reducing their whole constructor histories. -/
theorem spare_native (call : Call) (allocate : Backing.Registry.Allocate Nat) (growth : Option (Growth.Registered.Callbacks Nat)) (safety : Bool) (backing capacity object : Nat)
    (rows : List Storage.Cell) (operands : ArgumentSlice)
    (constructed : World (Publication.Effects Nat)) (taken : OwnedCall.State (Publication.Effects Nat))
    (duplicateMemory createMemory cloneMemory : Session (Publication.Effects Nat))
    (entry : CallerInput 7 call.source call.address call.request call.request.arguments call.native call.key
      constructed taken call.normalized call.lookup)
    (constructedFacts : GraphFacts safety backing capacity constructed rows)
    (takenFacts : GraphFacts safety backing capacity taken.world rows)
    (domain : (call.request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (spare : rows.length < capacity) (room : rows.length < 2 ^ 32 - 1)
    (duplicated : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
      ⟨view call.normalized, call.normalized.items, none⟩ taken.world.memory =
        (.ok (operands, ⟨view call.normalized, call.normalized.items, none⟩), duplicateMemory))
    (created : AssemblyItem.Creation.create (observe ops.create) 7 call.native.item duplicateMemory = (.ok object, createMemory))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) 7 call.native createMemory = (.ok call.native, cloneMemory)) :
    ∃ after,
    Native.insert ops allocate safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true growth taken.world =
        (.ok (Storage.idFor rows), call.publicationWorld rows object operands taken.world after) ∧
    GraphFacts safety backing capacity (call.publicationWorld rows object operands taken.world after)
      (rows ++ [call.publicationRow object operands taken.world]) ∧
    AssemblyClone.NativeFields.Represents (call.publicationWorld rows object operands taken.world after).memory.memory ⟨object, 0⟩ call.native ∧
    (∀ id native, constructed.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ backing →
      (∀ old, constructed.memory.effects.keys call.key = some old → call.key.arguments ≠ [] → id ≠ old.address) →
      (memory after).memory.heap.lookup id = some native) ∧
    (memory after).memory.nextId = cloneMemory.memory.nextId ∧
    (memory after).memory.nextAddress = cloneMemory.memory.nextAddress ∧
    Owner.NativeLock.checkHeader (memory after).memory (Owner.headerAddress ⟨6, 0⟩) =
      Owner.NativeLock.checkHeader constructed.memory.memory (Owner.headerAddress ⟨6, 0⟩) := by
  obtain ⟨owner, found, typed, writable⟩ := constructedFacts.owner
  let effects := (memory (append safety allocate 7 6 rows call.native call.key call.normalized
    ((call.key.eval Insertion.Tests.model taken.world.graph.read).getD 0) preparationOwnership
    (preparedFrame object call.native operands (call.installed object cloneMemory))).2).effects.allocator * 10 + 8
  obtain ⟨_, _, after, finalOwner, _, _, ran, valid, ownerFound, ownerTyped, ownerWritable, vector, owned, header,
      descriptors, resident, _, itemReads, _, _, _, live, unique, apart, accepted, keys, _, nextId, nextAddress, _, frame, _, items, candidate, lock⟩ :=
    entry.spare_success ops allocate safety 7 6 backing capacity object owner
      call.source call.address Insertion.Tests.model call.request call.request.arguments call.native call.native call.key
      call.normalized operands call.lookup ⟨view call.normalized, call.normalized.items, none⟩ constructed taken rows
      duplicateMemory createMemory cloneMemory (Normalization.Tests.external_admitted _) found typed writable
      constructedFacts.owned (readHeader_items _ _ _ _ constructedFacts.header)
      constructedFacts.capacity_read constructedFacts.vector constructedFacts.descriptors
      constructedFacts.resident constructedFacts.apart constructedFacts.items domain spare room
      duplicated created cloned effects (by
        intro reached assigned
        have same : call.installed object cloneMemory = reached :=
          congrArg (fun result => result.toOption.getD cloneMemory) assigned
        rw [← same]; exact probe_response _ _) (growth := growth)
  have checked := entry.checked_execution ops allocate safety 7 6 call.source call.address
    Insertion.Tests.model call.request call.request.arguments call.native call.key call.normalized call.lookup
    constructed taken true rows growth owner ⟨backing, 0⟩ found
    (readHeader_items _ _ _ _ constructedFacts.header)
  rw [ran] at checked
  have inserted : Native.insert ops allocate safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true growth taken.world =
        (.ok (Storage.idFor rows), call.publicationWorld rows object operands taken.world after) := by
    simp only [Native.insert, takenFacts.projected, Native.body, checked, candidate,
      Interner.insertionOutcome, Except.mapError]
    rfl
  have facts : GraphFacts safety backing capacity (call.publicationWorld rows object operands taken.world after)
      (rows ++ [call.publicationRow object operands taken.world]) := by
    obtain ⟨native, located, inputTyped, inputReads⟩ := constructedFacts.nativeInput
    obtain ⟨_, _, array, arrayFound, arrayTyped, _⟩ := constructedFacts.owned
    have different : AssemblyItem.Creation.NativeFields.Tests.source.allocation ≠ backing :=
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
      · have sameRow := List.mem_singleton.mp added
        subst logical
        intro _
        exact itemReads .data
  exact ⟨after, inserted, facts, itemReads, frame, nextId, nextAddress, lock⟩

/-- Finish the actual publication and return both constructor locals. The same
return proof applies to first allocation, spare insertion and relocation. -/
theorem publication_return (call : Call) (allocate : Backing.Registry.Allocate Nat) (growth : Option (Growth.Registered.Callbacks Nat))
    (safety : Bool) (backing capacity object oldBacking : Nat) (rows : List Storage.Cell) (operands : ArgumentSlice)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (after : Native.Frame Nat)
    (entry : CallerInput 7 call.source call.address call.request call.request.arguments call.native call.key
      call.constructed call.taken.2 call.normalized call.lookup)
    (inserted : Native.insert ops allocate safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true growth call.taken.2.world =
        (.ok (Storage.idFor rows), call.publicationWorld rows object operands call.taken.2.world after))
    (facts : GraphFacts safety backing capacity (call.publicationWorld rows object operands call.taken.2.world after)
      (rows ++ [call.publicationRow object operands call.taken.2.world]))
    (itemReads : AssemblyClone.NativeFields.Represents
      (call.publicationWorld rows object operands call.taken.2.world after).memory.memory ⟨object, 0⟩ call.native)
    (validBefore : Valid call.before.memory)
    (frame : ∀ id native, call.before.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ oldBacking →
      (∀ old, call.before.memory.effects.keys call.key = some old → call.key.arguments ≠ [] → id ≠ old.address) →
      (memory after).memory.heap.lookup id = some native)
    (older : 6 < call.before.memory.memory.nextId)
    (bounded : (rows ++ [call.publicationRow object operands call.taken.2.world]).length ≤ capacity)
    (routed : call.invoked p =
      (let done := finishInsertion ops allocate safety 7 6 call.source call.address
        Insertion.Tests.model call.native call.key true call.taken.2 growth
       if ordinary done.1 then (done.1, call.returned done.2) else done)) :
    (call.invoked p).1 = .ok (Storage.idFor rows) ∧
    GraphFacts safety backing capacity (call.invoked p).2.world (rows ++ [call.publicationRow object operands call.taken.2.world]) ∧
    AssemblyClone.NativeFields.Represents (call.invoked p).2.world.memory.memory ⟨object, 0⟩ call.native ∧
    (call.invoked p).2.world.graph.read = Storage.readValue (rows ++ [call.publicationRow object operands call.taken.2.world]) ∧
    (∀ id native, call.before.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ oldBacking →
      (∀ old, call.before.memory.effects.keys call.key = some old → call.key.arguments ≠ [] → id ≠ old.address) →
      (call.invoked p).2.world.memory.memory.heap.lookup id = some native) := by
  have finished := entry.finish_native ops allocate safety 7 6 call.source call.address
    Insertion.Tests.model call.request call.request.arguments call.native call.key call.normalized call.lookup
    call.constructed call.taken.2 true growth
  rw [inserted] at finished
  rw [finished] at routed
  have reached : (call.invoked p).2.world = call.returnedWorld (call.publicationWorld rows object operands call.taken.2.world after) :=
    congrArg (fun result => result.2.world) routed
  have inputOlder : AssemblyItem.Creation.NativeFields.Tests.source.allocation < call.before.memory.memory.nextId := by
    change 5 < call.before.memory.memory.nextId; omega
  have cleaned := (facts.cleanup (call.before.memory.memory.nextId + 1) (by omega) (by omega) bounded).cleanup
    call.before.memory.memory.nextId older inputOlder bounded
  obtain ⟨native, located⟩ := itemReads.live
  obtain ⟨stored, registered, persistent⟩ := facts.valid.injected _ _
    (facts.resident (call.publicationRow object operands call.taken.2.world) (List.mem_append_right _ (List.mem_singleton_self _))).1
  have same := Option.some.inj (located.symm.trans registered)
  subst stored
  have inner := persistent_cleanup _ (call.before.memory.memory.nextId + 1) _ native located persistent
  have outer := persistent_cleanup _ call.before.memory.memory.nextId _ native inner persistent
  refine ⟨congrArg Prod.fst routed, ?_, ?_, ?_, ?_⟩
  · rw [reached]; exact cleaned
  · rw [reached]; exact itemReads.frame (outer.trans located.symm)
  · rw [reached]; rfl
  · intro id native found ownerApart backingApart keyApart
    rw [reached]
    exact call.returned_cell _ validBefore id native found (frame id native found ownerApart backingApart keyApart)

/-- Reuse one native spare-capacity publication and return proof for Push and
operation calls. Prefix observations and routing refer to those same executions;
no reached graph, ownership or query conclusion is supplied by the caller. -/
theorem spare_publication (call : Call) (allocate : Backing.Registry.Allocate Nat) (growth : Option (Growth.Registered.Callbacks Nat)) (safety : Bool) (backing capacity object : Nat)
    (rows : List Storage.Cell) (operands : ArgumentSlice)
    (duplicateMemory createMemory cloneMemory : Session (Publication.Effects Nat))
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (prior : GraphFacts safety backing capacity call.before rows)
    (good : Good call.source call.request.arguments call.before)
    (domain : (call.request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (observed : call.observations = call.expected)
    (spare : rows.length < capacity) (room : rows.length < 2 ^ 32 - 1)
    (duplicated : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
      ⟨view call.normalized, call.normalized.items, none⟩ call.taken.2.world.memory =
        (.ok (operands, ⟨view call.normalized, call.normalized.items, none⟩), duplicateMemory))
    (created : AssemblyItem.Creation.create (observe ops.create) 7 call.native.item duplicateMemory = (.ok object, createMemory))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) 7 call.native createMemory = (.ok call.native, cloneMemory))
    (routed : call.invoked p =
      (let done := finishInsertion ops allocate safety 7 6 call.source call.address
        Insertion.Tests.model call.native call.key true call.taken.2 growth
       if ordinary done.1 then (done.1, call.returned done.2) else done)) :
    (call.invoked p).1 = .ok (Storage.idFor rows) ∧
    GraphFacts safety backing capacity (call.invoked p).2.world (rows ++ [call.publicationRow object operands call.taken.2.world]) ∧
    AssemblyClone.NativeFields.Represents (call.invoked p).2.world.memory.memory ⟨object, 0⟩ call.native ∧
    (call.invoked p).2.world.graph.read = Storage.readValue (rows ++ [call.publicationRow object operands call.taken.2.world]) ∧
    (∀ id native, call.before.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ backing →
      (∀ old, call.before.memory.effects.keys call.key = some old → call.key.arguments ≠ [] → id ≠ old.address) →
      (call.invoked p).2.world.memory.memory.heap.lookup id = some native) ∧
    (call.invoked p).2.world.memory.memory.nextId = cloneMemory.memory.nextId ∧
    (call.invoked p).2.world.memory.memory.nextAddress = cloneMemory.memory.nextAddress ∧
    (call.invoked p).2.world.graph.table call.key = some (Storage.idFor rows) ∧
    (call.invoked p).2.world.graph.table =
      Cache.put equalityFields call.before.graph.table call.key (Storage.idFor rows) ∧
    Owner.NativeLock.checkHeader (call.invoked p).2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) =
      Owner.NativeLock.checkHeader call.before.memory.memory (Owner.headerAddress ⟨6, 0⟩) := by
  have established := call.establish safety backing capacity rows prior (Nat.le_of_lt spare) good domain observed
  obtain ⟨after, inserted, facts, itemReads, frame, nextId, nextAddress, insertedLock⟩ := spare_native call allocate growth safety backing capacity object rows operands call.constructed call.taken.2 duplicateMemory createMemory cloneMemory
    established.entry established.constructed established.taken domain spare room duplicated created cloned
  obtain ⟨oldOwner, oldFound, oldTyped, _⟩ := prior.owner
  have returned := publication_return call allocate growth safety backing capacity object backing rows operands p after established.entry
    inserted facts itemReads prior.valid (fun id native found ownerApart backingApart keyApart =>
      frame id native (established.item.memory id native found) ownerApart backingApart (by
        intro old selected nonempty
        rw [established.item.effects] at selected
        exact keyApart old selected nonempty))
    (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory oldFound).1
    (by simp only [List.length_append, List.length_singleton]; omega) routed

  have finished := established.entry.finish_native ops allocate safety 7 6 call.source call.address
    Insertion.Tests.model call.request call.request.arguments call.native call.key call.normalized call.lookup
    call.constructed call.taken.2 true growth
  rw [inserted] at finished
  rw [finished] at routed
  have idCounter := congrArg (fun result => result.2.world.memory.memory.nextId) routed
  have addressCounter := congrArg (fun result => result.2.world.memory.memory.nextAddress) routed
  have keyResult := congrArg (fun result => result.2.world.graph.table call.key) routed
  have tableResult := congrArg (fun result => result.2.world.graph.table) routed
  have table : (call.invoked p).2.world.graph.table =
      Cache.put equalityFields call.before.graph.table call.key (Storage.idFor rows) := by
    change (call.invoked p).2.world.graph.table = _ at tableResult
    rw [tableResult]
    change Cache.put equalityFields call.taken.2.world.graph.table call.key (Storage.idFor rows) = _
    rw [established.entry.origin.graph, established.item.graph]
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory oldFound).1
  have actualWorld : (call.invoked p).2.world =
      call.returnedWorld (call.publicationWorld rows object operands call.taken.2.world after) :=
    congrArg (fun result => result.2.world) routed
  have ownerFrame : (call.invoked p).2.world.memory.memory.heap.lookup 6 =
      (call.publicationWorld rows object operands call.taken.2.world after).memory.memory.heap.lookup 6 := by
    rw [actualWorld]
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ 6 older).trans
      (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ 6 (Nat.lt_trans older (Nat.lt_succ_self _)))
  obtain ⟨newOwner, newFound, newTyped, _⟩ := facts.owner
  have lock := (Owner.NativeLock.checkHeader_eq_of_lookup safety
    (call.publicationWorld rows object operands call.taken.2.world after).memory.memory
    (call.invoked p).2.world.memory.memory 6 newOwner returned.2.1.valid.memory newFound newTyped ownerFrame).trans
    (insertedLock.trans (Owner.NativeLock.checkHeader_eq_of_lookup safety call.before.memory.memory
      call.constructed.memory.memory 6 oldOwner established.item.valid.memory oldFound oldTyped
      ((established.item.memory 6 oldOwner oldFound).trans oldFound.symm)))
  exact ⟨returned.1, returned.2.1, returned.2.2.1, returned.2.2.2.1, returned.2.2.2.2,
    idCounter.trans nextId, addressCounter.trans nextAddress, keyResult.trans (Cache.put_returns _ _ _), table, lock⟩

/-- Empty argument ownership follows the actual item/scratch preparation and take. -/
theorem duplicate_empty (call : Call) (arguments : call.request.arguments = [])
    (source : call.source.length = 0) (commutative : Interner.Scoped.commutative call.request.item = .ok false)
    (current : Prepared call.request.item debug call.before call.constructed)
    (allocated : Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨call.before.memory.memory.nextId + 1, 0⟩, call.stack)) :
    call.duplicate = (.ok (call.normalized, ⟨view call.normalized, [], none⟩), call.taken.2.world.memory) := by
  have counter := (Compiler.ZigAir.Memory.allocate_pointer _ _ _ _ allocated).2
  rw [current.nextId] at counter
  have normalized := call.normalized_empty arguments source commutative current allocated
  have items : call.normalized.items = [] := arguments
  simp only [Call.duplicate, takeOwned, items]
  rw [Duplication.run_empty _ _ _ _ _ _ (by change call.request.arguments.length = 0; rw [arguments]; rfl)]
  simp only [normalized.2.2.2, Call.normalized, arguments, counter]

/-- The actual create response fixes the returned allocation identity. -/
theorem created (call : Call) (valid : Valid call.duplicate.2)
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits call.duplicate.2.memory AssemblyItem.Creation.layout
      ((call.duplicate.2.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment)) :
    call.create.1 = .ok call.duplicate.2.memory.nextId := by
  have complete := AssemblyItem.Creation.create_from_response (observe ops.create) 7
    ((call.duplicate.2.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment)
    call.native.item call.duplicate.2
    { call.duplicate.2.effects with allocator := call.duplicate.2.effects.allocator * 10 + 5 }
    valid rfl fits
  exact congrArg Prod.fst complete.1
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
