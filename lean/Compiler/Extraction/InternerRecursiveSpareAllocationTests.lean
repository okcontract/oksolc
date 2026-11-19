/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursivePublicationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops GraphFacts)

/-- Lift spare-capacity allocator independence through the actual caller
preparation, native insertion control and reached projection. -/
theorem spare_insertion_same (call : Call) (allocate other : Backing.Registry.Allocate Nat)
    (growth : Option (Growth.Registered.Callbacks Nat)) (safety : Bool) (backing capacity object : Nat)
    (rows : List Storage.Cell) (operands : ArgumentSlice)
    (constructed : World (Publication.Effects Nat)) (taken : OwnedCall.State (Publication.Effects Nat))
    (duplicateMemory createMemory cloneMemory : Session (Publication.Effects Nat))
    (entry : CallerInput 7 call.source call.address call.request call.request.arguments call.native call.key
      constructed taken call.normalized call.lookup)
    (constructedFacts : GraphFacts safety backing capacity constructed rows)
    (takenFacts : GraphFacts safety backing capacity taken.world rows)
    (spare : rows.length < capacity) (room : rows.length < 2 ^ 32 - 1)
    (duplicated : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
      ⟨view call.normalized, call.normalized.items, none⟩ taken.world.memory =
        (.ok (operands, ⟨view call.normalized, call.normalized.items, none⟩), duplicateMemory))
    (created : AssemblyItem.Creation.create (observe ops.create) 7 call.native.item duplicateMemory = (.ok object, createMemory))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) 7 call.native createMemory = (.ok call.native, cloneMemory)) :
    Native.insert ops allocate safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true growth taken.world =
    Native.insert ops other safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true growth taken.world := by
  let value := (call.key.eval Insertion.Tests.model taken.world.graph.read).getD 0
  let graph : Storage.State → Native.Frame Nat → Interner.Heap := fun owner state => Interner.InsertionExecution.project
    rows taken.world.graph.table (cell call.native call.key call.normalized value owner state) call.key owner
  obtain ⟨installed, duplicateRun, createRun, cloneRun, established, assigned, _, _, _, _, _, _, _, _, frame, _⟩ :=
    entry.prepare ops allocate safety 7 6 object call.source call.address call.request call.request.arguments
      call.native call.native call.key call.normalized operands call.lookup
      ⟨view call.normalized, call.normalized.items, none⟩ constructed taken rows value graph
      duplicateMemory createMemory cloneMemory (Normalization.Tests.external_admitted _) duplicated created cloned
  obtain ⟨owner, found, typed, writable⟩ := constructedFacts.owner
  have ownerFrame := (frame 6 owner found).trans found.symm
  have header := (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) itemsOffset ownerFrame).trans
    (readHeader_items _ _ _ _ constructedFacts.header)
  have count := (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨6, 0⟩) capacityOffset ownerFrame).trans
    constructedFacts.capacity_read
  let ready := preparedFrame object call.native operands installed
  have sameAppend : append safety allocate 7 6 rows call.native call.key call.normalized value preparationOwnership ready growth =
      append safety other 7 6 rows call.native call.key call.normalized value preparationOwnership ready growth := by
    have core := Append.Registered.spare_allocators safety installed 7 6 backing capacity owner rows
      (cell call.native call.key call.normalized value preparationOwnership ready) (allocation allocate) (allocation other)
      established.valid (frame _ _ found) typed header count spare
      (by simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega)
    cases growth with
    | none => simp only [append, show memory ready = installed from rfl, core]
    | some calls =>
      have first := Append.Registered.spare_same safety installed 7 6 backing capacity owner rows
        (cell call.native call.key call.normalized value preparationOwnership ready) (allocation allocate) (growthCallbacks calls)
        established.valid (frame _ _ found) typed header count spare
        (by simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega)
      have second := Append.Registered.spare_same safety installed 7 6 backing capacity owner rows
        (cell call.native call.key call.normalized value preparationOwnership ready) (allocation other) (growthCallbacks calls)
        established.valid (frame _ _ found) typed header count spare
        (by simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega)
      simp only [append, show memory ready = installed from rfl, first, second, core]
  let start : Native.Frame Nat := ⟨⟨⟨⟨taken.world.memory, false⟩, none⟩, none⟩, none⟩
  let dupe : Native.Frame Nat := ⟨⟨⟨⟨duplicateMemory, false⟩, none⟩, none⟩, some operands⟩
  let made : Native.Frame Nat := ⟨⟨⟨⟨createMemory, false⟩, none⟩, some object⟩, some operands⟩
  have duplicateAll (a : Backing.Registry.Allocate Nat) (g : Option (Growth.Registered.Callbacks Nat)) : ∀ owner,
      (Native.callbacks ops a safety 7 6 call.source call.address call.native call.key call.normalized rows value graph g).attempt
        .arguments owner start = (.ok true, dupe) := duplicateRun
  have createAll (a : Backing.Registry.Allocate Nat) (g : Option (Growth.Registered.Callbacks Nat)) : ∀ owner,
      (Native.callbacks ops a safety 7 6 call.source call.address call.native call.key call.normalized rows value graph g).attempt
        .item owner dupe = (.ok true, made) := createRun
  have cloneAll (a : Backing.Registry.Allocate Nat) (g : Option (Growth.Registered.Callbacks Nat)) : ∀ owner,
      (Native.callbacks ops a safety 7 6 call.source call.address call.native call.key call.normalized rows value graph g).attempt
        .clone owner made = (.ok true, ready) := cloneRun
  have sameAttempt :
      (Native.callbacks ops allocate safety 7 6 call.source call.address call.native call.key call.normalized rows value graph growth).attempt
        .append preparationOwnership ready =
      (Native.callbacks ops other safety 7 6 call.source call.address call.native call.key call.normalized rows value graph growth).attempt
        .append preparationOwnership ready := sameAppend
  have executed : Native.execution ops allocate safety 7 6 call.source call.address Insertion.Tests.model
      call.native call.key call.normalized true rows taken.world growth =
      Native.execution ops other safety 7 6 call.source call.address Insertion.Tests.model
        call.native call.key call.normalized true rows taken.world growth := by
    have compared := Storage.insert_prepared_congr
      (Native.callbacks ops allocate safety 7 6 call.source call.address call.native call.key call.normalized rows value graph growth)
      (Native.callbacks ops other safety 7 6 call.source call.address call.native call.key call.normalized rows value graph growth)
      start dupe made ready (duplicateAll allocate growth) (createAll allocate growth) (cloneAll allocate growth)
      (duplicateAll other growth) (createAll other growth) (cloneAll other growth) sameAttempt rfl rfl
    simpa only [Native.execution, executionWithRoom, room, decide_true] using compared
  have first := entry.checked_execution ops allocate safety 7 6 call.source call.address Insertion.Tests.model
    call.request call.request.arguments call.native call.key call.normalized call.lookup constructed taken true rows growth
    owner ⟨backing, 0⟩ found (readHeader_items _ _ _ _ constructedFacts.header)
  have second := entry.checked_execution ops other safety 7 6 call.source call.address Insertion.Tests.model
    call.request call.request.arguments call.native call.key call.normalized call.lookup constructed taken true rows growth
    owner ⟨backing, 0⟩ found (readHeader_items _ _ _ _ constructedFacts.header)
  simp only [Native.insert, takenFacts.projected, Native.body, first, second, executed]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
