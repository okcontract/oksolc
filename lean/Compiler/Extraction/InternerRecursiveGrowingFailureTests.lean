/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursivePublicationTests
import Compiler.Extraction.InternerConstructorConstantAllocationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)

theorem constant_growth_contract (call : Call) (allocate : Backing.Registry.Allocate Nat)
    (safety : Bool) (backing oldCapacity capacity : Nat) (rows : List Storage.Cell)
    (prior : GraphFacts safety backing oldCapacity call.before rows) (bounded : rows.length ≤ oldCapacity)
    (reads : call.taken.2.world.graph.read = Storage.readValue rows)
    (current : call.Established safety backing oldCapacity rows) (observed : call.observations = call.expected)
    (kind : call.request.item.kind = 2) (empty : call.request.arguments = [])
    (classified : Interner.Queries.queries.deterministic call.request.item = .ok true)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength rows.length)
    (selected : capacity = Capacity.grow (Append.nextLength rows.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (count : rows.length < 2 ^ 32 - 1)
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits call.taken.2.world.memory.memory AssemblyItem.Creation.layout
      ((call.taken.2.world.memory.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment))
    (response : ∀ effects, allocate 7 (capacity * 32) 8 effects = (none, effects * 10 + 7))
    (unlocked : Owner.NativeLock.checkHeader call.constructed.memory.memory (Owner.headerAddress ⟨6, 0⟩) = .ok ()) :
    ∃ after : Native.Frame Nat,
      let reached := call.returnedWorld { call.taken.2.world with memory := Insertion.memory after }
      call.invoked (fun address native => callerPrimitives ops allocate safety 7 6 call.source address
        Insertion.Tests.model native childSeed (some growth)) =
        (.error (.language .outOfMemory), ⟨reached, ⟨none, some call.normalized, true⟩⟩) ∧
      GraphFacts safety backing oldCapacity reached rows ∧
      reached.memory.effects.keys = call.before.memory.effects.keys ∧
      (∀ id native, call.before.memory.memory.heap.lookup id = some native → reached.memory.memory.heap.lookup id = some native) ∧
      (∀ id block, call.before.memory.heap id = some block → reached.memory.heap id = some block) := by
  obtain ⟨made, counter, allocated, initialized, transferred, _, missed, keyed⟩ := call.prefix_results observed
  have setup : Caller.initLookup (Publication.external ops.arguments) 160 7 call.source
      ⟨call.constructed.memory.memory.nextId, 0, 2⟩ call.request
      ⟨{ call.constructed with memory := { call.constructed.memory with memory := call.stack } }, { lookup := none }⟩ =
      (.ok call.request.arguments, call.prepared.2) := by
    rw [counter]; exact Prod.ext initialized rfl
  have room : Interner.Queries.queries.atCapacity call.constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected]
    simp only [Nat.not_le.mpr count, decide_false]
  obtain ⟨owner, found, typed, _⟩ := prior.owner
  have lock := (Owner.NativeLock.checkHeader_eq_of_lookup safety call.before.memory.memory call.constructed.memory.memory
    6 owner current.item.valid.memory found typed ((current.item.memory 6 owner found).trans found.symm)).symm.trans unlocked
  let created := (AssemblyItem.Creation.create (observe ops.create) 7 call.native.item call.taken.2.world.memory).2
  let installed := (AssemblyClone.NativeFields.install call.native call.taken.2.world.memory.memory.nextId created).toOption.getD created
  let allocationEffects := installed.effects.allocator * 10 + 7
  have allocation : ∀ reached, AssemblyClone.NativeFields.install call.native call.taken.2.world.memory.memory.nextId created = .ok reached →
      allocate 7 (capacity * 32) 8 reached.effects.allocator = (none, allocationEffects) := by
    intro reached assigned
    have same : installed = reached := congrArg (fun result => result.toOption.getD created) assigned
    rw [← same]
    exact response _
  have beforeReads : call.before.graph.read = Storage.readValue rows :=
    (congrArg Interner.Heap.read (current.entry.origin.graph.trans current.item.graph)).symm.trans reads
  obtain ⟨after, _, routed, facts, graph, keys, frame, registry⟩ := constant_growing_empty_oom ops allocate
    CallerGrowingChainTests.releaseBacking safety 160 7 6 backing oldCapacity capacity 17 23
    ((call.taken.2.world.memory.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) * AssemblyItem.Creation.layout.alignment)
    call.source Insertion.Tests.model childSeed Interner.Queries.queries call.request debug call.before call.constructed
    call.address _ call.stack call.request.arguments call.prepared.2 call.taken.2 call.key call.normalized call.lookup rows
    (prior.native bounded) beforeReads (Normalization.Tests.external_admitted _) current.item current.entry made room allocated setup
    classified keyed (by rw [current.item.graph]; exact missed)
    (by simpa only [Call.taken] using (Prod.ext transferred rfl : call.taken = (.ok (), call.taken.2))) kind empty
    oldNonempty full selected size count (call.taken.2.world.memory.effects.allocator * 10 + 5) allocationEffects
    rfl fits allocation lock
  have retained := prior.frame bounded facts.valid facts.projected (congrArg Interner.Heap.table graph) keys frame registry
  rw [counter] at routed retained keys frame
  exact ⟨after, routed, retained, keys, frame, registry⟩


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests.Call
