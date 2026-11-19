/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorLookupReturn
import Compiler.Extraction.InternerCallerPublicationCleanup
import Compiler.Extraction.InternerNativeReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Native graph and key retention for an ordinary initialized lookup return.
Cache hits and classification errors supply their actual routing equation to
this common preparation, cleanup and publication frame proof. -/
theorem invoke_initialized_native (host : External σ) (budget allocator owner capacity : Nat) (safety : Bool)
    (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects σ))
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State (Publication.Effects σ)) (outcome : Except Fault NodeId)
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (completed : ordinary outcome = true)
    (routed : Caller.find (Publication.external host) budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } = OwnedCall.finish (Publication.external host) allocator outcome prepared) :
    let actual := invoke (Publication.external host) budget allocator p q source request debug before
    actual.1 = outcome ∧ NativeGraph.Facts safety allocator owner data capacity actual.2.world rows ∧
      Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧ actual.2.world.memory.effects.keys = before.memory.effects.keys ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  obtain ⟨result, good, closed, graph, native, registry, normalized⟩ := invoke_initialized_verified
    (Publication.external host) budget allocator p q source request debug before constructed address pointer memory
    values prepared outcome ⟨facts.valid, represented⟩ (Publication.external_admitted host admitted) domain typed
    made room allocated initialized completed routed
  have item := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
  have initKeys := Publication.caller_init_keys host budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩
  rw [initialized] at initKeys
  have finishKeys := Publication.caller_finish_keys host allocator outcome prepared
  have keys : (invoke (Publication.external host) budget allocator p q source request debug before).2.world.memory.effects.keys =
      before.memory.effects.keys := by
    rw [invoke_after_scratch_effects _ _ _ _ _ _ _ _ _ _ _ _ _ made room allocated, routed]
    exact finishKeys.trans (initKeys.trans (congrArg Publication.Effects.keys item.effects))
  exact ⟨result, facts.frame good.1 ((congrArg Interner.Heap.representatives graph).trans facts.projected)
    (congrArg Interner.Heap.table graph) keys (fun id cell found _ => native id cell found) registry,
    good, closed, graph, keys, native, registry, normalized⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Share the proper-child leaf packaging for initialized returns. A successful
result supplies its word from the unchanged initial graph; errors require no
word witness. The actual routing equation is discharged by each entry branch. -/
theorem step_initialized_verified (base : PairInput.Context (Publication.Effects σ))
    (host : External σ) (owner usizeBits capacity : Nat) (safety : Bool)
    (children : Constructors (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State (Publication.Effects σ)) (outcome : Except Fault NodeId)
    (other : Meaning) (expected : Word)
    (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : base.queries.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup base.external base.budget base.allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (completed : ordinary outcome = true)
    (routed : Caller.find base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source address (input request.item debug)) base.queries source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } = OwnedCall.finish base.external base.allocator outcome prepared)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (word : normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values →
      ∀ id, outcome = .ok id → before.graph.read id = some expected) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    actual.1 = outcome ∧
      Returns (GraphFrame safety base.allocator owner rows (Retains before)) actual outcome before.graph ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
          (outcome, actual.2.world)) := by
  dsimp only
  have checked := invoke_initialized_native host base.budget base.allocator owner capacity safety data rows
    ((context base owner usizeBits children debug).primitives source) base.queries source request debug before constructed
    address pointer memory values prepared outcome facts represented admitted domain typed made room allocated
    (by simpa only [external] using initialized) completed (by simpa only [external] using routed)
  rw [← external] at checked
  obtain ⟨result, native, _, closed, graph, keys, memory, registry, normalized⟩ := checked
  exact step_return_verified base owner usizeBits capacity safety children data rows source request debug before outcome other expected
    result native closed graph keys memory registry valid (word normalized)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
