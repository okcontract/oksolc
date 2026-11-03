/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorTakeFailure
import Compiler.Extraction.InternerCallerPublicationInput
import Compiler.Extraction.InternerNativeReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Failed take preserves the scoped native graph and exact key table through
its actual allocation attempt and local return. Ordinary OOM and the original
allocation frame are derived, not supplied as postconditions. -/
theorem invoke_take_failed_native (host : External σ) (budget allocator owner capacity : Nat) (safety : Bool)
    (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects σ))
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared reached : State (Publication.Effects σ)) (fault : Fault) (key : Key) (deterministic : Bool)
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok deterministic)
    (keyed : Interner.makeKey request values = .ok key)
    (missed : deterministic = true → constructed.graph.table key = none)
    (failed : take (Publication.external host) allocator prepared = (.error fault, reached)) :
    let actual := invoke (Publication.external host) budget allocator p q source request debug before
    fault = .language .outOfMemory ∧ actual.1 = .error fault ∧
      actual.2.world = returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world ∧
      NativeGraph.Facts safety allocator owner data capacity actual.2.world rows ∧
      Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧ actual.2.world.memory.effects.keys = before.memory.effects.keys ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  obtain ⟨oom, result, world, good, closed, graph, native, registry, normalized⟩ := invoke_take_failed
    (Publication.external host) budget allocator p q source request debug before constructed address pointer memory
    values prepared reached fault key deterministic ⟨facts.valid, represented⟩ (Publication.external_admitted host admitted)
    domain typed made room allocated initialized classified keyed missed failed
  have item := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
  have initKeys := Publication.caller_init_keys host budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩
  rw [initialized] at initKeys
  have takeKeys := Publication.caller_take_keys host allocator prepared
  rw [failed] at takeKeys
  have keys : (invoke (Publication.external host) budget allocator p q source request debug before).2.world.memory.effects.keys =
      before.memory.effects.keys := by
    rw [world]
    exact takeKeys.trans (initKeys.trans (congrArg Publication.Effects.keys item.effects))
  exact ⟨oom, result, world, facts.frame good.1 ((congrArg Interner.Heap.representatives graph).trans facts.projected)
    (congrArg Interner.Heap.table graph) keys (fun id cell found _ => native id cell found) registry,
    good, closed, graph, keys, native, registry, normalized⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Failed take is a leaf for arbitrary proper children. Reuse the shared
native step return after deriving its caller outcome and storage frame. -/
theorem step_take_failed_verified (base : PairInput.Context (Publication.Effects σ))
    (host : External σ) (owner usizeBits capacity : Nat) (safety : Bool)
    (children : Constructors (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared reached : State (Publication.Effects σ)) (fault : Fault) (key : Key) (deterministic : Bool)
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
    (classified : base.queries.deterministic request.item = .ok deterministic)
    (keyed : Interner.makeKey request values = .ok key)
    (missed : deterministic = true → constructed.graph.table key = none)
    (failed : take base.external base.allocator prepared = (.error fault, reached))
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    fault = .language .outOfMemory ∧ actual.1 = .error fault ∧
      Returns (GraphFrame safety base.allocator owner rows (Retains before)) actual (.error fault) before.graph ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
          (.error fault, actual.2.world)) := by
  dsimp only
  have checked := invoke_take_failed_native host base.budget base.allocator owner capacity safety data rows
    ((context base owner usizeBits children debug).primitives source) base.queries source request debug before constructed
    address pointer memory values prepared reached fault key deterministic facts represented admitted domain typed made room allocated
    (by simpa only [external] using initialized) classified keyed missed (by simpa only [external] using failed)
  rw [← external] at checked
  obtain ⟨oom, result, _, native, _, closed, graph, keys, memory, registry, _⟩ := checked
  exact ⟨oom, step_return_verified base owner usizeBits capacity safety children data rows source request debug before (.error fault)
    other expected result native closed graph keys memory registry valid (by intro _ impossible; cases impossible)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
