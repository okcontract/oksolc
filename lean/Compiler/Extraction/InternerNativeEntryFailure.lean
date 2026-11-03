/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorEntryFailure
import Compiler.Extraction.InternerConstructorScratch
import Compiler.Extraction.InternerCallerPublicationCleanup
import Compiler.Extraction.InternerNativeReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Entry failures before lookup ownership derive the native frame from actual
capacity or initialization observations. No simplifier/insertion contract or
successful lookup premise is supplied. Allocator effects are never rewound. -/
theorem invoke_entry_failed_native (host : External σ) (budget allocator owner capacity : Nat) (safety : Bool)
    (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects σ))
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address) (fault : Fault)
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (completed : ordinary (.error fault : Except Fault NodeId) = true)
    (stopped :
      (q.atCapacity constructed.graph = true ∧ fault = .language .capacity) ∨
      (q.atCapacity constructed.graph = false ∧ ∀ memory,
        Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
          .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) →
        ∃ reached, Caller.initLookup (Publication.external host) budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
          ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.error fault, reached))) :
    let actual := invoke (Publication.external host) budget allocator p q source request debug before
    actual.1 = .error fault ∧ NativeGraph.Facts safety allocator owner data capacity actual.2.world rows ∧
      Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧ actual.2.world.memory.effects.keys = before.memory.effects.keys ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) := by
  rcases stopped with ⟨full, rfl⟩ | ⟨room, initialization⟩
  · obtain ⟨ran, good, closed, graph, effects, native, registry⟩ := invoke_capacity_failed
      (Publication.external host) budget allocator p q source request debug before constructed address
      ⟨facts.valid, represented⟩ domain typed made full
    have keys := congrArg Publication.Effects.keys effects
    exact ⟨congrArg Prod.fst ran, facts.frame good.1 ((congrArg Interner.Heap.representatives graph).trans facts.projected)
      (congrArg Interner.Heap.table graph) keys (fun id cell found _ => native id cell found) registry,
      good, closed, graph, keys, native, registry⟩
  · obtain ⟨memory, allocated⟩ := prepare_scratch request.item debug before constructed address facts.valid domain typed made
    obtain ⟨reached, failed⟩ := initialization memory allocated
    obtain ⟨result, ran, good, closed, graph, native, registry⟩ := invoke_init_failed
      (Publication.external host) budget allocator p q source request debug before constructed address _ memory fault reached
      ⟨facts.valid, represented⟩ (Publication.external_admitted host admitted) domain typed made room allocated failed completed
    have item := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
    have initKeys := Publication.caller_init_keys host budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩
    rw [failed] at initKeys
    have keys : (invoke (Publication.external host) budget allocator p q source request debug before).2.world.memory.effects.keys =
        before.memory.effects.keys := by
      rw [ran]
      exact initKeys.trans (congrArg Publication.Effects.keys item.effects)
    exact ⟨result, facts.frame good.1 ((congrArg Interner.Heap.representatives graph).trans facts.projected)
      (congrArg Interner.Heap.table graph) keys (fun id cell found _ => native id cell found) registry,
      good, closed, graph, keys, native, registry⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- Capacity and ordinary initialization failures are leaves of the actual
proper-child step. Derive their exact error, original graph/native frame and
semantic error result; arbitrary children are never reached. -/
theorem step_entry_failed_verified (base : PairInput.Context (Publication.Effects σ))
    (host : External σ) (owner usizeBits capacity : Nat) (safety : Bool)
    (children : Constructors (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (fault : Fault) (other : Meaning) (expected : Word)
    (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (completed : ordinary (.error fault : Except Fault NodeId) = true)
    (stopped :
      (base.queries.atCapacity constructed.graph = true ∧ fault = .language .capacity) ∨
      (base.queries.atCapacity constructed.graph = false ∧ ∀ memory,
        Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
          .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) →
        ∃ reached, Caller.initLookup base.external base.budget base.allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
          ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.error fault, reached)))
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    actual.1 = .error fault ∧
      Returns (GraphFrame safety base.allocator owner rows (Retains before)) actual (.error fault) before.graph ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
          (.error fault, actual.2.world)) := by
  dsimp only
  have checked := invoke_entry_failed_native host base.budget base.allocator owner capacity safety data rows
    ((context base owner usizeBits children debug).primitives source) base.queries source request debug before constructed address fault
    facts represented admitted domain typed made completed (by simpa only [external] using stopped)
  rw [← external] at checked
  obtain ⟨result, native, _, closed, graph, keys, memory, registry⟩ := checked
  exact step_return_verified base owner usizeBits capacity safety children data rows source request debug before (.error fault) other expected
    result native closed graph keys memory registry valid (by intro _ impossible; cases impossible)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
