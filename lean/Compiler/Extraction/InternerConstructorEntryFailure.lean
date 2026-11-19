/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitFailure
import Compiler.Extraction.InternerConstructorNativeReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- A failed initializer has no live lookup owner on an ordinary result.
Retire only the reached scratch/item locals; retain the allocation attempt's
effects and derive the complete original storage frame. -/
theorem invoke_init_failed (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (fault : Fault) (reached : State σ)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (failed : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.error fault, reached))
    (completed : ordinary (.error fault : Except Fault NodeId) = true) :
    let actual := invoke external budget allocator p q source request debug before
    actual.1 = .error fault ∧
      actual = (.error fault, { reached with world := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world }) ∧
      Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) := by
  have item := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  have constructedGood := good_frame _ _ source request.arguments good item.valid item.memory
  obtain ⟨scratchValid, represented, scratch, kept⟩ := caller_buffer constructed.memory memory pointer source request.arguments
    constructedGood.1 constructedGood.2 allocated
  obtain ⟨failedGood, scope, graph, sameMemory, sameRegistry⟩ := Caller.initialize_failed external budget allocator
    source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    { constructed with memory := { constructed.memory with memory } } fault reached ⟨scratchValid, represented⟩
    scratch admitted failed completed
  have finished : OwnedCall.finish external allocator (.error fault : Except Fault NodeId) reached = (.error fault, reached) := by
    simp only [OwnedCall.finish, completed, ↓reduceIte, cleanup, scope, Bool.false_eq_true, deinit]
  have routed := invoke_after_scratch external budget allocator p q source request debug before constructed address pointer memory
    made room allocated
  rw [Caller.find_init_failed external budget allocator (p address (input request.item debug)) q source
    ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    { constructed with memory := { constructed.memory with memory } } fault reached room failed, finished] at routed
  simp only [completed, ↓reduceIte] at routed
  dsimp only
  rw [routed]
  have prior : ∀ id cell, before.memory.memory.heap.lookup id = some cell → reached.world.memory.memory.heap.lookup id = some cell := by
    intro id cell found
    rw [sameMemory]
    exact kept id cell (item.memory id cell found)
  have frame := returnWorld_frame before reached.world constructed.memory.memory.nextId good.1
    (by rw [item.nextId]; omega) prior
  exact ⟨rfl, rfl, good_frame _ _ source request.arguments good (returnWorld_valid _ _ _ failedGood.1) frame,
    by rw [scope]; exact ⟨rfl, Or.inr rfl⟩, graph.trans item.graph, frame,
    fun id block found => by change reached.world.memory.heap id = some block; rw [sameRegistry, item.heap]; exact found⟩

theorem invoke_capacity_failed (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (good : Good source request.arguments before)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (full : q.atCapacity constructed.graph = true) :
    let actual := invoke external budget allocator p q source request debug before
    actual = (.error (.language .capacity), ⟨{ constructed with memory := { constructed.memory with
        memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId constructed.memory.memory } }, { lookup := none }⟩) ∧
      Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧ actual.2.world.memory.effects = before.memory.effects ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) := by
  have item := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  dsimp only
  rw [invoke_prepared _ _ _ _ _ _ _ _ _ _ _ made]
  simp only [ConstructorFrame.find, full, ↓reduceIte, ordinary, Fault.recoverable]
  have frame : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      (Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId constructed.memory.memory).heap.lookup id = some cell := by
    intro id cell found
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id
      (Compiler.ZigAir.Memory.valid_lookup _ _ _ good.1.memory found).1).trans (item.memory id cell found)
  exact ⟨trivial, good_frame _ _ source request.arguments good (Valid.cleanup _ item.valid _) frame,
    ⟨rfl, Or.inr rfl⟩, item.graph, item.effects, frame, fun id block found => item.heap.symm ▸ found⟩

/-- Suspended or rejected initialization retains the complete reached state.
It does not acquire an ordinary result or trigger either local unwind. -/
theorem invoke_init_rejected (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (fault : Fault) (reached : State σ)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (failed : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.error fault, reached))
    (rejected : ordinary (.error fault : Except Fault NodeId) = false) :
    invoke external budget allocator p q source request debug before = (.error fault, reached) := by
  rw [invoke_after_scratch _ _ _ _ _ _ _ _ _ _ _ _ _ made room allocated,
    Caller.find_init_failed external budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } fault reached room failed,
    finish_semantic _ _ _ _ rejected]
  simp only [rejected, Bool.false_eq_true, ↓reduceIte]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
