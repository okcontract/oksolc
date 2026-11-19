/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorLookupReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Ordinary classification failure returns through the same initialized cleanup
as a cache hit, without calling take, recursive children or insertion. -/
theorem invoke_classification_failed (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State σ) (error : Interner.Error)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .error error)
    (completed : ordinary (.error (.language error) : Except Fault NodeId) = true) :
    let actual := invoke external budget allocator p q source request debug before
    actual.1 = .error (.language error) ∧ Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  exact invoke_initialized_verified external budget allocator p q source request debug before constructed address pointer memory
    values prepared (.error (.language error)) good admitted domain typed made room allocated initialized completed
    (Caller.find_classification_failed external budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } values prepared error room initialized classified)

/-- A rejected classifier retains the complete initialized state, including
any owned normalization temporary and both constructor locals. -/
theorem invoke_classification_rejected (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State σ) (error : Interner.Error)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .error error)
    (rejected : ordinary (.error (.language error) : Except Fault NodeId) = false) :
    invoke external budget allocator p q source request debug before = (.error (.language error), prepared) := by
  rw [invoke_after_scratch _ _ _ _ _ _ _ _ _ _ _ _ _ made room allocated,
    Caller.find_classification_failed external budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } values prepared error room initialized classified,
    finish_semantic _ _ _ _ rejected]
  simp only [rejected, Bool.false_eq_true, ↓reduceIte]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
