/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorNativeReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Compose a proved caller outcome with its actual item/scratch return. The
callee supplies its local postcondition; existing Prepared facts are reused,
without repeating item preparation or assuming the constructor's final frame. -/
theorem invoke_return_verified (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (result : Except Fault NodeId) (done : State σ)
    (good : Good source request.arguments before) (item : Prepared request.item debug before constructed)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (completed : ordinary result = true)
    (routed : Caller.find external budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } = (result, done))
    (closedGood : Good source request.arguments done.world) (closed : Closed done.scope)
    (graph : done.world.graph = constructed.graph)
    (native : ∀ id cell, constructed.memory.memory.heap.lookup id = some cell → done.world.memory.memory.heap.lookup id = some cell)
    (registry : ∀ id block, constructed.memory.heap id = some block → done.world.memory.heap id = some block) :
    let actual := invoke external budget allocator p q source request debug before
    actual.1 = result ∧ Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) := by
  have invoked := invoke_after_scratch external budget allocator p q source request debug before constructed address pointer memory
    made room allocated
  rw [routed] at invoked
  dsimp only
  rw [invoked]
  simp only [completed, ↓reduceIte]
  have frame := returnWorld_frame before done.world constructed.memory.memory.nextId good.1
    (by rw [item.nextId]; omega) (fun id cell found => native id cell (item.memory id cell found))
  exact ⟨trivial, good_frame _ _ source request.arguments good
      (returnWorld_valid _ _ done.world closedGood.1) frame,
    closed, graph.trans item.graph, frame,
    fun id block found => registry id block (item.heap.symm ▸ found)⟩

/-- Returning the two constructor-local frames preserves the exact caller
effects, whether the caller completes ordinarily or rejects. -/
theorem invoke_after_scratch_effects (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory)) :
    (invoke external budget allocator p q source request debug before).2.world.memory.effects =
      (Caller.find external budget allocator (p address (input request.item debug)) q source
        ⟨constructed.memory.memory.nextId, 0, 2⟩ request
        { constructed with memory := { constructed.memory with memory } }).2.world.memory.effects := by
  rw [invoke_after_scratch _ _ _ _ _ _ _ _ _ _ _ _ _ made room allocated]
  generalize Caller.find external budget allocator (p address (input request.item debug)) q source
    ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    { constructed with memory := { constructed.memory with memory } } = ran
  rcases ran with ⟨result, reached⟩
  cases completed : ordinary result <;> simp only [completed, Bool.false_eq_true, ↓reduceIte] <;> rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
