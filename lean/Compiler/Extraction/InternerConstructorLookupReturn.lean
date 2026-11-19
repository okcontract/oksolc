/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitializedCleanup
import Compiler.Extraction.InternerConstructorReturnedFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Return any ordinary initialized lookup result through the actual normalizer,
scratch and item cleanup. The local routing equation is supplied by an entry
branch; no final ownership, native frame or callback contract is assumed. -/
theorem invoke_initialized_verified (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State σ) (result : Except Fault NodeId)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (completed : ordinary result = true)
    (routed : Caller.find external budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } = OwnedCall.finish external allocator result prepared) :
    let actual := invoke external budget allocator p q source request debug before
    actual.1 = result ∧ Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  have item := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  obtain ⟨done, finished, closedGood, closed, graph, native, registry, normalized⟩ :=
    Caller.finish_initialized external budget allocator source request constructed memory pointer values prepared
      result (good_frame _ _ source request.arguments good item.valid item.memory)
      admitted allocated initialized completed
  obtain ⟨resultEq, good, closed, graph, native, registry⟩ := invoke_return_verified
    external budget allocator p q source request debug before constructed address pointer memory result done good item
    made room allocated completed (routed.trans finished) closedGood closed graph native registry
  exact ⟨resultEq, good, closed, graph, native, registry, normalized⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
