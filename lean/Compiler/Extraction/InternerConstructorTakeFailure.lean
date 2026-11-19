/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTakeFailure
import Compiler.Extraction.InternerConstructorReturnedFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Ordinary take failure composes the actual initialized caller with the
shared constructor return. The exact reached world is retained apart from the
two local frames; allocation effects are not rewound. -/
theorem invoke_take_failed (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared reached : State σ) (fault : Fault) (key : Key) (deterministic : Bool)
    (good : Good source request.arguments before) (admitted : Admitted external)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok deterministic)
    (keyed : Interner.makeKey request values = .ok key)
    (missed : deterministic = true → constructed.graph.table key = none)
    (failed : take external allocator prepared = (.error fault, reached)) :
    let actual := invoke external budget allocator p q source request debug before
    fault = .language .outOfMemory ∧ actual.1 = .error fault ∧
      actual.2.world = returnWorld before.memory.memory.nextId constructed.memory.memory.nextId reached.world ∧
      Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  have item := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  obtain ⟨done, oom, finished, same, closedGood, closed, graph, native, registry, normalized⟩ :=
    Caller.finish_take_failed external budget allocator source request constructed memory pointer values prepared reached fault
      (good_frame _ _ source request.arguments good item.valid item.memory) admitted allocated initialized failed
  subst fault
  have routed := Caller.find_take_failed external budget allocator (p address (input request.item debug)) q source
    ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    { constructed with memory := { constructed.memory with memory } } values prepared reached (.language .outOfMemory)
    key deterministic room initialized classified keyed missed failed
  obtain ⟨result, afterGood, closed, graph, native, registry⟩ := invoke_return_verified
    external budget allocator p q source request debug before constructed address pointer memory (.error (.language .outOfMemory)) done
    good item made room allocated rfl (routed.trans finished) closedGood closed graph native registry
  have invoked := invoke_after_scratch external budget allocator p q source request debug before constructed address pointer memory
    made room allocated
  rw [routed, finished] at invoked
  simp only [ordinary, Fault.recoverable, ↓reduceIte] at invoked
  refine ⟨rfl, result, ?_, afterGood, closed, graph, native, registry, normalized⟩
  rw [invoked, same]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
