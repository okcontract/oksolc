/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorCacheHit
import Compiler.Extraction.InternerNativeLookupReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- The cache-hit entry preserves the scoped native graph invariant through
actual preparation and cleanup. Full prior allocation/registry retention is
derived, so callers can retain their own live parent without a final frame premise.
The exact key table is preserved even if normalization releases a temporary. -/
theorem invoke_cached_native (host : External σ) (budget allocator owner capacity : Nat) (safety : Bool)
    (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects σ))
    (q : Caller.Queries) (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State (Publication.Effects σ)) (key : Key) (id : NodeId)
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments) (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok true)
    (keyed : Interner.makeKey request values = .ok key) (found : constructed.graph.table key = some id) :
    let actual := invoke (Publication.external host) budget allocator p q source request debug before
    actual.1 = .ok id ∧ NativeGraph.Facts safety allocator owner data capacity actual.2.world rows ∧
      Good source request.arguments actual.2.world ∧ Closed actual.2.scope ∧
      actual.2.world.graph = before.graph ∧ actual.2.world.memory.effects.keys = before.memory.effects.keys ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → actual.2.world.memory.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → actual.2.world.memory.heap id = some block) ∧
      normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values := by
  exact invoke_initialized_native host budget allocator owner capacity safety data rows p q source request debug
    before constructed address pointer memory values prepared (.ok id) facts represented admitted domain typed made room allocated
    initialized rfl (Caller.find_cached (Publication.external host) budget allocator (p address (input request.item debug)) q source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      { constructed with memory := { constructed.memory with memory } } values prepared key id room initialized classified keyed found)

/-- The cached ID denotes the requested word because the actual normalization
and key construction select that cache entry. No logical callback contract or
new graph value is assumed. -/
theorem cached_word (other : Meaning) (request : Interner.Request) (values : List NodeId)
    (key : Key) (id : NodeId) (before : Interner.Heap) (expected : Word)
    (valid : Interner.Invariant (Folding.wordMeaning other) before)
    (normalized : normalizeCode.run InsertionSort.sortIds request.item request.arguments = some values)
    (keyed : Interner.makeKey request values = .ok key) (found : before.table key = some id)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.read request.arguments request.sequence = some expected) :
    before.read id = some expected := by
  have normalizedValue := (Compiler.Extraction.InsertionSort.normalize_word other request.item request.arguments
    values before.read request.sequence normalized).trans evaluated
  have keyValue := Interner.makeKey_sound _ _ _ _ _ _ normalizedValue keyed
  obtain ⟨cached, cachedKey, cachedId⟩ := valid.cache key id found
  have same : cached = expected := Option.some.inj (cachedKey.symm.trans keyValue)
  exact same ▸ cachedId

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

/-- A cache hit is a leaf of the proper-child step for arbitrary children. Its
native graph, live original allocations, closed ownership and word result follow
from the actual entry prefix; no child simulation or insertion contract is needed. -/
theorem step_cached_verified (base : PairInput.Context (Publication.Effects σ))
    (host : External σ) (owner usizeBits capacity : Nat) (safety : Bool)
    (children : Constructors (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared : State (Publication.Effects σ)) (key : Key) (id : NodeId)
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
    (classified : base.queries.deterministic request.item = .ok true)
    (keyed : Interner.makeKey request values = .ok key) (found : constructed.graph.table key = some id)
    (valid : Interner.Invariant (Folding.wordMeaning other) before.graph)
    (evaluated : request.item.eval (Folding.wordMeaning other) before.graph.read request.arguments request.sequence = some expected) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    actual.1 = .ok id ∧
      Returns (GraphFrame safety base.allocator owner rows (Retains before)) actual (.ok id) before.graph ∧
      Semantic.Ensures (Folding.wordMeaning other) before.graph actual.1 actual.2.world.graph
        (fun id after => after.read id = some expected) ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
          (.ok id, actual.2.world)) := by
  have routed := Caller.find_cached base.external base.budget base.allocator
    ((context base owner usizeBits children debug).primitives source address (input request.item debug)) base.queries source
    ⟨constructed.memory.memory.nextId, 0, 2⟩ request
    { constructed with memory := { constructed.memory with memory } } values prepared key id room initialized classified keyed found
  have item := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
  exact step_initialized_verified base host owner usizeBits capacity safety children data rows source request debug
    before constructed address pointer memory values prepared (.ok id) other expected external facts represented admitted
    domain typed made room allocated initialized rfl routed valid (by
      intro normalized result same
      cases same
      exact cached_word other request values key id before.graph expected valid normalized keyed
        (by simpa only [item.graph] using found) evaluated)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
