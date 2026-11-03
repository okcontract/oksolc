/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorNativeReturn
import Compiler.Extraction.InternerCallerInsertionAllocationFailure
import Compiler.Extraction.InternerCallerInsertionEmptyGrowthFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Insertion Insertion.Native

/-- One actual constant call: initial native graph and prefix observations,
permitted create/backing responses, derived ownership cleanup, then both local
returns. There is no final-native-invariant or whole-constructor premise. -/
theorem constant_growing_empty_oom (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (safety : Bool)
    (budget allocator owner oldBacking oldCapacity capacity context returnAddress base : Nat)
    (source : View) (meaning : Meaning) (seed : Primitives (Publication.Effects σ))
    (q : Caller.Queries) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ)) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (values : List NodeId) (prepared taken : State (Publication.Effects σ))
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle) (rows : List Storage.Cell)
    (facts : NativeGraph.Facts safety allocator owner ⟨oldBacking, 0⟩ oldCapacity before rows)
    (reads : before.graph.read = Storage.readValue rows)
    (admitted : Admitted ops.arguments) (item : Prepared request.item debug before constructed)
    (entry : CallerInput allocator source address request values (input request.item debug) key constructed taken normalized lookup)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : q.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external ops.arguments) budget allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (classified : q.deterministic request.item = .ok true) (keyed : Interner.makeKey request values = .ok key)
    (missed : constructed.graph.table key = none)
    (transferred : take (Publication.external ops.arguments) allocator prepared = (.ok (), taken))
    (kind : request.item.kind = 2) (empty : normalized.items = [])
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength rows.length)
    (selected : capacity = Capacity.grow (Append.nextLength rows.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (count : rows.length < 2 ^ 32 - 1)
    (createEffects allocationEffects : σ)
    (createResponse : ops.create AssemblyItem.Creation.layout (Publication.forget taken.world.memory) = (some base, createEffects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits taken.world.memory.memory AssemblyItem.Creation.layout base)
    (allocation : ∀ installed,
      AssemblyClone.NativeFields.install (input request.item debug) taken.world.memory.memory.nextId
        (AssemblyItem.Creation.create (observe ops.create) allocator request.item taken.world.memory).2 = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (none, allocationEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    ∃ after,
      let reached := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId
        { taken.world with memory := Insertion.memory after }
      Native.execution ops allocate safety allocator owner source address meaning (input request.item debug) key normalized true
        rows taken.world (some growth) =
        ((.ok (some .allocationFailure), (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership), after) ∧
      invoke (Publication.external ops.arguments) budget allocator
        (fun address native => callerPrimitives ops allocate safety allocator owner source address meaning native seed (some growth))
        q source request debug before = (.error (.language .outOfMemory), ⟨reached, ⟨none, some normalized, true⟩⟩) ∧
      NativeGraph.Facts safety allocator owner ⟨oldBacking, 0⟩ oldCapacity reached rows ∧
      reached.graph = before.graph ∧ reached.memory.effects.keys = before.memory.effects.keys ∧
      (∀ id native, before.memory.memory.heap.lookup id = some native → reached.memory.memory.heap.lookup id = some native) ∧
      (∀ id block, before.memory.heap id = some block → reached.memory.heap id = some block) := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  have constructedFacts : NativeGraph.Facts safety allocator owner ⟨oldBacking, 0⟩ oldCapacity constructed rows :=
    facts.frame item.valid (by rw [item.graph]; exact facts.projected)
      (congrArg Interner.Heap.table item.graph) (congrArg Publication.Effects.keys item.effects)
      (fun id cell found _ => item.memory id cell found) (fun id block found => item.heap.symm ▸ found)
  obtain ⟨ownerCell, found, typed, _⟩ := facts.ownerLive
  have constructedLock := (Owner.NativeLock.checkHeader_eq_of_lookup safety before.memory.memory constructed.memory.memory
    owner ownerCell item.valid.memory found typed ((item.memory owner ownerCell found).trans found.symm)).trans unlocked
  obtain ⟨after, ran, valid, _, _, keys, native, registry, _⟩ := entry.growing_empty_oom ops allocate freeBacking safety
    allocator owner oldBacking oldCapacity capacity context returnAddress base source address meaning request values
    (input request.item debug) key normalized lookup constructed taken rows constructedFacts admitted empty rfl oldNonempty full
    selected size count createEffects allocationEffects createResponse fits allocation constructedLock
  have graph : taken.world.graph = before.graph := entry.origin.graph.trans item.graph
  have takenReads : taken.world.graph.read = Storage.readValue rows := by rw [graph]; exact reads
  obtain ⟨constructedOwner, constructedFound, _, _⟩ := constructedFacts.ownerLive
  have inserted := entry.insert_allocation_failure ops allocate safety allocator owner source address meaning request values
    (input request.item debug) key normalized lookup constructed taken rows (some growth) constructedOwner ⟨oldBacking, 0⟩
    constructedFound (readHeader_items _ _ _ _ constructedFacts.header)
    (by rw [graph]; exact facts.projected) takenReads after ran
  have routed := invoke_native_constant ops allocate safety budget allocator owner source meaning seed (some growth) q request debug
    before constructed address pointer memory values prepared taken key normalized lookup entry made room allocated initialized
    classified keyed missed transferred kind
  rw [inserted] at routed
  let reached := returnWorld before.memory.memory.nextId constructed.memory.memory.nextId
    { taken.world with memory := Insertion.memory after }
  have finalValid : Valid reached.memory := returnWorld_valid _ _ _ valid
  have finalFrame : ∀ id cell, before.memory.memory.heap.lookup id = some cell → reached.memory.memory.heap.lookup id = some cell :=
    returnWorld_frame before _ constructed.memory.memory.nextId facts.valid (by rw [item.nextId]; omega)
      (fun id cell found => native id cell (item.memory id cell found))
  have finalRegistry : ∀ id block, before.memory.heap id = some block → reached.memory.heap id = some block :=
    fun id block found => registry id block (item.heap.symm ▸ found)
  have finalKeys : reached.memory.effects.keys = before.memory.effects.keys :=
    keys.trans (congrArg Publication.Effects.keys item.effects)
  exact ⟨after, ran, routed,
    facts.frame finalValid (by change taken.world.graph.representatives = some rows; rw [graph]; exact facts.projected)
      (congrArg Interner.Heap.table graph) finalKeys (fun id cell found _ => finalFrame id cell found) finalRegistry,
    graph, finalKeys, finalFrame, finalRegistry⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem
