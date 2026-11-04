/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFindCaller
import Compiler.Extraction.InternerNativeFindWords

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive

/-- The same raw native find body and actual deferred cleanup now satisfy the
existing combined ownership and word contract. Closed finite replay and frame
induction supply child correctness; native entry admission remains explicit. -/
theorem production_find_verified (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (env : AddressMask.Environment) (other : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (debug : AssemblyItem.Fields.Values) (seed : Interner.Primitives) (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : ∀ item, base.queries.deterministic item = Interner.Queries.queries.deterministic item)
    (capacityQuery : ∀ heap cursor, seed.atCapacity {heap with allocationCursor := cursor} = base.queries.atCapacity heap)
    (classificationQuery : ∀ item, seed.deterministic item = base.queries.deterministic item)
    (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other)
    (depth : Nat) (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (stack : Enclosing safety base.allocator owner parent)
    (source : View) (request : Interner.Request) (before : World (Publication.Effects σ))
    (initial : parent before) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (item : AssemblyClone.NativeFields.Represents before.memory.memory address native)
    (sameItem : native.item = request.item)
    (domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph) (expected : Word)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected) :
    let nativeBase := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth
    let nativeChildren := NativeRecursion.unfold nativeBase owner usizeBits depth
    let actual := (context nativeBase owner usizeBits nativeChildren debug).primitives source address native
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := {before with memory := {before.memory with memory}}
    Semantic.Verified nativeBase.external base.allocator source request.arguments (Dispatch.wordDispatchMeaning env other)
      (Caller.findBody nativeBase.external base.budget base.allocator actual base.queries source buffer request) input
      (fun id after => after.read id = some expected) := by
  intro nativeBase nativeChildren actual buffer input
  refine ⟨native_find_caller ops allocate safety owner usizeBits (Dispatch.wordDispatchMeaning env other) base growth debug
    admitted typed depth rows parent stack source request before initial data capacity facts represented privateSource array
    address native item sameItem domain memory pointer allocated, ?_⟩
  exact AllocationTrace.native_find_words ops allocate safety owner usizeBits env other base growth debug seed mismatch
    admitted typed closedQuery capacityQuery classificationQuery pushes pushValues depth rows parent stack source request before
    initial data capacity facts represented privateSource array address native item sameItem memory pointer allocated valid expected evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
