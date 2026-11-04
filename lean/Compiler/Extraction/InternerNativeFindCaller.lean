/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeInsertionSource
import Compiler.Extraction.InternerNativeFrameInduction
import Compiler.Extraction.InternerCallerProduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive

attribute [local irreducible] NativeRecursion.unfold

/-- The actual native caller derives its own cleanup admission. Original
source/item facts supply the reached call frame; closed finite child frames
retain it through dispatch, and native insertion/publication preserve its source.
The existing Caller.Verified conclusion retains exact result and graph agreement. -/
theorem native_find_caller (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (debug : AssemblyItem.Fields.Values) (admitted : Admitted ops.arguments)
    (typed : AssemblyItem.Initializers.DebugTyped debug) (depth : Nat)
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
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
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory)) :
    let nativeBase := callerContext ops allocate safety owner meaning base growth
    let nativeChildren := NativeRecursion.unfold nativeBase owner usizeBits depth
    let actual := (context nativeBase owner usizeBits nativeChildren debug).primitives source address native
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let input : World (Publication.Effects σ) := {before with memory := {before.memory with memory}}
    Caller.Verified nativeBase.external base.allocator source request.arguments
      (Caller.findBody nativeBase.external base.budget base.allocator actual base.queries source buffer request) input := by
  intro nativeBase nativeChildren actual buffer input
  have external := Publication.external_admitted ops.arguments admitted
  obtain ⟨valid, sourceReady, scratch, _⟩ := caller_buffer before.memory memory pointer source request.arguments
    facts.valid represented allocated
  apply Caller.invoke_verified nativeBase.external base.allocator source request.arguments _ input
  apply Caller.find_ready_at nativeBase.external base.budget base.allocator actual base.queries source buffer request input
    ⟨valid, sourceReady⟩ scratch external
  intro handle prepared deterministic initialized ready
  apply body_ready_at nativeBase.external base.allocator actual request deterministic handle source request.arguments prepared
    ready external
  intro reached normalized remaining key transferred keyed aligned held
  let taken : State (Publication.Effects σ) := ⟨{prepared with memory := reached}, ⟨some remaining, some normalized, false⟩⟩
  have nativeTaken : take nativeBase.external base.allocator ⟨prepared, {lookup := some handle}⟩ = (.ok (), taken) := by
    simp only [take, transferred, taken]
  obtain ⟨owned, lookup, entry⟩ := Insertion.Native.caller_input ops.arguments base.budget base.allocator source address
    request native before memory pointer handle.values ⟨prepared, {lookup := some handle}⟩ taken key
    ⟨facts.valid, represented⟩ admitted item sameItem allocated initialized nativeTaken keyed facts.live facts.unique (privateSource key)
  have sameOwned : normalized = owned := Option.some.inj (congrArg Local.slice entry.origin.scope)
  have sameLookup : remaining = lookup := Option.some.inj (congrArg Local.lookup entry.origin.scope)
  subst owned
  subst lookup
  have retained := stack.retained initial entry.origin.held.1.1 entry.origin.graph
    ⟨entry.keys, entry.origin.memory, entry.origin.registry⟩
  let predicate := CallFrame safety base.allocator owner rows source request.arguments normalized address native parent
  have frame : predicate taken.world := CallFrame.caller entry facts privateSource array parent retained
  have takenFacts := facts.frame entry.origin.held.1.1
    (by rw [entry.origin.graph]; exact facts.projected)
    (congrArg Interner.Heap.table entry.origin.graph) entry.keys
    (fun id cell found _ => entry.origin.memory id cell found) entry.origin.registry
  have children := stack.unfold_frames ops allocate safety owner usizeBits base growth meaning debug depth rows source
    request.arguments normalized address native parent admitted typed
  have simplified := dispatcher_keeps nativeBase owner usizeBits nativeChildren debug source address native key normalized
    predicate taken.world frame (by
      rw [takenFacts.reads]
      simpa only [Interner.representativeReads, takenFacts.projected] using children)
  apply miss_post_at nativeBase.external base.allocator actual source request.arguments request key normalized remaining deterministic
    taken.world predicate frame held
  · exact fun completed => ⟨simplified completed, (simplified completed).1.2⟩
  · intro id world _ live completed
    have published := Publication.publish_held ops.probe ops.arguments base.allocator source request.arguments key normalized id world live completed
    exact ⟨published.1, fun _ _ => published.2.1⟩
  · intro world live _ completed
    exact live.insertion_source ops allocate growth meaning key deterministic admitted aligned domain completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
