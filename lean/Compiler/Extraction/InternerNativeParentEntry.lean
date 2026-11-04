/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Allocation-only prefixes preserve the live call through the existing
native and registry frames. Source offsets, empty sentinels and current keys
remain unrestricted. The separate outer predicate keeps its own prefix law. -/
theorem CallFrame.frame
    {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before after : World (Publication.Effects σ)}
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    (valid : Valid after.memory) (graph : after.graph = before.graph)
    (keys : after.memory.effects.keys = before.memory.effects.keys)
    (memory : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      after.memory.memory.heap.lookup id = some cell)
    (registry : ∀ id block, before.memory.heap id = some block → after.memory.heap id = some block)
    (outer : parent after) :
    CallFrame safety allocator owner rows source values normalized address native parent after := by
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := initial.1.1
  have kept := facts.frame valid (by rw [graph]; exact facts.projected)
    (congrArg Interner.Heap.table graph) keys (fun id cell found _ => memory id cell found) registry
  have live : SliceValid allocator after.memory.heap normalized := by
    rcases custody.live with empty | stored
    · exact Or.inl empty
    · exact Or.inr (registry _ _ stored)
  obtain ⟨item, found⟩ := initial.2.1.live
  exact ⟨⟨⟨added, data, capacity, kept,
      ⟨⟨live, by rw [keys]; exact custody.apart⟩, custody.operands⟩,
      by rw [keys]; exact privateSource⟩,
    good_frame before after source values initial.1.2.1 valid memory, live, initial.1.2.2.2⟩,
    initial.2.1.frame ((memory _ item found).trans found.symm), outer,
    initial.arraySource.frame (fun _ cell found => memory _ cell found)⟩

/-- Actual child item allocation and initialization retain the enclosing
input and item. The existing constructor preparation supplies every frame. -/
theorem CallFrame.prepared
    {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before after : World (Publication.Effects σ)}
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    {item : Item} {debug : AssemblyItem.Fields.Values}
    (prepared : Prepared item debug before after) (outer : parent after) :
    CallFrame safety allocator owner rows source values normalized address native parent after :=
  initial.frame prepared.valid prepared.graph (congrArg Publication.Effects.keys prepared.effects)
    prepared.memory (fun _ _ found => prepared.heap ▸ found) outer

/-- Literal preparation uses the same frame, including the empty no-allocation
case. Evaluation of the literal's elements remains the caller's obligation. -/
theorem CallFrame.arguments
    {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before after : World (Publication.Effects σ)}
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    {arguments : List NodeId} {literal : View}
    (prepared : Arguments.Prepared arguments before literal after) (outer : parent after) :
    CallFrame safety allocator owner rows source values normalized address native parent after :=
  initial.frame prepared.good.1 prepared.graph (congrArg Publication.Effects.keys prepared.effects)
    prepared.frame (fun _ _ found => prepared.heap ▸ found) outer

/-- Initial item and borrow facts come from the actual take boundary. Only the
separate parent predicate needs a prefix frame theorem at its owning layer. -/
theorem CallFrame.caller {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {request : Interner.Request}
    {native : AssemblyClone.NativeFields.ItemValue} {key : Key} {lookup : Handle}
    {constructed : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
    (entry : Insertion.Native.CallerInput allocator source address request values native key constructed taken normalized lookup)
    (facts : NativeGraph.Facts safety allocator owner data capacity constructed rows)
    (privateSource : Caller.SourcePrivate source constructed.memory.effects.keys)
    (array : ArraySource source constructed.memory.memory)
    (parent : World (Publication.Effects σ) → Prop) (kept : parent taken.world) :
    CallFrame safety allocator owner rows source request.arguments normalized address native parent taken.world :=
  ⟨InputFrame.caller entry facts privateSource, entry.item, kept,
    array.frame (fun _ cell found => entry.origin.memory _ cell found)⟩

/-- Scratch allocation, normalization and take retain the concrete enclosing
call through the child's original origin. No reached parent frame is assumed. -/
theorem CallFrame.caller_parent
    {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {rows parentRows : List Storage.Cell} {source parentSource : View}
    {request : Interner.Request} {values parentValues : List NodeId}
    {normalized parentNormalized : ArgumentSlice} {lookup : Handle} {key : Key}
    {address parentAddress : Compiler.ZigAir.Memory.Address}
    {native parentNative : AssemblyClone.NativeFields.ItemValue}
    {outer : World (Publication.Effects σ) → Prop}
    {constructed : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
    (entry : Insertion.Native.CallerInput allocator source address request values native key constructed taken normalized lookup)
    (facts : NativeGraph.Facts safety allocator owner data capacity constructed rows)
    (privateSource : Caller.SourcePrivate source constructed.memory.effects.keys)
    (array : ArraySource source constructed.memory.memory)
    (initial : CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized
      parentAddress parentNative outer constructed)
    (outerKept : outer taken.world) :
    CallFrame safety allocator owner rows source request.arguments normalized address native
      (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer)
      taken.world :=
  CallFrame.caller entry facts privateSource array _
    (initial.frame entry.origin.held.1.1 entry.origin.graph entry.keys entry.origin.memory entry.origin.registry outerKept)

/-- Successful item/scratch/normalization/take observations establish both the
child's induction frame and its live enclosing call. The original child origin
is retained at the constructed world for later publication and cleanup proofs.
Only the next outer predicate's prefix law remains explicit. -/
theorem CallFrame.enter_child
    {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {rows parentRows : List Storage.Cell} {parentSource : View} {parentValues : List NodeId}
    {parentNormalized : ArgumentSlice} {parentAddress : Compiler.ZigAir.Memory.Address}
    {parentNative : AssemblyClone.NativeFields.ItemValue} {outer : World (Publication.Effects σ) → Prop}
    (host : External σ) (budget : Nat) (source : View) (request : Interner.Request)
    (debug : AssemblyItem.Fields.Values) (before constructed : World (Publication.Effects σ))
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId)
    (prepared taken : State (Publication.Effects σ)) (key : Key)
    (facts : NativeGraph.Facts safety allocator owner data capacity before rows)
    (initial : CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized
      parentAddress parentNative outer before)
    (good : Good source request.arguments before)
    (array : ArraySource source before.memory.memory)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug) (admitted : Admitted host)
    (made : prepare request.item debug before = (.ok address, constructed))
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (Publication.external host) budget allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : take (Publication.external host) allocator prepared = (.ok (), taken))
    (keyed : Interner.makeKey request values = .ok key)
    (constructedOuter : outer constructed)
    (outerKept : outer taken.world) :
    Prepared request.item debug before constructed ∧
      CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized
        parentAddress parentNative outer constructed ∧
      ∃ normalized lookup,
        Insertion.Native.CallerInput allocator source address request values (input request.item debug) key
          constructed taken normalized lookup ∧
        CallFrame safety allocator owner rows source request.arguments normalized address (input request.item debug)
          (CallFrame safety allocator owner parentRows parentSource parentValues parentNormalized parentAddress parentNative outer)
          taken.world := by
  have post := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
  obtain ⟨normalized, lookup, entry⟩ := caller_input host budget allocator source request debug before constructed
    address memory pointer values prepared taken key good domain typed admitted made allocated initialized transferred keyed
    facts.live facts.unique (privateSource key)
  have constructedFacts := facts.frame post.valid (by rw [post.graph]; exact facts.projected)
    (congrArg Interner.Heap.table post.graph) (congrArg Publication.Effects.keys post.effects)
    (fun id cell found _ => post.memory id cell found) (fun _ _ found => post.heap ▸ found)
  have parentConstructed := initial.prepared post constructedOuter
  have ready := CallFrame.caller_parent entry constructedFacts
    (by rw [post.effects]; exact privateSource)
    (array.frame (fun _ cell found => post.memory _ cell found)) parentConstructed outerKept
  exact ⟨post, parentConstructed, normalized, lookup, entry, ready⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
