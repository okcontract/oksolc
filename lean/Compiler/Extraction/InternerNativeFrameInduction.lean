/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingConstructorFrames
import Compiler.Extraction.InternerNativeSourceInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray Recursive

variable (ops : Insertion.Operations σ) (allocate : RepresentativeArray.Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (RepresentativeArray.Growth.Registered.Callbacks σ)) (meaning : Meaning)
    (debug : AssemblyItem.Fields.Values)

local notation "nativeBase" => callerContext ops allocate safety owner meaning base growth

/-- All five actual finite constructors preserve every enclosing live call.
Induction is on the native unfolding depth, with the next enclosing frame
introduced at the reached child entry. Query-selected borrowed/local inputs
derive their native admission from the retained row prefix. This proves frames
on ordinary outcomes; it does not assert termination or resource/word replay. -/
theorem Enclosing.unfold_frames (depth : Nat) (rows : List Storage.Cell)
    (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug) :
    (keeping (CallFrame safety base.allocator owner rows source values normalized address native parent)).SourceConstructorsAt
      (Nested.storageReads rows) debug (unfold nativeBase owner usizeBits depth) (unfold nativeBase owner usizeBits depth) := by
  induction depth generalizing rows source values normalized address native parent with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro opcode ids tag before initial completed
      cases completed
    · intro value tag before initial completed
      cases completed
    · intro id value tag before initial completed
      cases completed
    · intro id queried slice found opcode tag before initial completed
      cases completed
    · intro id opcode slice found shape selected bound repeated first tag before initial completed
      cases completed
  | succ depth ih =>
    let frame := CallFrame safety base.allocator owner rows source values normalized address native parent
    have nested : Enclosing safety base.allocator owner frame := .call stack
    have proper (childRows : List Storage.Cell) (childSource : View) (request : Interner.Request)
        (before : World (Publication.Effects σ)) :
        ProperFrames safety owner nativeBase (unfold nativeBase owner usizeBits depth)
          childSource request debug before childRows frame := by
      intro site reached guard
      exact ih childRows childSource request.arguments site.normalized site.address (input request.item debug) frame nested
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro opcode ids tag before initial completed
      obtain ⟨added, data, capacity, facts, _⟩ := initial.1.1
      have post := nested.operation_frame ops allocate safety owner usizeBits base growth meaning
        (unfold nativeBase owner usizeBits depth) debug (rows ++ added) frame opcode ids before initial data capacity facts admitted typed
        (fun childSource prepared _ _ => proper (rows ++ added) childSource _ prepared)
      exact (post completed).2
    · intro value tag before initial completed
      obtain ⟨added, data, capacity, facts, _⟩ := initial.1.1
      have post := nested.constant_frame ops allocate safety owner usizeBits base growth meaning
        (unfold nativeBase owner usizeBits depth) debug (rows ++ added) frame value before initial data capacity facts admitted typed
      exact (post completed).2
    · intro id value tag before initial completed
      obtain ⟨added, data, capacity, facts, _⟩ := initial.1.1
      have post := nested.materialize_frame ops allocate safety owner usizeBits base growth meaning
        (unfold nativeBase owner usizeBits depth) debug (rows ++ added) frame id value before initial data capacity facts admitted typed
      exact (post completed).2
    · intro id queried slice found opcode tag before initial completed
      obtain ⟨added, data, capacity, facts, _⟩ := initial.1.1
      obtain ⟨represented, privateSource, array⟩ := facts.source_after_append rows added id queried slice found
      have post := nested.invocation_frame ops allocate safety owner usizeBits base growth meaning debug (rows ++ added) frame
        (unfold nativeBase owner usizeBits depth) (view slice) (Interner.constructorCode.operationRequest opcode slice.items)
        before initial data capacity facts represented privateSource array
        (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted typed
        (proper (rows ++ added) (view slice) _ before)
      exact (post completed).2.2
    · intro id opcode slice found shape selected bound repeated first tag before initial completed
      obtain ⟨added, data, capacity, facts, _⟩ := initial.1.1
      obtain ⟨represented, _, _⟩ := facts.source_after_append rows added id opcode slice found
      have post := nested.local_frame ops allocate safety owner usizeBits base growth meaning
        (unfold nativeBase owner usizeBits depth) debug (rows ++ added) frame opcode slice selected repeated first before
        initial data capacity facts represented (by intro _; simpa only [shape] using bound) admitted typed
        (fun childSource prepared _ _ => proper (rows ++ added) childSource _ prepared)
      exact (post completed).2

/-- The actual all-entry native invocation consumes the proved finite frame
induction. No proper-child frame, logical model or word premise remains here. -/
theorem Enclosing.unfold_invocation_frame (depth : Nat) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop) (source : View) (request : Interner.Request)
    (before : World (Publication.Effects σ)) (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug) :
    FramePost (GraphFrame safety base.allocator owner rows parent)
      (invoke (nativeBase).external base.budget base.allocator
        ((context nativeBase owner usizeBits (unfold nativeBase owner usizeBits depth) debug).primitives source)
        base.queries source request debug before) := by
  apply stack.invocation_frame ops allocate safety owner usizeBits base growth meaning debug rows parent
    (unfold nativeBase owner usizeBits depth) source request before initial data capacity facts
    represented privateSource array domain admitted typed
  intro site reached guard
  exact stack.unfold_frames ops allocate safety owner usizeBits base growth meaning debug depth rows source request.arguments
    site.normalized site.address (input request.item debug) parent admitted typed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
