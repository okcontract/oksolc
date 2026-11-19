/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingNativeStepFrame
import Compiler.Extraction.InternerNativeConstructors

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray Recursive

/-- Only source-selected proper children must preserve the reached live call.
This is the existing all-entry frame hypothesis, with no word or model duty. -/
def ProperFrames (safety : Bool) (owner : Nat) (base : PairInput.Context (Publication.Effects σ))
    (children : Constructors (Publication.Effects σ)) (source : View) (request : Interner.Request)
    (debug : AssemblyItem.Fields.Values) (before : World (Publication.Effects σ))
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop) : Prop :=
  ∀ site : ProtocolTrace.TakenSite σ, site.Reached base source request debug before →
    (site.deterministic && (request.item.kind == 1)) = true →
    (keeping (CallFrame safety base.allocator owner rows source request.arguments site.normalized site.address
      (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children children

variable (ops : Insertion.Operations σ) (allocate : RepresentativeArray.Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (RepresentativeArray.Growth.Registered.Callbacks σ)) (meaning : Meaning)
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)

local notation "nativeBase" => callerContext ops allocate safety owner meaning base growth

/-- Literal and local wrappers share native input and enclosing-parent
preparation before the same all-entry invocation proof. -/
theorem Enclosing.prepared_frame (source : View) (request : Interner.Request)
    (before prepared : World (Publication.Effects σ))
    (ready : Arguments.Prepared request.arguments before source prepared)
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (proper : ProperFrames safety owner nativeBase children source request debug prepared rows parent) :
    FramePost (GraphFrame safety base.allocator owner rows parent)
      (invoke (nativeBase).external base.budget base.allocator
        ((context nativeBase owner usizeBits children debug).primitives source) base.queries source request debug prepared) := by
  obtain ⟨native, privateSource⟩ := prepared_input_frame (base := base) ready facts
  have kept : parent prepared := stack.retained initial ready.good.1 ready.graph
    ⟨congrArg Publication.Effects.keys ready.effects, ready.frame, fun _ _ found => ready.heap ▸ found⟩
  exact stack.invocation_frame ops allocate safety owner usizeBits base growth meaning debug rows parent children source request
    prepared kept data capacity native ready.good.2 privateSource ready.arraySource domain admitted typed proper

/-- Constants have an empty source and cannot select recursive simplification.
The complete entry proof derives native allocation and return frames. -/
theorem Enclosing.constant_frame (value : Word) (before : World (Publication.Effects σ))
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug) :
    let actual := (step nativeBase owner usizeBits children).constant value debug before
    ordinary actual.1 = true → GraphFrame safety base.allocator owner rows parent actual.2 := by
  have represented : Represents before.memory.memory ⟨0, 0, 0⟩ [] := ⟨rfl, by intro index inside; simp at inside⟩
  have privateSource : Caller.SourcePrivate ⟨0, 0, 0⟩ before.memory.effects.keys := by
    intro key old found nonempty impossible
    exact (impossible rfl).elim
  have post := stack.invocation_frame ops allocate safety owner usizeBits base growth meaning debug rows parent children
    ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) before initial data capacity facts
    represented privateSource (ArraySource.empty rfl)
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted typed
    (by intro site reached guard; simp [Interner.ConstructorCode.constantRequest] at guard)
  exact post.project

theorem Enclosing.materialize_frame (id : NodeId) (value : Word) (before : World (Publication.Effects σ))
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug) :
    let actual := (step nativeBase owner usizeBits children).materialize id value debug before
    ordinary actual.1 = true → GraphFrame safety base.allocator owner rows parent actual.2 :=
  stack.constant_frame ops allocate safety owner usizeBits base growth meaning children debug rows parent value before
    initial data capacity facts admitted typed

/-- Literal operations derive their actual source and return from the shared
wrapper decomposition. Only proper-child frame laws remain at reached entries. -/
theorem Enclosing.operation_frame (opcode : Opcode) (values : List NodeId) (before : World (Publication.Effects σ))
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (proper : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      Arguments.Prepared values before source prepared →
      ProperFrames safety owner nativeBase children source (Interner.constructorCode.operationRequest opcode values)
        debug prepared rows parent) :
    let actual := (step nativeBase owner usizeBits children).operation opcode values debug before
    ordinary actual.1 = true → GraphFrame safety base.allocator owner rows parent actual.2 := by
  dsimp only
  intro completed
  obtain ⟨source, after, prepared, ready, ran⟩ := Arguments.operation_entry (nativeBase).external base.budget base.allocator
    (context nativeBase owner usizeBits children debug).primitives base.queries opcode values debug before facts.valid completed
  have post := stack.prepared_frame ops allocate safety owner usizeBits base growth meaning children debug rows parent
    source (Interner.constructorCode.operationRequest opcode values) before after ready initial data capacity facts
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted typed (proper source after prepared ready)
  obtain ⟨ownerCell, ownerFound, _⟩ := facts.ownerLive
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory ownerFound).1
  change ordinary (Arguments.operation (nativeBase).external base.budget base.allocator
    (context nativeBase owner usizeBits children debug).primitives base.queries opcode values debug before).1 = true at completed
  change GraphFrame _ _ _ _ _ (Arguments.operation (nativeBase).external base.budget base.allocator
    (context nativeBase owner usizeBits children debug).primitives base.queries opcode values debug before).2
  rw [ran] at completed ⊢
  exact post.returned values before.memory.memory.nextId older
    (stack.cleanup initial _ (Nat.le_refl _)) completed

/-- Named-local operations use the same copy/overwrite entry decomposition and
the same original-mark frame return as semantic preservation. -/
theorem Enclosing.local_frame (opcode : Opcode) (slice : ArgumentSlice) (selected : Nat)
    (repeated : NodeId) (first : Bool) (before : World (Publication.Effects σ))
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (inside : first = true → selected < slice.items.length)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (proper : ∀ source prepared, LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →
      Arguments.Prepared (if first then slice.items.set selected repeated else slice.items) before source prepared →
      ProperFrames safety owner nativeBase children source
        (Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))
        debug prepared rows parent) :
    let actual := (step nativeBase owner usizeBits children).localOperation opcode slice selected repeated first debug before
    ordinary actual.1 = true → GraphFrame safety base.allocator owner rows parent actual.2 := by
  dsimp only
  intro completed
  obtain ⟨source, after, prepared, ready, ran⟩ := ViewInput.local_entry
    (context nativeBase owner usizeBits children debug) opcode slice selected repeated first debug before
    ⟨facts.valid, represented⟩ inside completed
  have post := stack.prepared_frame ops allocate safety owner usizeBits base growth meaning children debug rows parent
    source (Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))
    before after ready initial data capacity facts (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    admitted typed (proper source after prepared ready)
  obtain ⟨ownerCell, ownerFound, _⟩ := facts.ownerLive
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory ownerFound).1
  change ordinary ((ViewInput.constructors (context nativeBase owner usizeBits children debug)).localOperation
    opcode slice selected repeated first debug before).1 = true at completed
  change GraphFrame _ _ _ _ _ ((ViewInput.constructors (context nativeBase owner usizeBits children debug)).localOperation
    opcode slice selected repeated first debug before).2
  rw [ran] at completed ⊢
  exact post.unwind before.memory.memory.nextId older (stack.cleanup initial _ (Nat.le_refl _)) completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
