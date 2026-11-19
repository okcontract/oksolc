/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeConstructors

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive

/-- Reached native frames and proper-child contracts. Completed suffix words
and candidate values are derived from actual callbacks, so no expected word or
suffix semantic theorem belongs to this input interface. -/
structure TakenFramesAt (cursor : World (Publication.Effects σ) → Nat)
    (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (modelChildren : Associative.Constructors AssemblyItem.Fields.Values)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (address : Compiler.ZigAir.Memory.Address) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (deterministic : Bool) (env : AddressMask.Environment) (other : Meaning) : Prop where
  coupled : (deterministic && (request.item.kind == 1)) = true →
    (projectionAt (cursorGraph cursor) (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren
  frames : MissFrames base.external base.allocator
    ((context base owner usizeBits children debug).primitives source address (input request.item debug))
    (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent) (GraphFrame safety base.allocator owner rows parent)
    key normalized lookup deterministic (deterministic && (request.item.kind == 1))
  correct : (deterministic && (request.item.kind == 1)) = true →
    Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren
  addresses : (deterministic && (request.item.kind == 1)) = true →
    AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation
  shifts : (deterministic && (request.item.kind == 1)) = true →
    ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation

/-- The same parent laws and source-selected entry observations as the shared
constructor proof, with only child/frame obligations at each reached miss.
Earlier failures and cache hits require no child witnesses. -/
structure EntryFrames (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (env : AddressMask.Environment) (other : Meaning) : Prop where
  retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after
  localParent : ∀ constructed address, prepare request.item debug before = (.ok address, constructed) →
      ∀ world, parent world → parent (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world)
  taken : ∀ constructed address pointer memory values prepared taken key normalized lookup deterministic,
      prepare request.item debug before = (.ok address, constructed) →
      base.queries.atCapacity constructed.graph = false →
      Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory) →
      Caller.initLookup base.external base.budget base.allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
        ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared) →
      base.queries.deterministic request.item = .ok deterministic →
      Interner.makeKey request values = .ok key →
      (deterministic = true → constructed.graph.table key = none) →
      take base.external base.allocator prepared = (.ok (), taken) →
      Insertion.Native.CallerInput base.allocator source address request values (input request.item debug) key
        constructed taken normalized lookup →
      ∃ cursor modelChildren, TakenFramesAt cursor safety owner usizeBits base children modelChildren
        source request debug rows parent
        address key normalized lookup deterministic env other

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (children : Constructors (Publication.Effects σ))
    (env : AddressMask.Environment) (other : Meaning)

/-- Actual native insertion/publication/failure supply the missing suffix
semantics at this reached key. All proper-child and native-frame laws retain
exactly their source guard and chosen cursor/model. -/
theorem TakenFramesAt.native {cursor : World (Publication.Effects σ) → Nat}
    {modelChildren : Associative.Constructors AssemblyItem.Fields.Values}
    {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {rows : List Storage.Cell} {parent : World (Publication.Effects σ) → Prop}
    {address : Compiler.ZigAir.Memory.Address} {key : Key} {normalized : ArgumentSlice} {lookup : Handle}
    {deterministic : Bool}
    (frames : TakenFramesAt cursor safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children modelChildren
      source request debug rows parent address key normalized lookup deterministic env other)
    (expected : Word) (aligned : key.arguments = normalized.items)
    (bound : keyCode.run request.item normalized.items request.sequence = some key)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other) :
    TakenObligationsAt cursor safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children modelChildren
      source request debug rows parent address key normalized lookup deterministic env other expected where
  coupled := frames.coupled
  frames := frames.frames
  words := native_miss_words ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits children debug
    source address (input request.item debug) rows request.arguments normalized parent key lookup deterministic
    (deterministic && (request.item.kind == 1)) expected aligned request.sequence bound pushes
  correct := frames.correct
  addresses := frames.addresses
  shifts := frames.shifts

/-- Original caller input supplies the normalized key, so every ordinary
constructor route can use derived suffix words without assuming them at entry. -/
theorem EntryFrames.native {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {before : World (Publication.Effects σ)} {rows : List Storage.Cell} {parent : World (Publication.Effects σ) → Prop}
    (frames : EntryFrames safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children
      source request debug before rows parent env other)
    (expected : Word) (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other) :
    ObservedEntryObligations safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children
      source request debug before rows parent env other expected where
  retained := frames.retained
  localParent := frames.localParent
  taken := by
    intro constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred entry
    obtain ⟨cursor, modelChildren, reached⟩ := frames.taken constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred entry
    exact ⟨cursor, modelChildren, reached.native ops allocate safety owner usizeBits base growth children env other
      expected entry.publication.aligned entry.keyed pushes⟩

variable {capacity : Nat} {data : Compiler.ZigAir.Memory.Address} {rows : List Storage.Cell}
    {before : World (Publication.Effects σ)} {debug : AssemblyItem.Fields.Values}
    {parent : World (Publication.Effects σ) → Prop} {expected : Word}
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
include facts admitted typed valid

/-- Complete native item invocation consumes the derived suffix semantics;
preparation, all early exits and local return share the existing entry proof. -/
theorem EntryFrames.native_verified {source : View} {request : Interner.Request}
    (frames : EntryFrames safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children source request debug before rows parent env other)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other) :
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph (invoke (Publication.external ops.arguments) base.budget base.allocator
        ((context (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children debug).primitives source)
        base.queries source request debug before) expected :=
  (frames.native ops allocate safety owner usizeBits base growth children env other expected pushes).verified
    ops.arguments rfl facts represented privateSource array admitted domain typed valid evaluated

attribute [local irreducible] step

theorem step_borrowed_native_verified (slice : ArgumentSlice) (opcode : Opcode)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (privateSource : Caller.SourcePrivate (view slice) before.memory.effects.keys)
    (array : ArraySource (view slice) before.memory.memory)
    (evaluated : (Interner.constructorCode.operationRequest opcode slice.items).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read slice.items Interner.constructorCode.sequence = some expected)
    (obligations : EntryFrames safety owner usizeBits (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children
      (view slice) (Interner.constructorCode.operationRequest opcode slice.items) debug before rows parent env other) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children).borrowedOperation slice.address opcode slice.items debug before) expected :=
  step_borrowed_verified_observed
    (base := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
    (children := children) ops.arguments rfl facts admitted typed valid slice opcode represented privateSource array evaluated
    (obligations.native ops allocate safety owner usizeBits base growth children env other expected (by
      intro impossible
      have wrong : (1#32 : BitVec 32) = 2#32 := impossible
      contradiction))

theorem step_constant_native_verified (value : Word) (pushes : Associative.Pushes other)
    (literals : Insertion.Native.PushValues other)
    (obligations : EntryFrames safety owner usizeBits (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children
      ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug before rows parent env other) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children).constant value debug before) value :=
  step_constant_verified_observed
    (base := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
    (children := children) ops.arguments rfl facts admitted typed valid value pushes
    (obligations.native ops allocate safety owner usizeBits base growth children env other value (fun _ => literals))

theorem step_materialize_native_verified (id : NodeId) (value : Word) (pushes : Associative.Pushes other)
    (literals : Insertion.Native.PushValues other)
    (obligations : EntryFrames safety owner usizeBits (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children
      ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug before rows parent env other) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children).materialize id value debug before) value :=
  step_materialize_verified_observed
    (base := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
    (children := children) ops.arguments rfl facts admitted typed valid id value pushes
    (obligations.native ops allocate safety owner usizeBits base growth children env other value (fun _ => literals))

theorem step_operation_native_verified (opcode : Opcode) (values : List NodeId)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read values Interner.constructorCode.sequence = some expected)
    (obligations : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      Arguments.Prepared values before source prepared →
      EntryFrames safety owner usizeBits (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children source
        (Interner.constructorCode.operationRequest opcode values) debug prepared rows parent env other)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children).operation opcode values debug before) expected :=
  step_operation_verified_observed
    (base := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
    (children := children) ops.arguments rfl facts admitted typed valid opcode values evaluated
    (fun source prepared made ready =>
      (obligations source prepared made ready).native ops allocate safety owner usizeBits base growth children env other expected (by
      intro impossible
      have wrong : (1#32 : BitVec 32) = 2#32 := impossible
      contradiction)) localParent

theorem step_local_native_verified (opcode : Opcode) (slice : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (inside : first = true → selected < slice.items.length)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read
      (if first then slice.items.set selected repeated else slice.items) Interner.constructorCode.sequence = some expected)
    (obligations : ∀ source prepared, LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →
      Arguments.Prepared (if first then slice.items.set selected repeated else slice.items) before source prepared →
      EntryFrames safety owner usizeBits (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) children source
        (Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))
        debug prepared rows parent env other)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits children).localOperation opcode slice selected repeated first debug before) expected :=
  step_local_verified_observed
    (base := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
    (children := children) ops.arguments rfl facts admitted typed valid opcode slice selected repeated first represented inside evaluated
    (fun source prepared made ready =>
      (obligations source prepared made ready).native ops allocate safety owner usizeBits base growth children env other expected (by
      intro impossible
      have wrong : (1#32 : BitVec 32) = 2#32 := impossible
      contradiction)) localParent

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
