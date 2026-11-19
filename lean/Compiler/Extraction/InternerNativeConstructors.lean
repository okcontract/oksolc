/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorEntry
import Compiler.Extraction.InternerNativeArgumentReturn
import Compiler.Extraction.InternerNativeSuffixWords
import Compiler.Extraction.InternerNativeParentReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray Recursive

/-- The remaining entry obligations are local parent laws and actual reached
miss suffixes. They do not assume preservation of any complete constructor. -/
structure EntryObligations (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (modelChildren : Associative.Constructors AssemblyItem.Fields.Values) (modelSeed : Interner.Primitives)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word) : Prop where
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
      TakenObligations safety owner usizeBits base children modelChildren modelSeed source request debug rows parent
        address key normalized lookup deterministic env other expected

/-- Parent laws and child data local to the actual reached miss. Constructor
preparation need not select a fixed cursor, child model or raw suffix model. -/
structure ObservedEntryObligations (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word) : Prop where
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
      ∃ cursor modelChildren, TakenObligationsAt cursor safety owner usizeBits base children modelChildren
        source request debug rows parent
        address key normalized lookup deterministic env other expected

/-- Public constructor actions discard the internal scope record. The shared
invocation proof closes that scope before these wrappers retire their own locals. -/
def ConstructorPost (meaning : Meaning) (frame : World σ → Prop) (before : Interner.Heap)
    (actual : Except Fault NodeId × World σ) (expected : Word) : Prop :=
  ordinary actual.1 = true → frame actual.2 ∧
    Semantic.Ensures meaning before actual.1 actual.2.graph
      (fun id after => after.read id = some expected)

variable {safety : Bool} {owner usizeBits capacity : Nat}
    {base : PairInput.Context (Publication.Effects σ)} {children : Constructors (Publication.Effects σ)}
    {modelChildren : Associative.Constructors AssemblyItem.Fields.Values} {modelSeed : Interner.Primitives}
    {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    {data : Compiler.ZigAir.Memory.Address} {parent : World (Publication.Effects σ) → Prop}
    {env : AddressMask.Environment} {other : Meaning} {expected : Word}

/-- Raw correspondence supplies the same reached obligations through the shared
native frame and word adapters. The enclosing constructor is not assumed. -/
theorem EntryObligations.observed
    (obligations : EntryObligations safety owner usizeBits base children modelChildren modelSeed
      source request debug before rows parent env other expected) :
    ObservedEntryObligations safety owner usizeBits base children
      source request debug before rows parent env other expected where
  retained := obligations.retained
  localParent := obligations.localParent
  taken := by
    intro constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred entry
    exact ⟨(fun world => world.graph.allocationCursor), modelChildren,
      (obligations.taken constructed address pointer memory values prepared taken key normalized lookup deterministic
        made room allocated initialized classified keyed missed transferred entry).observed⟩

/-- Package the existing all-entry theorem without strengthening its premises. -/
theorem ObservedEntryObligations.verified
    (obligations : ObservedEntryObligations safety owner usizeBits base children
      source request debug before rows parent env other expected)
    (host : External σ) (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected) :
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph (invoke base.external base.budget base.allocator
        ((context base owner usizeBits children debug).primitives source) base.queries source request debug before) expected :=
  (step_invocation_verified_observed safety owner usizeBits capacity base host children
    source request debug before data rows parent env other expected external facts represented privateSource array admitted domain typed
    valid evaluated obligations.retained obligations.localParent obligations.taken).1

/-- The raw-model interface specializes the shared observed proof. -/
theorem EntryObligations.verified
    (obligations : EntryObligations safety owner usizeBits base children modelChildren modelSeed
      source request debug before rows parent env other expected)
    (host : External σ) (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected) :
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph (invoke base.external base.budget base.allocator
        ((context base owner usizeBits children debug).primitives source) base.queries source request debug before) expected :=
  obligations.observed.verified host external facts represented privateSource array admitted domain typed valid evaluated

theorem InvocationPost.project {meaning : Meaning} {frame : World σ → Prop} {initial : Interner.Heap}
    {actual : Except Fault NodeId × State σ} {value : Word}
    (post : InvocationPost meaning frame initial actual value) :
    ConstructorPost meaning frame initial (actual.1, actual.2.world) value := fun completed => (post completed).2

/-- One argument cleanup retains the reached native graph, including relocation,
and the same word result. Only the outer parent's own cleanup law is supplied. -/
theorem InvocationPost.unwind {meaning : Meaning} {initial : Interner.Heap}
    {actual : Except Fault NodeId × State (Publication.Effects σ)} {value : Word}
    (post : InvocationPost meaning (GraphFrame safety base.allocator owner rows parent) initial actual value)
    (mark : Nat) (older : owner < mark)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } }) :
    ConstructorPost meaning (GraphFrame safety base.allocator owner rows parent) initial
      (TemporaryArguments.unwind mark actual) value := by
  intro completed
  have actualCompleted : ordinary actual.1 = true := completed
  have native : FramePost (GraphFrame safety base.allocator owner rows parent) actual :=
    fun done => ⟨(post done).1, (post done).2.1⟩
  refine ⟨native.unwind mark older localParent completed, ?_⟩
  simpa only [TemporaryArguments.unwind, actualCompleted, ↓reduceIte] using (post actualCompleted).2.2

theorem InvocationPost.returned {meaning : Meaning} {initial : Interner.Heap}
    {actual : Except Fault NodeId × State (Publication.Effects σ)} {value : Word}
    (post : InvocationPost meaning (GraphFrame safety base.allocator owner rows parent) initial actual value)
    (values : List NodeId) (mark : Nat) (older : owner < mark)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } }) :
    ConstructorPost meaning (GraphFrame safety base.allocator owner rows parent) initial
      (Arguments.returned values mark actual) value := by
  unfold Arguments.returned
  split
  · exact post.project
  · exact post.unwind mark older localParent

/-- Actual argument preparation retains the native graph and separates its
new input view from every live key. Both recorded and native entry proofs use
these same reached facts. -/
theorem prepared_input_frame {prepared : World (Publication.Effects σ)}
    (ready : Arguments.Prepared request.arguments before source prepared)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows) :
    NativeGraph.Facts safety base.allocator owner data capacity prepared rows ∧
      Caller.SourcePrivate source prepared.memory.effects.keys := by
  have native := facts.frame ready.good.1 (by rw [ready.graph]; exact facts.projected)
    (congrArg Interner.Heap.table ready.graph) (congrArg Publication.Effects.keys ready.effects)
    (fun id cell found _ => ready.frame id cell found) (fun _ _ found => ready.heap ▸ found)
  refine ⟨native, ?_⟩
  intro key old found nonempty length
  exact ready.key_apart _ _ _ _ facts.valid base.allocator key facts.live old
    (by rw [ready.effects] at found; exact found) nonempty length

/-- Literal and named-local preparation share one native input theorem. The
actual preparation supplies validity, graph retention and fresh key separation. -/
theorem prepared_invocation_verified_observed {prepared : World (Publication.Effects σ)}
    (ready : Arguments.Prepared request.arguments before source prepared)
    (obligations : ObservedEntryObligations safety owner usizeBits base children
      source request debug prepared rows parent env other expected)
    (host : External σ) (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected) :
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph (invoke base.external base.budget base.allocator
        ((context base owner usizeBits children debug).primitives source) base.queries source request debug prepared) expected := by
  obtain ⟨native, privateSource⟩ := prepared_input_frame ready facts
  have post := obligations.verified host external native ready.good.2 privateSource ready.arraySource admitted domain typed
    (ready.graph.symm ▸ valid) (ready.graph.symm ▸ evaluated)
  simpa only [ready.graph] using post

/-- The raw-model interface specializes the shared observed proof. -/
theorem prepared_invocation_verified {prepared : World (Publication.Effects σ)}
    (ready : Arguments.Prepared request.arguments before source prepared)
    (obligations : EntryObligations safety owner usizeBits base children modelChildren modelSeed
      source request debug prepared rows parent env other expected)
    (host : External σ) (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected) :
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph (invoke base.external base.budget base.allocator
        ((context base owner usizeBits children debug).primitives source) base.queries source request debug prepared) expected :=
  prepared_invocation_verified_observed ready obligations.observed host external facts admitted domain typed valid evaluated

/-- Literal preparation either builds its typed source array or rejects the
memory observation/unsupported shape. It cannot manufacture ordinary native OOM. -/
theorem literal_error_nonordinary (values : List NodeId) (initial : Valid before.memory)
    (reached : World (Publication.Effects σ)) (fault : Fault)
    (failed : Arguments.prepare values before = (.error fault, reached)) :
    ordinary (.error fault : Except Fault NodeId) = false :=
  Arguments.error_nonordinary values initial reached fault failed

/-- Valid copied words and the guarded selected index discharge every store.
The unused index remains unrestricted when the optional overwrite is skipped. -/
theorem local_error_nonordinary (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (good : Good source [left, right] before) (inside : first = true → selected < 2)
    (reached : World (Publication.Effects σ)) (fault : Fault)
    (failed : LocalArguments.zigLocal source selected repeated first before = (.error fault, reached)) :
    ordinary (.error fault : Except Fault NodeId) = false :=
  LocalArguments.error_nonordinary left right repeated selected first good inside reached fault failed

variable (host : External σ) (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted host) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
include external facts admitted typed valid

theorem step_borrowed_verified_observed (slice : ArgumentSlice) (opcode : Opcode)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (privateSource : Caller.SourcePrivate (view slice) before.memory.effects.keys)
    (array : ArraySource (view slice) before.memory.memory)
    (evaluated : (Interner.constructorCode.operationRequest opcode slice.items).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read slice.items Interner.constructorCode.sequence = some expected)
    (obligations : ObservedEntryObligations safety owner usizeBits base children
      (view slice) (Interner.constructorCode.operationRequest opcode slice.items) debug before rows parent env other expected) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).borrowedOperation slice.address opcode slice.items debug before) expected :=
  (obligations.verified host external facts represented privateSource array admitted
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed valid evaluated).project

/-- The raw-model interface specializes the shared observed proof. -/
theorem step_borrowed_verified (slice : ArgumentSlice) (opcode : Opcode)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (privateSource : Caller.SourcePrivate (view slice) before.memory.effects.keys)
    (array : ArraySource (view slice) before.memory.memory)
    (evaluated : (Interner.constructorCode.operationRequest opcode slice.items).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read slice.items Interner.constructorCode.sequence = some expected)
    (obligations : EntryObligations safety owner usizeBits base children modelChildren modelSeed
      (view slice) (Interner.constructorCode.operationRequest opcode slice.items) debug before rows parent env other expected) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).borrowedOperation slice.address opcode slice.items debug before) expected :=
  step_borrowed_verified_observed host external facts admitted typed valid slice opcode represented privateSource array evaluated obligations.observed

theorem step_constant_verified_observed (value : Word) (pushes : Associative.Pushes other)
    (obligations : ObservedEntryObligations safety owner usizeBits base children
      ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug before rows parent env other value) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).constant value debug before) value := by
  have represented : Represents before.memory.memory ⟨0, 0, 0⟩ [] := ⟨rfl, by intro index inside; simp at inside⟩
  have privateSource : Caller.SourcePrivate ⟨0, 0, 0⟩ before.memory.effects.keys := by
    intro key old found nonempty impossible
    exact (impossible rfl).elim
  have evaluated : (Interner.constructorCode.constantRequest value).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read [] Interner.constructorCode.sequence = some value := by
    simpa [Interner.constructorCode, Interner.ConstructorCode.constantRequest, Scalar.run, Item.eval,
      readArguments, Dispatch.wordDispatchMeaning, Dispatch.wordBaseMeaning, Folding.wordMeaning,
      ArithmeticShift.shiftMeaning, AddressMask.addressMeaning] using pushes value
  exact (obligations.verified host external facts represented privateSource (ArraySource.empty rfl) admitted
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) typed valid evaluated).project

/-- The raw-model interface specializes the shared observed proof. -/
theorem step_constant_verified (value : Word) (pushes : Associative.Pushes other)
    (obligations : EntryObligations safety owner usizeBits base children modelChildren modelSeed
      ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug before rows parent env other value) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).constant value debug before) value :=
  step_constant_verified_observed host external facts admitted typed valid value pushes obligations.observed

/-- Materialization follows the source's constant forwarding, including the
same debug fields and ordinary failure paths. The old ID is not reinterpreted. -/
theorem step_materialize_verified_observed (id : NodeId) (value : Word) (pushes : Associative.Pushes other)
    (obligations : ObservedEntryObligations safety owner usizeBits base children
      ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug before rows parent env other value) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).materialize id value debug before) value :=
  step_constant_verified_observed host external facts admitted typed valid value pushes obligations

/-- The raw-model interface specializes the shared observed proof. -/
theorem step_materialize_verified (id : NodeId) (value : Word) (pushes : Associative.Pushes other)
    (obligations : EntryObligations safety owner usizeBits base children modelChildren modelSeed
      ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) debug before rows parent env other value) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).materialize id value debug before) value :=
  step_materialize_verified_observed host external facts admitted typed valid id value pushes obligations.observed

theorem step_operation_verified_observed (opcode : Opcode) (values : List NodeId)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read values Interner.constructorCode.sequence = some expected)
    (obligations : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      Arguments.Prepared values before source prepared →
      ObservedEntryObligations safety owner usizeBits base children source
        (Interner.constructorCode.operationRequest opcode values) debug prepared rows parent env other expected)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).operation opcode values debug before) expected := by
  change ConstructorPost _ _ _ (Arguments.operation base.external base.budget base.allocator
    (context base owner usizeBits children debug).primitives base.queries opcode values debug before) _
  intro completed
  obtain ⟨source, after, prepared, ready, ran⟩ := Arguments.operation_entry base.external base.budget base.allocator
    (context base owner usizeBits children debug).primitives base.queries opcode values debug before facts.valid completed
  have post := prepared_invocation_verified_observed ready (obligations source after prepared ready)
    host external facts admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed valid evaluated
  obtain ⟨ownerCell, ownerFound, _⟩ := facts.ownerLive
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory ownerFound).1
  rw [ran] at completed ⊢
  exact post.returned values before.memory.memory.nextId older localParent completed

/-- The raw-model interface specializes the shared observed proof. -/
theorem step_operation_verified (opcode : Opcode) (values : List NodeId)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read values Interner.constructorCode.sequence = some expected)
    (obligations : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      Arguments.Prepared values before source prepared →
      EntryObligations safety owner usizeBits base children modelChildren modelSeed source
        (Interner.constructorCode.operationRequest opcode values) debug prepared rows parent env other expected)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).operation opcode values debug before) expected :=
  step_operation_verified_observed host external facts admitted typed valid opcode values evaluated
    (fun source prepared made ready => (obligations source prepared made ready).observed) localParent

theorem step_local_verified_observed (opcode : Opcode) (slice : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (inside : first = true → selected < slice.items.length)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read
      (if first then slice.items.set selected repeated else slice.items) Interner.constructorCode.sequence = some expected)
    (obligations : ∀ source prepared, LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →
      Arguments.Prepared (if first then slice.items.set selected repeated else slice.items) before source prepared →
      ObservedEntryObligations safety owner usizeBits base children source
        (Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))
        debug prepared rows parent env other expected)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).localOperation opcode slice selected repeated first debug before) expected := by
  change ConstructorPost _ _ _ ((ViewInput.constructors (context base owner usizeBits children debug)).localOperation
    opcode slice selected repeated first debug before) _
  intro completed
  obtain ⟨source, after, prepared, ready, ran⟩ := ViewInput.local_entry
    (context base owner usizeBits children debug) opcode slice selected repeated first debug before
    ⟨facts.valid, represented⟩ inside completed
  have post := prepared_invocation_verified_observed ready (obligations source after prepared ready)
    host external facts admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed valid evaluated
  obtain ⟨ownerCell, ownerFound, _⟩ := facts.ownerLive
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory ownerFound).1
  rw [ran] at completed ⊢
  exact post.unwind before.memory.memory.nextId older localParent completed

/-- The raw-model interface specializes the shared observed proof. -/
theorem step_local_verified (opcode : Opcode) (slice : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (inside : first = true → selected < slice.items.length)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read
      (if first then slice.items.set selected repeated else slice.items) Interner.constructorCode.sequence = some expected)
    (obligations : ∀ source prepared, LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →
      Arguments.Prepared (if first then slice.items.set selected repeated else slice.items) before source prepared →
      EntryObligations safety owner usizeBits base children modelChildren modelSeed source
        (Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))
        debug prepared rows parent env other expected)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph ((step base owner usizeBits children).localOperation opcode slice selected repeated first debug before) expected :=
  step_local_verified_observed host external facts admitted typed valid opcode slice selected repeated first represented inside evaluated
    (fun source prepared made ready => (obligations source prepared made ready).observed) localParent

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
