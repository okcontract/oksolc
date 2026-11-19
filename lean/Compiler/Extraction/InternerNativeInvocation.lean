/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray Recursive

/-- Native frame, local closure and word preservation for the same ordinary
invocation. This does not assert a whole-stream logical correspondence. -/
def InvocationPost (meaning : Meaning) (frame : World σ → Prop) (before : Interner.Heap)
    (actual : Except Fault NodeId × State σ) (expected : Word) : Prop :=
  ordinary actual.1 = true → Closed actual.2.scope ∧ frame actual.2.world ∧
    Semantic.Ensures meaning before actual.1 actual.2.world.graph
      (fun id after => after.read id = some expected)

/-- Only reached miss suffixes and proper children remain obligations. None of
these fields assumes preservation of the enclosing invocation. The source guard
protects every child and publication contract, including word semantics. -/
structure TakenObligations (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (modelChildren : Associative.Constructors AssemblyItem.Fields.Values) (modelSeed : Interner.Primitives)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (address : Compiler.ZigAir.Memory.Address) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (deterministic : Bool)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word) : Prop where
  coupled : (deterministic && (request.item.kind == 1)) = true →
    (projection (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren
  suffixes : MissSteps base.external base.allocator
    ((context base owner usizeBits children debug).primitives source address (input request.item debug))
    modelSeed (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent) (GraphFrame safety base.allocator owner rows parent)
    key normalized lookup deterministic (deterministic && (request.item.kind == 1))
  correct : (deterministic && (request.item.kind == 1)) = true →
    Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren
  addresses : (deterministic && (request.item.kind == 1)) = true →
    AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation
  shifts : (deterministic && (request.item.kind == 1)) = true →
    ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation
  insertWords : ∀ heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
    key.eval (Dispatch.wordDispatchMeaning env other) heap.read = some expected →
    Interner.Safe (Dispatch.wordDispatchMeaning env other) (modelSeed.insert key deterministic) heap
      (fun id after => after.read id = some expected)
  publishWords : (deterministic && (request.item.kind == 1)) = true →
    ∀ id heap, Interner.Invariant (Dispatch.wordDispatchMeaning env other) heap →
    key.eval (Dispatch.wordDispatchMeaning env other) heap.read = some expected → heap.read id = some expected →
    Interner.Safe (Dispatch.wordDispatchMeaning env other) (modelSeed.publish key id) heap (fun _ _ => True)

/-- Local preservation data for a reached miss. Its child cursor/model can be
chosen after the actual prefix. Native suffix semantics and frame laws do not
assume an exact raw heap model or preservation of the enclosing invocation. -/
structure TakenObligationsAt (cursor : World (Publication.Effects σ) → Nat)
    (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (children : Constructors (Publication.Effects σ))
    (modelChildren : Associative.Constructors AssemblyItem.Fields.Values)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (address : Compiler.ZigAir.Memory.Address) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (deterministic : Bool) (env : AddressMask.Environment) (other : Meaning) (expected : Word) : Prop where
  coupled : (deterministic && (request.item.kind == 1)) = true →
    (projectionAt (cursorGraph cursor) (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug children modelChildren
  frames : MissFrames base.external base.allocator
    ((context base owner usizeBits children debug).primitives source address (input request.item debug))
    (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent) (GraphFrame safety base.allocator owner rows parent)
    key normalized lookup deterministic (deterministic && (request.item.kind == 1))
  words : MissWords base.external base.allocator
    ((context base owner usizeBits children debug).primitives source address (input request.item debug))
    (CallFrame safety base.allocator owner rows source request.arguments normalized
      address (input request.item debug) parent) (Dispatch.wordDispatchMeaning env other) expected
    key normalized lookup deterministic (deterministic && (request.item.kind == 1))
  correct : (deterministic && (request.item.kind == 1)) = true →
    Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) modelChildren
  addresses : (deterministic && (request.item.kind == 1)) = true →
    AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) modelChildren.operation
  shifts : (deterministic && (request.item.kind == 1)) = true →
    ArithmeticShift.Constructs (AddressMask.addressMeaning env other) modelChildren.operation

/-- Legacy raw correspondence supplies the observed local data through the
shared frame and word adapters; its clients need no stronger assumptions. -/
theorem TakenObligations.observed {safety : Bool} {owner usizeBits : Nat}
    {base : PairInput.Context (Publication.Effects σ)} {children : Constructors (Publication.Effects σ)}
    {modelChildren : Associative.Constructors AssemblyItem.Fields.Values} {modelSeed : Interner.Primitives}
    {source : View} {request : Interner.Request} {debug : AssemblyItem.Fields.Values}
    {rows : List Storage.Cell} {parent : World (Publication.Effects σ) → Prop}
    {address : Compiler.ZigAir.Memory.Address} {key : Key} {normalized : ArgumentSlice} {lookup : Handle}
    {deterministic : Bool} {env : AddressMask.Environment} {other : Meaning} {expected : Word}
    (obligations : TakenObligations safety owner usizeBits base children modelChildren modelSeed source request debug rows parent
      address key normalized lookup deterministic env other expected) :
    TakenObligationsAt (fun world => world.graph.allocationCursor) safety owner usizeBits base children modelChildren
      source request debug rows parent address key normalized lookup deterministic env other expected where
  coupled := obligations.coupled
  frames := obligations.suffixes.frames
  words := obligations.suffixes.words (Dispatch.wordDispatchMeaning env other) expected obligations.insertWords obligations.publishWords
  correct := obligations.correct
  addresses := obligations.addresses
  shifts := obligations.shifts

/-- Compose every actual item-entry route from its reached native miss.
The local miss can be supplied by a direct native proof or observed children.
No successful preparation, scratch allocation, initialization, classification,
cache miss or take is assumed at entry. Rejected
prefixes remain nonordinary; successful initialization derives the actual key.
All five constructor wrappers and complete-stream correspondence remain separate
consumers; the borrowed native step is attached here without a fixture. -/
theorem step_invocation_verified_miss (safety : Bool) (owner usizeBits capacity : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (host : External σ)
    (children : Constructors (Publication.Effects σ))
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected)
    (retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after)
    (localParent : ∀ constructed address, prepare request.item debug before = (.ok address, constructed) →
      ∀ world, parent world → parent (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world))
    (takenMiss : ∀ site : ProtocolTrace.TakenSite σ, site.Reached base source request debug before →
      let p := (context base owner usizeBits children debug).primitives source site.address (input request.item debug)
      let ran := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator p)
        request site.key site.deterministic ⟨site.taken.world, ⟨some site.lookup, some site.normalized, false⟩⟩
      let actual := OwnedCall.finish base.external base.allocator ran.1 ran.2
      FramePost (GraphFrame safety base.allocator owner rows parent) actual ∧
        Semantic.Ensures (Dispatch.wordDispatchMeaning env other) site.taken.world.graph actual.1 actual.2.world.graph
          (fun id after => after.read id = some expected)) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph actual expected ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        let ran := (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before
        ordinary ran.1 = true → GraphFrame safety base.allocator owner rows parent ran.2 ∧
          Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph ran.1 ran.2.graph
            (fun id after => after.read id = some expected)) := by
  dsimp only
  let p := (context base owner usizeBits children debug).primitives source
  let actual := invoke base.external base.budget base.allocator p base.queries source request debug before
  have post : InvocationPost (Dispatch.wordDispatchMeaning env other)
      (GraphFrame safety base.allocator owner rows parent) before.graph actual expected := by
    intro completed
    rcases invocation_entry safety owner usizeBits capacity base host children source request debug before data rows
        external facts represented privateSource admitted domain typed completed with leaf | ⟨site, reached⟩
    · exact ⟨leaf.closed, leaf.parent retained, leaf.words (Dispatch.wordBaseMeaning env other) expected valid evaluated⟩
    · have item := (prepare_success request.item debug before site.constructed site.address facts.valid domain typed reached.made).2
      obtain ⟨ownerCell, ownerFound, _⟩ := facts.ownerLive
      have ownerOlder := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory ownerFound).1
      have checked := reached.return_verified children owner usizeBits (Dispatch.wordDispatchMeaning env other) expected
        (GraphFrame safety base.allocator owner rows parent) (reached.input.origin.graph.trans item.graph)
        (GraphFrame.locals safety base.allocator owner rows parent before.memory.memory.nextId site.constructed.memory.memory.nextId
          ownerOlder (by rw [item.nextId]; omega) (localParent site.constructed site.address reached.made)) (takenMiss _ reached)
      exact ⟨(checked.1 completed).1, (checked.1 completed).2, checked.2⟩
  refine ⟨post, ?_⟩
  intro opcode borrowed requestEq sourceEq
  have same : (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before =
      (actual.1, actual.2.world) := by
    subst request source
    rfl
  rw [same]
  intro completed
  exact (post completed).2


/-- The observed-model entry proof specializes the shared native-miss composition. -/
theorem step_invocation_verified_observed (safety : Bool) (owner usizeBits capacity : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (host : External σ)
    (children : Constructors (Publication.Effects σ))
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected)
    (retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after)
    (localParent : ∀ constructed address, prepare request.item debug before = (.ok address, constructed) →
      ∀ world, parent world → parent (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world))
    (takenObligations : ∀ constructed address pointer memory values prepared taken key normalized lookup deterministic,
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
        source request debug rows parent address key normalized lookup deterministic env other expected) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph actual expected ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        let ran := (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before
        ordinary ran.1 = true → GraphFrame safety base.allocator owner rows parent ran.2 ∧
          Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph ran.1 ran.2.graph
            (fun id after => after.read id = some expected)) := by
  apply step_invocation_verified_miss safety owner usizeBits capacity base host children source request debug before data rows parent
    env other expected external facts represented privateSource array admitted domain typed valid evaluated retained localParent
  intro site reached
  obtain ⟨cursor, modelChildren, obligations⟩ := takenObligations site.constructed site.address site.pointer site.memory site.values
    site.prepared site.taken site.key site.normalized site.lookup site.deterministic reached.made reached.room reached.allocated
    reached.initialized reached.classified reached.keyed reached.missed reached.transferred reached.input
  obtain ⟨item, constructedFacts, _, initial, _⟩ := reached.native_inputs facts privateSource array domain typed retained
  have keyValue := reached.key_value item env other expected valid evaluated
  exact taken_miss_verified_cursor safety owner usizeBits base children modelChildren source request debug site.constructed
    site.address site.values site.taken site.key site.normalized site.lookup rows constructedFacts reached.input
    (by rw [item.effects]; exact privateSource) (array.frame (fun _ cell found => item.memory _ cell found)) parent
    (GraphFrame safety base.allocator owner rows parent) initial.parent reached.keyed cursor site.deterministic obligations.coupled
    env other expected obligations.frames obligations.words obligations.correct obligations.addresses obligations.shifts keyValue.1 keyValue.2

/-- The fixed raw-model entry theorem specializes the same observed entry
composition. Preparation, failure, cache and return proofs are shared. -/
theorem step_invocation_verified (safety : Bool) (owner usizeBits capacity : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (host : External σ)
    (children : Constructors (Publication.Effects σ))
    (modelChildren : Associative.Constructors AssemblyItem.Fields.Values) (modelSeed : Interner.Primitives)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before : World (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop)
    (env : AddressMask.Environment) (other : Meaning) (expected : Word)
    (external : base.external = Publication.external host)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted host)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read
      request.arguments request.sequence = some expected)
    (retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after)
    (localParent : ∀ constructed address, prepare request.item debug before = (.ok address, constructed) →
      ∀ world, parent world → parent (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world))
    (takenObligations : ∀ constructed address pointer memory values prepared taken key normalized lookup deterministic,
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
        address key normalized lookup deterministic env other expected) :
    let actual := invoke base.external base.budget base.allocator
      ((context base owner usizeBits children debug).primitives source) base.queries source request debug before
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      before.graph actual expected ∧
      (∀ opcode borrowed, request = Interner.constructorCode.operationRequest opcode borrowed.items → source = view borrowed →
        let ran := (step base owner usizeBits children).borrowedOperation borrowed.address opcode borrowed.items debug before
        ordinary ran.1 = true → GraphFrame safety base.allocator owner rows parent ran.2 ∧
          Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph ran.1 ran.2.graph
            (fun id after => after.read id = some expected)) := by
  apply step_invocation_verified_observed safety owner usizeBits capacity base host children source request debug
    before data rows parent env other expected external facts represented privateSource array admitted domain typed valid evaluated retained localParent
  intro constructed address pointer memory values prepared taken key normalized lookup deterministic
    made room allocated initialized classified keyed missed transferred entry
  exact ⟨(fun world => world.graph.allocationCursor), modelChildren,
    (takenObligations constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred entry).observed⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
