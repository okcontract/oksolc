/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolPrefix

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ResourceAdapter Interner.InvocationTrace

attribute [local irreducible] Initialization.capture Close.capture

/-- The two lookup exits share the same initialized state. A successful result
requires the actual deterministic cache hit; an error is the actual classifier
error. Neither branch reaches take or a graph callback. -/
theorem lookup_body (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (before : World σ) (values : List NodeId) (prepared : OwnedCall.State σ)
    (result : Except Interner.Error NodeId) (leading : List ProtocolEvent)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (initialized : Caller.initLookup external budget allocator source buffer request
      ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (room : q.atCapacity before.graph = false)
    (classified : q.deterministic request.item = result.map (fun _ => true))
    (cached : ∀ id, result = .ok id → ∃ key, Interner.makeKey request values = .ok key ∧ before.graph.table key = some id) :
    let init := Initialization.capture external budget allocator commutative source buffer request.arguments before.memory
    ∃ lookup, init.1 = .ok (some lookup) ∧
      findBody external budget allocator p q observations source buffer request
        ⟨⟨before, { lookup := none }⟩, {}, leading⟩ =
        (result.mapError Fault.language, ⟨prepared, { lookup := some lookup, items := init.2.effects.handle.values },
          leading ++ init.2.events.map Event.normalization⟩) := by
  intro init
  obtain ⟨lookup, captured, _⟩ := Initialization.capture_success external budget allocator commutative
    source buffer request before values prepared decoded initialized
  refine ⟨lookup, captured, ?_⟩
  cases result with
  | error error =>
    simp only [Except.map] at classified
    simp only [findBody, Interner.FindCode.controlRun, execution, bind, Effect.bind, record, unchanged,
      List.append_nil, room, Bool.false_eq_true, ↓reduceIte, initialization, decoded, initialized, captured,
      classified, Except.mapError]
    rfl
  | ok id =>
    obtain ⟨key, made, found⟩ := cached id rfl
    simp only [Except.map] at classified
    simp only [findBody, Interner.FindCode.controlRun, execution, bind, Effect.bind, record, unchanged,
      List.append_nil, room, Bool.false_eq_true, ↓reduceIte, initialization, decoded, initialized, captured,
      classified, made, found, Except.mapError, pure, Effect.pure]
    rfl

/-- The scoped source uses the same guards and returns through its lookup
cleanup. Resources remain arbitrary here; physical admission is proved below. -/
theorem scoped_lookup (r : Interner.Scoped.Resources) (model : Interner.Primitives)
    (request : Interner.Request) (before : Interner.Heap) (values : List NodeId)
    (prepared : Interner.Scoped.Session) (result : Except Interner.Error NodeId)
    (room : model.atCapacity before = false)
    (initialized : Interner.Scoped.initScope r request ⟨{}, before⟩ = (.ok values, prepared))
    (classified : model.deterministic request.item = result.map (fun _ => true))
    (cached : ∀ id, result = .ok id → ∃ key, Interner.makeKey request values = .ok key ∧ before.table key = some id) :
    Interner.Scoped.findDetailed r model request before = (result, Interner.Scoped.close r prepared) := by
  cases result with
  | error error =>
    simp only [Except.map] at classified
    simp only [Interner.Scoped.findDetailed, Interner.Scoped.finish, Interner.FindCode.controlRun,
      Interner.Scoped.execution, Interner.Scoped.liftGraph, Interner.get, Interner.lift,
      bind, Effect.bind, room, Bool.false_eq_true, ↓reduceIte, initialized, classified]
  | ok id =>
    obtain ⟨key, made, found⟩ := cached id rfl
    simp only [Except.map] at classified
    simp only [Interner.Scoped.findDetailed, Interner.Scoped.finish, Interner.FindCode.controlRun,
      Interner.Scoped.execution, Interner.Scoped.liftGraph, Interner.get, Interner.lift,
      bind, Effect.bind, room, Bool.false_eq_true, ↓reduceIte, initialized, classified, made, found]
    rfl

/-- One complete physical/scoped return proof for ordinary classification
errors and cache hits. The actual initializer supplies readiness, and readiness
derives cleanup. The resource stream is the complete actual recorder output;
no final frame, cleanup equation or enclosing simulation is a premise. -/
theorem lookup_projected (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : OwnedCall.State σ)
    (result : Except Interner.Error NodeId) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (room : q.atCapacity before.graph = false)
    (classified : q.deterministic request.item = result.map (fun _ => true))
    (cached : ∀ id, result = .ok id → ∃ key, Interner.makeKey request values = .ok key ∧ before.graph.table key = some id)
    (completed : ordinary (result.mapError Fault.language) = true)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = q.deterministic request.item) :
    let input := { before with memory := { before.memory with memory } }
    let actual := find external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    actual.1 = result.mapError Fault.language ∧ Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧
      actual.2.tokens.incomplete = false := by
  intro input actual logical
  let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
  let init := Initialization.capture external budget allocator commutative source buffer request.arguments input.memory
  obtain ⟨lookup, captured, locals, tokenEq, contents, ready, _, normalized, prefixProof⟩ := initialized_recorded external budget allocator
    commutative source request before memory pointer values prepared leading other read sequence
    valid represented allocated decoded admitted initialized
  obtain ⟨bodyLookup, bodyCapture, body⟩ := lookup_body external budget allocator commutative p q observations source buffer
    request input values prepared result leading decoded initialized room classified cached
  have same := Option.some.inj (Except.ok.inj (bodyCapture.symm.trans captured))
  subst bodyLookup
  change Caller.initLookup external budget allocator source buffer request ⟨input, { lookup := none }⟩ =
    (.ok values, prepared) at initialized
  change (Initialization.capture external budget allocator commutative source buffer request.arguments input.memory).1 =
    .ok (some lookup) at captured
  let handle := init.2.effects.handle
  let closeLeading := leading ++ init.2.events.map Event.normalization
  let entry : Recorded σ := ⟨prepared, { lookup := some lookup, items := handle.values }, closeLeading⟩
  let closed := record (cleanup external allocator) (closing external allocator) entry
  have entryEq : entry = ⟨⟨prepared.world, { lookup := some handle }⟩,
      { lookup := some (token lookup.origin handle), items := handle.values }, closeLeading⟩ := by
    dsimp only [entry]
    rw [tokenEq]
    congr 2
    change (⟨prepared.world, prepared.scope⟩ : OwnedCall.State σ) = _
    rw [locals]
  have closeProof := lookup_close_projected external allocator lookup.origin source request.arguments handle prepared.world
    closeLeading trailing ready
  rw [← entryEq] at closeProof
  change closed.1 = .ok () ∧ _ at closeProof
  have actualEq : actual = (result.mapError Fault.language, closed.2) := by
    change finish external allocator
      (findBody external budget allocator p q observations source buffer request ⟨⟨input, { lookup := none }⟩, {}, leading⟩).1
      (findBody external budget allocator p q observations source buffer request ⟨⟨input, { lookup := none }⟩, {}, leading⟩).2 = _
    rw [body]
    change finish external allocator (result.mapError Fault.language) entry = _
    simp only [finish, completed, ↓reduceIte]
    change ((match closed.1 with | .error fault => Except.error fault | .ok () => result.mapError Fault.language), closed.2) = _
    rw [closeProof.1]
  let r := resources (closed.2.events ++ trailing) (.preparation .incomplete)
  let initial := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
  have closedEvents : closed.2.events = closeLeading ++
      (Close.capture external allocator lookup .lookup handle prepared).2.events.map Event.normalization := by
    simp only [closed, record, entry, closing, locals]
    rfl
  have initialEq : initial = (.ok values, scopeView entry) := by
    simpa only [initial, r, closedEvents, entry, closeLeading, List.append_assoc] using
      prefixProof ((Close.capture external allocator lookup .lookup handle prepared).2.events.map Event.normalization ++ trailing)
  have initialResult := congrArg Prod.fst initialEq
  have scopeEq := congrArg Prod.snd initialEq
  have modelRun := scoped_lookup r model request { before.graph with allocationCursor := leading.length } values initial.2 result
    (capacityQuery.trans room) (Prod.ext initialResult rfl) (classificationQuery.trans classified) cached
  have logicalEq : logical = (result, Interner.Scoped.close r (scopeView entry)) := by
    simpa only [logical, actualEq, r, scopeEq] using modelRun
  rw [actualEq, logicalEq]
  exact ⟨rfl, closeProof.2.1, closeProof.2.2.1, Prod.ext rfl closeProof.2.2.2.2.1, closeProof.2.2.2.2.2⟩

/-- Ordinary classification failure now consumes the same physical lookup
return as a cache hit, with no cache, take or child obligation. -/
theorem classification_projected (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : OwnedCall.State σ)
    (error : Interner.Error) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (room : q.atCapacity before.graph = false)
    (classified : q.deterministic request.item = .error error)
    (completed : ordinary ((.error (.language error) : Except Fault NodeId)) = true)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = q.deterministic request.item) :
    let input := { before with memory := { before.memory with memory } }
    let actual := find external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    actual.1 = (.error (.language error) : Except Fault NodeId) ∧ Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧
      actual.2.tokens.incomplete = false := by
  exact lookup_projected external budget allocator commutative p q observations model source request before memory pointer
    values prepared (.error error) leading trailing other read sequence valid represented allocated decoded admitted initialized
    room classified (by intro id impossible; cases impossible) completed capacityQuery classificationQuery

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
