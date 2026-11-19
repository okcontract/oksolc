/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolFailure
import Compiler.Extraction.InternerCallerProtocolLookup
import Compiler.Extraction.InternerCallerProtocolTakeFailure
import Compiler.Extraction.InternerCallerLookupRouting

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace

attribute [local irreducible] Initialization.capture Take.capture
attribute [local irreducible] Interner.Scoped.initScope Interner.Scoped.take

/-- The sole continuation obligation belongs to the actual reached miss, after
successful initialization and take and the source cache guard. It compares only
miss control and its cleanup, not the enclosing find. A proper-child proof can
discharge this boundary without assuming the caller relation being proved. -/
def MissContinuation (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives)
    (source buffer : View) (request : Interner.Request) (before : Recorded σ) (trailing : List ProtocolEvent) : Prop :=
  ∀ (values : List NodeId) (key : Key) (deterministic : Bool),
    let normalized := record (Caller.initLookup external budget allocator source buffer request)
      (initialization external budget allocator source buffer request) before
    let taken := record (OwnedCall.take external allocator) (taking external allocator) normalized.2
    q.atCapacity before.native.world.graph = false → normalized.1 = .ok values →
    q.deterministic request.item = .ok deterministic → Interner.makeKey request values = .ok key →
    (deterministic = true → before.native.world.graph.table key = none) → taken.1 = .ok () →
    let body := missBody external budget allocator p q observations source buffer request key deterministic taken.2
    let actual := finish external allocator body.1 body.2
    let r := resources (actual.2.events ++ trailing) (.preparation .incomplete)
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution r model) request key deterministic (scopeView taken.2)
    ordinary body.1 = true →
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, Interner.Scoped.close r logical.2) ∧
      actual.2.tokens.incomplete = false

/-- Join the admitted initialization/take prefix to a local miss proof over
one complete actual stream. Earlier history is retained by source execution;
no event-count or final cleanup equation is an input. -/
theorem taken_find_projected (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives)
    (source : View) (request : Interner.Request) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared called : OwnedCall.State σ) (key : Key) (deterministic : Bool)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (room : q.atCapacity before.graph = false) (classified : q.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key) (absent : deterministic = true → before.graph.table key = none)
    (transferred : OwnedCall.take external allocator prepared = (.ok (), called))
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = q.deterministic request.item)
    (miss : MissContinuation external budget allocator p q observations model source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing) :
    let input := { before with memory := { before.memory with memory } }
    let body := findBody external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let actual := find external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    ordinary body.1 = true →
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro input body actual logical completed
  let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
  let init := Initialization.capture external budget allocator commutative source buffer request.arguments input.memory
  obtain ⟨lookup, captured, prefixProof⟩ := initialized_taken_recorded external budget allocator commutative source request
    before memory pointer values prepared called leading other read sequence valid represented allocated decoded admitted initialized transferred
  let handle := init.2.effects.handle
  let taken := Take.capture external allocator lookup.origin handle prepared.world.memory
  let missLeading := leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
  obtain ⟨slice, remaining, _, _, _, _, _, _, normalizedResult, takenRecord, prefixProof⟩ := prefixProof
  let entry : Recorded σ := ⟨⟨input, { lookup := none }⟩, {}, leading⟩
  let normalized := record (Caller.initLookup external budget allocator source buffer request)
    (initialization external budget allocator source buffer request) entry
  let missEntry : Recorded σ := ⟨called, { lookup := some taken.1.2, items := remaining.values, phase := .cleanup }, missLeading⟩
  change ∀ suffix : List ProtocolEvent,
    let r := resources (missLeading ++ suffix) (.preparation .incomplete)
    let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
    let takeScope := Interner.Scoped.take r initialScope.2
    initialScope.1 = .ok values ∧ takeScope.1 = .ok () ∧ takeScope.2 = scopeView missEntry at prefixProof
  let missBodyResult := missBody external budget allocator p q observations source buffer request key deterministic missEntry
  have routed := findBody_taken external budget allocator p q observations source buffer request key deterministic values
    entry normalized.2 missEntry room (Prod.ext normalizedResult rfl) classified made absent takenRecord
  change body = missBodyResult at routed
  have actualEq : actual = finish external allocator missBodyResult.1 missBodyResult.2 := by
    change finish external allocator body.1 body.2 = _
    rw [routed]
  have ordinaryMiss : ordinary missBodyResult.1 = true := by rw [← routed]; exact completed
  have checked := miss values key deterministic room normalizedResult classified made absent (congrArg Prod.fst takenRecord)
  simp only [takenRecord] at checked
  have finished := checked ordinaryMiss
  obtain ⟨suffix, history⟩ := miss_finish_history external budget allocator p q observations source buffer request key deterministic missEntry
  have events : actual.2.events = missLeading ++ suffix := by rw [actualEq]; exact history
  let r := resources (actual.2.events ++ trailing) (.preparation .incomplete)
  let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
  obtain ⟨initialResult, takeResult, takeState⟩ := prefixProof (suffix ++ trailing)
  have normalizedScope : initialScope = (.ok values, initialScope.2) := by
    have result : initialScope.1 = .ok values := by
      simpa only [initialScope, r, events, List.append_assoc] using initialResult
    exact Prod.ext result rfl
  have takenScope : Interner.Scoped.take r initialScope.2 = (.ok (), scopeView missEntry) := by
    apply Prod.ext
    · simpa only [initialScope, r, events, List.append_assoc] using takeResult
    · simpa only [initialScope, r, events, List.append_assoc] using takeState
  have logicalRoute := scoped_taken r model request key deterministic values
    { before.graph with allocationCursor := leading.length } initialScope.2 (scopeView missEntry)
    (capacityQuery.trans room) normalizedScope (classificationQuery.trans classified) made absent takenScope
  change logical = _ at logicalRoute
  rw [logicalRoute, actualEq]
  simpa only [r, actualEq] using finished

/-- Every source entry branch uses the same actual stream. Initialization,
classification, cache lookup and take outcomes are inspected here, not supplied
by the client. Only the reached miss needs a continuation proof. Ordinary
failure includes allocation refusal; semantic faults remain outside this
ordinary-return relation rather than being reclassified as allocation failure. -/
theorem find_projected (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives)
    (source : View) (request : Interner.Request) (before : World σ)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted external)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = q.deterministic request.item)
    (miss : MissContinuation external budget allocator p q observations model source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing) :
    let input := { before with memory := { before.memory with memory } }
    let body := findBody external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let actual := find external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    ordinary body.1 = true →
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro input body actual logical completed
  let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
  obtain ⟨scratchValid, scratchRepresents, scratch, _⟩ :=
    caller_buffer before.memory memory pointer source request.arguments valid represented allocated
  have good : Good source request.arguments input := ⟨scratchValid, scratchRepresents⟩
  cases room : q.atCapacity before.graph with
  | true =>
    exact (capacity_projected external budget allocator p q observations model source buffer request input leading trailing
      good room capacityQuery).2.2.2
  | false =>
    generalize initialized : Caller.initLookup external budget allocator source buffer request
      ⟨input, { lookup := none }⟩ = initial
    obtain ⟨result, prepared⟩ := initial
    dsimp only [input, buffer] at initialized
    cases result with
    | error fault =>
      have ordinaryFailure : ordinary (.error fault : Except Fault NodeId) = true := by
        simpa only [body, findBody, Interner.FindCode.controlRun, execution, bind, Effect.bind, record, unchanged,
          input, List.append_nil, room, Bool.false_eq_true, ↓reduceIte, initialized] using completed
      exact (initialization_failed_projected external budget allocator p q observations model source buffer request input
        fault prepared leading trailing other read sequence good scratch rfl admitted room initialized ordinaryFailure capacityQuery).2.2.2.2
    | ok values =>
      obtain ⟨commutative, decoded⟩ : ∃ commutative, Interner.Scoped.commutative request.item = .ok commutative := by
        cases decoded : Interner.Scoped.commutative request.item with
        | error error => simp only [Caller.initLookup, decoded] at initialized; cases initialized
        | ok commutative => exact ⟨commutative, rfl⟩
      obtain ⟨key, made⟩ := Caller.initialized_key external budget allocator source buffer request _ prepared values initialized
      cases classified : q.deterministic request.item with
      | error error =>
        have ordinaryFailure : ordinary (.error (.language error) : Except Fault NodeId) = true := by
          simpa only [body, findBody, Interner.FindCode.controlRun, execution, bind, Effect.bind, record, unchanged,
            input, List.append_nil, room, Bool.false_eq_true, ↓reduceIte, initialized, classified, Except.mapError] using completed
        exact (classification_projected external budget allocator commutative p q observations model source request before
          memory pointer values prepared error leading trailing other read sequence valid represented allocated decoded admitted
          initialized room classified ordinaryFailure capacityQuery classificationQuery).2.2.2
      | ok deterministic =>
        have missed (absent : deterministic = true → before.graph.table key = none) :
            (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
          generalize transferred : OwnedCall.take external allocator prepared = transfer
          obtain ⟨result, called⟩ := transfer
          cases result with
          | error fault =>
            exact (take_failed_projected external budget allocator commutative p q observations model source request before
              memory pointer values prepared called fault key deterministic leading trailing other read sequence valid represented
              allocated decoded admitted initialized room classified made absent transferred capacityQuery classificationQuery).2.2.2.2
          | ok value =>
            cases value
            exact taken_find_projected external budget allocator commutative p q observations model source request before
              memory pointer values prepared called key deterministic leading trailing other read sequence valid represented allocated
              decoded admitted initialized room classified made absent transferred capacityQuery classificationQuery miss completed
        cases deterministic with
        | false => exact missed (by intro impossible; cases impossible)
        | true =>
          cases cached : before.graph.table key with
          | none => exact missed (fun _ => cached)
          | some id =>
            exact (lookup_projected external budget allocator commutative p q observations model source request before
              memory pointer values prepared (.ok id) leading trailing other read sequence valid represented allocated decoded admitted
              initialized room classified (by intro found same; cases same; exact ⟨key, made, cached⟩) rfl
              capacityQuery classificationQuery).2.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
