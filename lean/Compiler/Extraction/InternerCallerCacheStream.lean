/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitializedStream
import Compiler.Extraction.InternerCallerCloseVerified
import Compiler.Extraction.InternerCallerNativeRouting
import Compiler.Extraction.InternerInvocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.CacheStream
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ResourceAdapter Interner.InvocationTrace

/-- The scoped source body returns an actual cache hit before take or any graph
callback, then closes its initialized lookup. -/
theorem scoped_cached (resources : Interner.Scoped.Resources) (model : Interner.Primitives)
    (request : Interner.Request) (before : Interner.Heap) (values : List NodeId)
    (prepared : Interner.Scoped.Session) (key : Key) (id : NodeId)
    (room : model.atCapacity before = false)
    (initialized : Interner.Scoped.initScope resources request ⟨{}, before⟩ = (.ok values, prepared))
    (classified : model.deterministic request.item = .ok true)
    (made : Interner.makeKey request values = .ok key) (found : before.table key = some id) :
    Interner.Scoped.findDetailed resources model request before = (.ok id, Interner.Scoped.close resources prepared) := by
  unfold Interner.Scoped.findDetailed Interner.Scoped.finish Interner.FindCode.controlRun
  simp only [Interner.Scoped.execution, Interner.Scoped.liftGraph, Interner.get, Interner.lift,
    bind, Effect.bind, room, Bool.false_eq_true, ↓reduceIte, initialized, classified, made, found]
  rfl

attribute [local irreducible] Initialization.capture Close.capture

/-- The cache-hit leaf has one exact initialized/closed tagged stream. The real
initialization supplies its handle and token; readiness proves reached cleanup.
No take, child trace, suffix lifetime contract or cursor equation is assumed.
Query observations bind the native and scoped source guards at their inputs. -/
theorem cached (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (model : Interner.Primitives) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : OwnedCall.State σ)
    (key : Key) (id : NodeId) (leading trailing : List (Event Failure ι))
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (room : q.atCapacity before.graph = false) (classified : q.deterministic request.item = .ok true)
    (made : Interner.makeKey request values = .ok key) (found : before.graph.table key = some id)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = q.deterministic request.item) :
    let input := { before with memory := { before.memory with memory } }
    let initialization := Initialization.capture external budget allocator commutative source
      ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments input.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let close := Close.capture external allocator lookup .lookup handle prepared
      let closeLeading := leading ++ initialization.2.events.map Event.normalization
      let events := closeLeading ++ close.2.events.map Event.normalization ++ trailing
      let r := resources events (.preparation .incomplete)
      let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
      let logical := Interner.Scoped.findDetailed r model request { before.graph with allocationCursor := leading.length }
      ∃ after, Caller.find external budget allocator p q source ⟨before.memory.memory.nextId, 0, 2⟩ request input = (.ok id, after) ∧
        Good source request.arguments after.world ∧ Closed after.scope ∧ after.world.graph = before.graph ∧
        after.world.memory = close.2.effects.session ∧
        Initialization.checked initialization (normalizations leading) (close.2.events ++ normalizations trailing) request
          { before.graph with allocationCursor := leading.length } = .ok initialScope ∧
        Close.checked close (normalizations closeLeading) (normalizations trailing) lookup .lookup values initialScope.2.heap = .ok logical.2 ∧
        logical.1 = .ok id ∧
        logical.2 = ⟨⟨some close.1, values, .lookup⟩,
          { after.world.graph with allocationCursor := (closeLeading ++ close.2.events.map Event.normalization).length }⟩ := by
  intro input initialization
  obtain ⟨lookup, captured, state, contents, tokenEq, prefixProof⟩ := Initialization.successful_stream external budget allocator
    commutative source request before memory pointer values prepared (normalizations leading) other read sequence
    valid represented allocated decoded admitted initialized
  refine ⟨lookup, captured, ?_⟩
  intro handle close closeLeading events r initialScope logical
  have tokenEq : lookup = token lookup.origin handle := tokenEq
  have contents : handle.values = values := contents
  have ready := (prefixProof []).2.2.2.2.2.2 values rfl
  obtain ⟨nativeHandle, nativeLookup, present, _, _, ready, _, _, _, _⟩ := ready
  have sameHandle : nativeHandle = handle := Option.some.inj (present.symm.trans
    (congrArg (fun s : OwnedCall.State σ => s.scope.lookup) state))
  subst nativeHandle
  have nativeState : (⟨prepared.world, { lookup := some handle }⟩ : OwnedCall.State σ) = prepared := by rw [state]
  have closed := Close.lookup_verified external allocator lookup.origin source request.arguments handle prepared.world ready
    (normalizations closeLeading) (normalizations trailing)
  simp only [nativeState, ← tokenEq] at closed
  obtain ⟨after, cleaned, good, locals, graph, reached, closeChecked⟩ := closed
  have graphBefore : prepared.world.graph = before.graph := congrArg (fun s : OwnedCall.State σ => s.world.graph) state
  have finished : finish external allocator (.ok id) prepared = (.ok id, after) := by
    simp only [finish, ordinary, ↓reduceIte, cleaned]
  have called := Caller.find_cached external budget allocator p q source ⟨before.memory.memory.nextId, 0, 2⟩
    request input values prepared key id room initialized classified made found
  have initialProof := prefixProof (close.2.events ++ normalizations trailing)
  have initialCheck : Initialization.checked initialization (normalizations leading) (close.2.events ++ normalizations trailing) request
      { before.graph with allocationCursor := leading.length } = .ok initialScope := by
    simpa only [initialScope, r, events, closeLeading, resources, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc] using initialProof.1
  have known : Initialization.Coupled allocator source request input (leading.length + initialization.2.events.length)
      initialization.2.effects.session (.ok values, prepared) initialScope other read sequence := by
    simpa only [initialScope, r, events, closeLeading, resources, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc] using initialProof.2
  have initialResult : initialScope.1 = .ok values := by
    cases returned : initialScope.1 with
    | error fault =>
      have impossible := known.1
      rw [returned] at impossible
      cases impossible
    | ok items => simpa only [returned, Except.mapError, Except.ok.injEq] using known.1.symm
  obtain ⟨_, observed, _, scopedLookup, _, _, _⟩ := Initialization.checked_scope external budget allocator commutative
    source ⟨before.memory.memory.nextId, 0, 2⟩ request input.memory { before.graph with allocationCursor := leading.length }
    (normalizations leading) (close.2.events ++ normalizations trailing) initialScope represented.1 rfl decoded
    (by simp only [normalizations_length]) initialCheck
  have sameLookup := Except.ok.inj (captured.symm.trans observed)
  rw [← sameLookup] at scopedLookup
  obtain ⟨_, scopedToken, _, presentToken, _, _, _, _, _, scopeShape⟩ := known.2.2.2.2.2 values rfl
  have sameToken : scopedToken = lookup := Option.some.inj (presentToken.symm.trans scopedLookup)
  subst scopedToken
  have modelRun := scoped_cached r model request { before.graph with allocationCursor := leading.length }
    values initialScope.2 key id (capacityQuery.trans room) (Prod.ext initialResult rfl) (classificationQuery.trans classified) made found
  change logical = (.ok id, Interner.Scoped.close r initialScope.2) at modelRun
  have closedProjection := Close.capture_replays_at external allocator lookup .lookup handle prepared
    (normalizations closeLeading) (normalizations trailing)
  have initialState : initialScope.2 = ⟨⟨some lookup, values, .lookup⟩,
      { prepared.world.graph with allocationCursor := closeLeading.length }⟩ := by
    have heapShape : initialScope.2.heap = { prepared.world.graph with allocationCursor := closeLeading.length } := by
      rw [known.2.2.2.1, graphBefore]
      simp only [closeLeading, List.length_append, List.length_map]
      rfl
    change (⟨initialScope.2.scope, initialScope.2.heap⟩ : Interner.Scoped.Session) = _
    rw [scopeShape, heapShape]
  have logicalState : logical.2 = ⟨⟨some close.1, values, .lookup⟩,
      { prepared.world.graph with allocationCursor := closeLeading.length + close.2.events.length }⟩ := by
    rw [modelRun, initialState]
    dsimp only
    simp only [r, resources]
    rw [NormalizationOwnership.Trace.Scope.close_projection]
    simpa only [events, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc] using congrArg
        (fun pair => (⟨⟨some pair.1, values, .lookup⟩,
          { prepared.world.graph with allocationCursor := pair.2 }⟩ : Interner.Scoped.Session)) closedProjection
  refine ⟨after, called.trans finished, good, locals, graph.trans graphBefore, reached, initialCheck, ?_, ?_, ?_⟩
  · rw [logicalState, initialState]
    simpa only [normalizations_length, contents] using closeChecked
  · exact congrArg Prod.fst modelRun
  · rw [logicalState, graph]
    simp only [List.length_append, List.length_map]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.CacheStream
