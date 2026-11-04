/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolLookup
import Compiler.Extraction.InternerCallerCacheStream

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace

attribute [local irreducible] Initialization.capture Close.capture

/-- A real cache-hit body computes its complete protocol observation. The token
comes from the actual successful initializer; no child events or supplied trace
are needed. Cleanup is observed only at this body's reached native scope. -/
theorem cached_events (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (request : Interner.Request) (before : World σ) (values : List NodeId) (prepared : OwnedCall.State σ)
    (key : Key) (id : NodeId) (leading : List ProtocolEvent)
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (initialized : Caller.initLookup external budget allocator source buffer request
      ⟨before, { lookup := none }⟩ = (.ok values, prepared))
    (room : q.atCapacity before.graph = false) (classified : q.deterministic request.item = .ok true)
    (made : Interner.makeKey request values = .ok key) (found : before.graph.table key = some id) :
    let init := Initialization.capture external budget allocator commutative source buffer request.arguments before.memory
    let actual := find external budget allocator p q observations source buffer request
      ⟨⟨before, { lookup := none }⟩, {}, leading⟩
    ∃ lookup, init.1 = .ok (some lookup) ∧
      let close := Close.capture external allocator lookup .lookup init.2.effects.handle prepared
      actual.2.events = leading ++ init.2.events.map Event.normalization ++ close.2.events.map Event.normalization ∧
      actual.2.tokens.incomplete = false ∧ actual.2.tokens.lookup = some close.1 ∧
      actual.2.tokens.toScope = ⟨some close.1, values, .lookup⟩ := by
  intro init actual
  obtain ⟨lookup, captured, state, contents, _⟩ := Initialization.capture_success external budget allocator commutative
    source buffer request before values prepared decoded initialized
  refine ⟨lookup, captured, ?_⟩
  intro close
  obtain ⟨bodyLookup, bodyCapture, body⟩ := lookup_body external budget allocator commutative p q observations
    source buffer request before values prepared (.ok id) leading decoded initialized room classified
    (by intro foundId returned; cases Except.ok.inj returned; exact ⟨key, made, found⟩)
  have same := Option.some.inj (Except.ok.inj (bodyCapture.symm.trans captured))
  subst bodyLookup
  have locals : prepared.scope = { lookup := some init.2.effects.handle } := congrArg OwnedCall.State.scope state
  simp only [actual, find, invoke, body, Except.mapError, finish, ordinary, ↓reduceIte, record, closing, locals]
  exact ⟨rfl, trivial, rfl, congrArg (fun items => (⟨some close.1, items, .lookup⟩ : Interner.Scoped.Scope)) contents⟩

/-- A complete actual cache-hit caller projects to the scoped source caller
using its own computed stream, including the final retained ownership state.
The shared initialized-return proof derives the native lifetime obligations;
no event list, cleanup postcondition or full-caller simulation is assumed. -/
theorem cached_projected (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives) (source : View)
    (request : Interner.Request) (before : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared : OwnedCall.State σ)
    (key : Key) (id : NodeId) (leading trailing : List ProtocolEvent)
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
    let actual := find external budget allocator p q observations source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨input, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    actual.1 = .ok id ∧ Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧
      actual.2.tokens.incomplete = false := by
  exact lookup_projected external budget allocator commutative p q observations model source request before memory pointer
    values prepared (.ok id) leading trailing other read sequence valid represented allocated decoded admitted initialized
    room classified (by intro foundId returned; cases Except.ok.inj returned; exact ⟨key, made, found⟩)
    rfl capacityQuery classificationQuery

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
