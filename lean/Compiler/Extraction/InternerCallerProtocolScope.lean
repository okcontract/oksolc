/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolTrace
import Compiler.Extraction.InternerCallerTakeVerified
import Compiler.Extraction.InternerCallerCloseVerified

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ResourceAdapter Interner.InvocationTrace

/-- Native cleanup may retire its descriptors. The existing scoped ownership
state remains local to the recorder; its cursor is the actual protocol length. -/
def scopeView (before : Recorded σ) : Interner.Scoped.Session :=
  ⟨before.tokens.toScope, { before.native.world.graph with allocationCursor := before.events.length }⟩

attribute [local irreducible] Initialization.capture Take.capture Close.capture

/-- Ordinary initialization binds the recorded local state to the accepted
scoped initializer, including refused temporary allocation. Native memory,
argument normalization and lifetime facts come from the existing refinement. -/
theorem initialization_projected (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (scratch : commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (bufferLength : buffer.length = 2) (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (admitted : Admitted external)
    (ordinaryInit : ordinary (Caller.initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩).1 = true) :
    let input : Recorded σ := ⟨⟨before, { lookup := none }⟩, {}, leading⟩
    let actual := record (Caller.initLookup external budget allocator source buffer request)
      (initialization external budget allocator source buffer request) input
    let captured := Initialization.capture external budget allocator commutative source buffer request.arguments before.memory
    let logical := Interner.Scoped.initScope (resources (actual.2.events ++ trailing) (.preparation .incomplete)) request (scopeView input)
    Initialization.checked captured (normalizations leading) (normalizations trailing) request (scopeView input).heap = .ok logical ∧
      Initialization.Coupled allocator source request before actual.2.events.length captured.2.effects.session
        (actual.1, actual.2.native) logical other read sequence ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro input actual captured logical
  have events : actual.2.events = leading ++ captured.2.events.map Event.normalization := by
    simp only [actual, record, initialization, input, decoded]
    rfl
  have accepted : Initialization.checked captured (normalizations leading) (normalizations trailing) request
      (scopeView input).heap = .ok logical := by
    have checked := Initialization.checked_ordinary external budget allocator commutative source buffer request before
      (normalizations leading) (normalizations trailing) (scopeView input).heap represented.1 bufferLength decoded ordinaryInit
      (by simp only [scopeView, input, normalizations_length])
    simpa only [logical, resources, events, normalizations_append, normalizations_embed, List.append_assoc] using checked
  have coupled := Initialization.coupled external budget allocator commutative source buffer request before
    (normalizations leading) (normalizations trailing) logical other read sequence valid represented scratch bufferLength decoded admitted
    (by simpa only [normalizations_length] using accepted)
  obtain ⟨lookup, capturedResult, _, scopedLookup, scopedResult, _, _⟩ := Initialization.checked_scope external budget allocator
    commutative source buffer request before.memory (scopeView input).heap (normalizations leading) (normalizations trailing)
    logical represented.1 bufferLength decoded (by simp only [scopeView, input, normalizations_length]) accepted
  have contents := NormalizationOwnership.Trace.Scope.checked_init_scope _ _ _ _ _
    (TraceBridge.check_physical_sound _ _ _ accepted).2
  have shape : logical.2.scope = ⟨lookup, logical.1.toOption.getD [], .lookup⟩ := by
    change (⟨logical.2.scope.lookup, logical.2.scope.items, logical.2.scope.phase⟩ : Interner.Scoped.Scope) = _
    rw [scopedLookup, contents.1, contents.2]
  have localScope : actual.2.tokens.toScope = logical.2.scope := by
    rw [shape, scopedResult]
    cases lookup with
    | none => simp only [actual, record, initialization, input, decoded, capturedResult]; rfl
    | some lookup =>
      have returned : (Caller.initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩).1 =
          .ok (normalized commutative source request.arguments) := coupled.1.trans (congrArg (Except.mapError Fault.language) scopedResult)
      obtain ⟨_, _, _, values, _⟩ := Initialization.capture_success external budget allocator commutative source buffer request before
        _ _ decoded (Prod.ext returned rfl)
      simp only [actual, record, initialization, input, decoded, capturedResult, Except.toOption, Option.getD_some]
      exact congrArg (fun items => (⟨some lookup, items, .lookup⟩ : Interner.Scoped.Scope)) values
  refine ⟨accepted, ?_, Prod.ext coupled.1 ?_, ?_⟩
  · simpa only [events, List.length_append, List.length_map, normalizations_length] using coupled
  · change (⟨actual.2.tokens.toScope, { actual.2.native.world.graph with allocationCursor := actual.2.events.length }⟩ : Interner.Scoped.Session) = _
    have graph : actual.2.native.world.graph = before.graph := coupled.2.1
    rw [localScope, graph]
    change (⟨logical.2.scope, _⟩ : Interner.Scoped.Session) = ⟨logical.2.scope, logical.2.heap⟩
    rw [coupled.2.2.2.1]
    simp only [events, List.length_append, List.length_map, normalizations_length]
    rfl
  · simp only [actual, record, initialization, input, decoded]

/-- Both successful duplication and allocation refusal project from the actual
recorded take. Readiness and admitted host behavior derive physical acceptance;
neither a successful allocation nor a projected result is assumed. -/
theorem take_projected (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (leading trailing : List ProtocolEvent) (ready : Ready allocator source original handle before.memory)
    (admitted : Admitted external) :
    let input : Recorded σ := ⟨⟨before, { lookup := some handle }⟩,
      { lookup := some (token origin handle), items := handle.values }, leading⟩
    let actual := record (OwnedCall.take external allocator) (taking external allocator) input
    let captured := Take.capture external allocator origin handle before.memory
    let logical := Interner.Scoped.take (resources (actual.2.events ++ trailing) (.preparation .incomplete)) (scopeView input)
    Take.checked captured (normalizations leading) (normalizations trailing) (token origin handle) handle.values
      (scopeView input).heap = .ok logical ∧
      Take.Coupled allocator source original handle before actual.2.events.length captured.2.effects.session captured.1
        (actual.1, actual.2.native) logical ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧
      actual.2.tokens.incomplete = false := by
  intro input actual captured logical
  have verified := Take.verified external allocator origin source original handle before
    (normalizations leading) (normalizations trailing) ready admitted
  have events : actual.2.events = leading ++ captured.2.events.map Event.normalization := rfl
  have accepted : Take.checked captured (normalizations leading) (normalizations trailing) (token origin handle) handle.values
      (scopeView input).heap = .ok logical := by
    simpa only [logical, scopeView, input, events, resources, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc] using verified.1
  have coupled : Take.Coupled allocator source original handle before actual.2.events.length captured.2.effects.session captured.1
      (actual.1, actual.2.native) logical := by
    simpa only [logical, scopeView, input, events, resources, normalizations_append, normalizations_embed,
      normalizations_length, List.length_append, List.length_map, List.append_assoc] using verified.2
  refine ⟨accepted, coupled, Prod.ext coupled.1 ?_, rfl⟩
  rw [coupled.2.2.2.1]
  simp only [scopeView, actual, record, taking, input, token, List.length_append, List.length_map]
  congr 1
  exact congrArg (fun graph => { graph with allocationCursor := leading.length + captured.2.events.length }) coupled.2.1

/-- Handoff changes only the caller's existing scoped phase. It emits no
allocation event and remains exact for arbitrary graphs, history and tokens. -/
theorem handoff_projected (before : Recorded σ) :
    let actual := record OwnedCall.handoff handingOff before
    (actual.1, scopeView actual.2) =
      ((Interner.Scoped.handoff (scopeView before)).1.mapError Fault.language,
        (Interner.Scoped.handoff (scopeView before)).2) ∧
      actual.2.events = before.events ∧ actual.2.tokens.incomplete = before.tokens.incomplete := by
  simp only [record, OwnedCall.handoff, handingOff, scopeView, Interner.Scoped.handoff, List.append_nil, Except.mapError]
  exact ⟨trivial, trivial, trivial⟩

/- The shared close adapter consumes existing native lifetime proofs. Its
callers below derive these premises for lookup and taken states. -/
theorem close_from_cleanup (external : External σ) (allocator : Nat) (before after : OwnedCall.State σ)
    (handle : Handle) (lookup : NormalizationOwnership.State) (items : List NodeId)
    (leading trailing : List ProtocolEvent) (present : before.scope.lookup = some handle)
    (corresponds : Close.observe before (Close.capture external allocator lookup
      (if before.scope.handedOff then .transfer else if before.scope.slice.isSome then .cleanup else .lookup) handle before).2.effects =
        some (cleanup external allocator before))
    (closed : cleanup external allocator before = (.ok (), after)) (graph : after.world.graph = before.world.graph) :
    let phase : NormalizationOwnership.Exit := if before.scope.handedOff then .transfer else if before.scope.slice.isSome then .cleanup else .lookup
    let input : Recorded σ := ⟨before, { lookup := some lookup, items, phase }, leading⟩
    let actual := record (cleanup external allocator) (closing external allocator) input
    let captured := Close.capture external allocator lookup phase handle before
    let logical := Interner.Scoped.close (resources (actual.2.events ++ trailing) (.preparation .incomplete)) (scopeView input)
    actual.1 = .ok () ∧ actual.2.native = after ∧
      Close.checked captured (normalizations leading) (normalizations trailing) lookup phase items (scopeView input).heap = .ok logical ∧
      scopeView actual.2 = logical ∧ actual.2.tokens.incomplete = false := by
  intro phase input actual captured logical
  have events : actual.2.events = leading ++ captured.2.events.map Event.normalization := by
    simp only [actual, record, input, closing, present]
    rfl
  have checked := Close.checked_of_cleanup external allocator lookup phase handle before after
    (normalizations leading) (normalizations trailing) items (scopeView input).heap
    (by simp only [scopeView, input, normalizations_length]) corresponds closed
  have accepted : Close.checked captured (normalizations leading) (normalizations trailing) lookup phase items (scopeView input).heap = .ok logical := by
    simpa only [logical, resources, events, normalizations_append, normalizations_embed, List.append_assoc] using checked.2.1
  have shape : logical = ⟨⟨some captured.1, items, phase⟩,
      { before.world.graph with allocationCursor := actual.2.events.length }⟩ := by
    simpa only [logical, resources, scopeView, input, events, normalizations_append, normalizations_embed,
      normalizations_length, List.append_assoc, List.length_append, List.length_map] using checked.2.2
  refine ⟨congrArg Prod.fst closed, congrArg Prod.snd closed, accepted, ?_, ?_⟩
  · rw [shape]
    simp only [scopeView, actual, record, input, closing, present, closed, graph]
    rfl
  · simp only [actual, record, input, closing, present]

/-- A ready lookup closes at the reached native memory. Its recorded scope
retains the normalized arguments even when native cleanup removes the handle. -/
theorem lookup_close_projected (external : External σ) (allocator : Nat) (origin : NormalizationOwnership.Origin)
    (source : View) (original : List NodeId) (handle : Handle) (before : World σ)
    (leading trailing : List ProtocolEvent) (ready : Ready allocator source original handle before.memory) :
    let input : Recorded σ := ⟨⟨before, { lookup := some handle }⟩,
      { lookup := some (token origin handle), items := handle.values }, leading⟩
    let actual := record (cleanup external allocator) (closing external allocator) input
    let captured := Close.capture external allocator (token origin handle) .lookup handle input.native
    let logical := Interner.Scoped.close (resources (actual.2.events ++ trailing) (.preparation .incomplete)) (scopeView input)
    actual.1 = .ok () ∧ Good source original actual.2.native.world ∧ Closed actual.2.native.scope ∧
      Close.checked captured (normalizations leading) (normalizations trailing) (token origin handle) .lookup handle.values
        (scopeView input).heap = .ok logical ∧ scopeView actual.2 = logical ∧ actual.2.tokens.incomplete = false := by
  intro input actual captured logical
  obtain ⟨after, closed, good, locals, graph, _, _⟩ := Close.lookup_verified external allocator origin
    source original handle before ready (normalizations leading) (normalizations trailing)
  have projected := close_from_cleanup external allocator input.native after handle (token origin handle) handle.values leading trailing
    rfl (Close.lookup_spec external allocator origin handle before) closed graph
  exact ⟨projected.1, projected.2.1 ▸ good, projected.2.1 ▸ locals, projected.2.2⟩

/-- Taken cleanup covers retained and transferred buffers in one theorem.
The actual handoff flag selects the phase; lifetime and separation discharge
native cleanup, rather than trusting the recorded token's completeness flag. -/
theorem taken_close_projected (external : External σ) (allocator : Nat) (lookup : NormalizationOwnership.State)
    (source : View) (original : List NodeId) (handle : Handle) (slice : ArgumentSlice) (handedOff : Bool) (before : World σ)
    (leading trailing : List ProtocolEvent) (detached : handle.owned = none) (unowned : lookup.owned = false)
    (owner : lookup.owner = .caller) (good : Good source original before)
    (live : handedOff = false → SliceValid allocator before.memory.heap slice)
    (separate : original ≠ [] → source.allocation ≠ slice.address) :
    let phase : NormalizationOwnership.Exit := if handedOff then .transfer else .cleanup
    let native : OwnedCall.State σ := ⟨before, ⟨some handle, some slice, handedOff⟩⟩
    let input : Recorded σ := ⟨native, { lookup := some lookup, items := handle.values, phase }, leading⟩
    let actual := record (cleanup external allocator) (closing external allocator) input
    let captured := Close.capture external allocator lookup phase handle native
    let logical := Interner.Scoped.close (resources (actual.2.events ++ trailing) (.preparation .incomplete)) (scopeView input)
    actual.1 = .ok () ∧ CleanupPost external allocator source original slice native actual.2.native ∧
      Close.checked captured (normalizations leading) (normalizations trailing) lookup phase handle.values (scopeView input).heap = .ok logical ∧
      scopeView actual.2 = logical ∧ actual.2.tokens.incomplete = false := by
  intro phase native input actual captured logical
  obtain ⟨after, closed, post, _, _⟩ := Close.taken_verified external allocator lookup source original handle slice handedOff before
    detached unowned owner good live separate (normalizations leading) (normalizations trailing)
  have projected := close_from_cleanup external allocator native after handle lookup handle.values leading trailing rfl
    (Close.taken_spec external allocator lookup handle slice handedOff before detached unowned owner) closed post.graph
  exact ⟨projected.1, projected.2.1 ▸ post, projected.2.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
