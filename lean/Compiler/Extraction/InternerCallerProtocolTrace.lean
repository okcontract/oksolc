/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitialization
import Compiler.Extraction.InternerCallerClose
import Compiler.Extraction.InternerInvocationTrace
import Compiler.Extraction.InternerInsertionNative

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Interner.InvocationTrace

abbrev ProtocolEvent := Event Failure Insertion.Native.Fault

/-- Protocol descriptors belong to this caller, not to a recursive child. A
missing descriptor is recorded explicitly; erasure alone is not acceptance. -/
structure Tokens extends Interner.Scoped.Scope where
  incomplete : Bool := false
  deriving DecidableEq, Repr

/-- The existing native state is retained, with local protocol instrumentation.
Graph callbacks see only the native world, never these caller-local tokens. -/
structure Recorded (σ : Type) where
  native : OwnedCall.State σ
  tokens : Tokens := {}
  events : List ProtocolEvent := []

abbrev Action (σ α : Type) := Effect (Recorded σ) Fault α
abbrev Observation (σ : Type) := OwnedCall.State σ → Tokens → Tokens × List ProtocolEvent

def prepend (leading : List ProtocolEvent) (before : Recorded σ) : Recorded σ :=
  { before with events := leading ++ before.events }

/-- Observe at exactly the input consumed by the native action. Observation
cannot change the action's result, memory, graph or caller scope. -/
def record (action : OwnedCall.Action σ α) (observe : Observation σ) : Action σ α := fun before =>
  let actual := action before.native
  let observed := observe before.native before.tokens
  (actual.1, ⟨actual.2, observed.1, before.events ++ observed.2⟩)

theorem record_erases (action : OwnedCall.Action σ α) (observe : Observation σ) :
    Effect.Transport Recorded.native (record action observe) action := fun _ => rfl

theorem record_prefix (action : OwnedCall.Action σ α) (observe : Observation σ) (leading : List ProtocolEvent) :
    Effect.Transport (prepend leading) (record action observe) (record action observe) := by
  intro before
  simp only [record, prepend, List.append_assoc]

def unchanged : Observation σ := fun _ tokens => (tokens, [])

/-- Read the existing initialization recorder at the actual source arguments.
Classification failures never run normalization and contribute no events. -/
def initialization (external : External σ) (budget allocator : Nat) (source buffer : View)
    (request : Interner.Request) : Observation σ := fun before tokens =>
  match Interner.Scoped.commutative request.item with
  | .error _ => (tokens, [])
  | .ok commutative =>
    let captured := Initialization.capture external budget allocator commutative source buffer request.arguments before.world.memory
    let scope : Interner.Scoped.Scope := match captured.1 with
      | .ok (some lookup) => ⟨some lookup, captured.2.effects.handle.values, .lookup⟩
      | _ => {}
    ({ tokens with toScope := scope }, captured.2.events.map Event.normalization)

def taking (external : External σ) (allocator : Nat) : Observation σ := fun before tokens =>
  match before.scope.lookup, tokens.lookup with
  | none, _ => (tokens, [])
  | some _, none => ({ tokens with incomplete := true }, [])
  | some handle, some lookup =>
    let captured := Take.capture external allocator lookup.origin handle before.world.memory
    ({ tokens with lookup := some captured.1.2, phase := if captured.1.1 then .cleanup else tokens.phase },
      captured.2.events.map Event.normalization)

/-- Retain the existing scoped handoff after native cleanup clears descriptors.
The native result remains authoritative; this observation grants no admission. -/
def handingOff : Observation σ := fun _ tokens => ({ tokens with phase := .transfer }, [])

def closing (external : External σ) (allocator : Nat) : Observation σ := fun before tokens =>
  match before.scope.lookup, tokens.lookup with
  | none, _ => ({ tokens with incomplete := tokens.incomplete || (!before.scope.handedOff && before.scope.slice.isSome) }, [])
  | some _, none => ({ tokens with incomplete := true }, [])
  | some handle, some lookup =>
    let phase := if before.scope.handedOff then NormalizationOwnership.Exit.transfer
      else if before.scope.slice.isSome then .cleanup else .lookup
    let captured := Close.capture external allocator lookup phase handle before
    ({ tokens with lookup := some captured.1 }, captured.2.events.map Event.normalization)

/-- These three observations are the remaining graph obligations. Initialization,
take and close are already bound above to their actual native recorders. -/
structure GraphObservations (σ : Type) where
  simplify : Key → ArgumentSlice → World σ → List ProtocolEvent
  publish : Key → ArgumentSlice → NodeId → World σ → List ProtocolEvent
  insert : Key → ArgumentSlice → Bool → World σ → List ProtocolEvent

def graphObservation (observe : ArgumentSlice → World σ → List ProtocolEvent) : Observation σ := fun before tokens =>
  match before.scope.slice with
  | none => (tokens, [])
  | some slice => (tokens, observe slice before.world)

/-- A graph callback uses its actual native input and preserves the parent's
protocol token. A child cannot replace its caller's deferred-cleanup metadata. -/
theorem graph_recorded (action : ArgumentSlice → GraphAction σ α)
    (observe : ArgumentSlice → World σ → List ProtocolEvent) (before : Recorded σ) (slice : ArgumentSlice)
    (present : before.native.scope.slice = some slice) :
    let actual := record (graph action) (graphObservation observe) before
    (actual.1, actual.2.native) = graph action before.native ∧
      actual.2.events = before.events ++ observe slice before.native.world ∧ actual.2.tokens = before.tokens := by
  simp only [record, graphObservation, present]
  exact ⟨trivial, trivial, trivial⟩

/-- Interpret the existing source control with observed native operations.
No capacity/cache/miss branch or callback ordering is reimplemented here. -/
def execution (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) : Interner.Execution (Action σ) where
  get := record (fun before => (.ok before.world.graph, before)) unchanged
  lift := fun result => record (fun before => (result.mapError Fault.language, before)) unchanged
  atCapacity := q.atCapacity
  deterministic := q.deterministic
  normalize := fun request => record (Caller.initLookup external budget allocator source buffer request)
    (initialization external budget allocator source buffer request)
  takeOwned := fun _ => record (OwnedCall.take external allocator) (taking external allocator)
  handoff := record OwnedCall.handoff handingOff
  simplify := fun key => record (graph (p.simplify key)) (graphObservation (observations.simplify key))
  publish := fun key id => record (graph (fun slice => p.publish key slice id))
    (graphObservation (fun slice => observations.publish key slice id))
  insert := fun key deterministic => record (graph (fun slice => p.insert key slice deterministic))
    (graphObservation (fun slice => observations.insert key slice deterministic))

def findBody (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request) : Action σ NodeId :=
  Interner.findCode.controlRun (execution external budget allocator p q observations source buffer) request

def forceBody (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (id : NodeId) (item : Item) (values : List NodeId) : Action σ Unit :=
  Interner.forceCode.controlRun (execution external budget allocator p q observations source buffer) q.validate id item values

/-- Semantic failures retain the body state and events. Only the native
ordinary-outcome guard permits an observation of deferred cleanup. -/
def finish (external : External σ) (allocator : Nat) (result : Except Fault α) : Action σ α := fun before =>
  if ordinary result then
    let closed := record (cleanup external allocator) (closing external allocator) before
    (match closed.1 with | .error fault => .error fault | .ok () => result, closed.2)
  else (result, before)

def invoke (external : External σ) (allocator : Nat) (action : Action σ α) : Action σ α := fun before =>
  let actual := action before
  finish external allocator actual.1 actual.2

def find (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request) : Action σ NodeId :=
  invoke external allocator (findBody external budget allocator p q observations source buffer request)

def force (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (id : NodeId) (item : Item) (values : List NodeId) : Action σ Unit :=
  invoke external allocator (forceBody external budget allocator p q observations source buffer id item values)

theorem findBody_erases (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request) :
    Effect.Transport Recorded.native (findBody external budget allocator p q observations source buffer request)
      (Caller.findBody external budget allocator p q source buffer request) := by
  unfold findBody Caller.findBody Interner.FindCode.controlRun Interner.FindCode.controlOwned Interner.FindCode.controlMiss
  simp only [execution, Caller.execution, OwnedCall.execution]
  repeat first
    | exact record_erases _ _
    | exact Effect.Transport.pure Recorded.native _
    | apply Effect.Transport.bind Recorded.native
    | split
    | intro value

theorem forceBody_erases (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (id : NodeId) (item : Item) (values : List NodeId) :
    Effect.Transport Recorded.native (forceBody external budget allocator p q observations source buffer id item values)
      (Caller.forceBody external budget allocator p q source buffer id item values) := by
  unfold forceBody Caller.forceBody Interner.ForceCode.controlRun Interner.ForceCode.controlOwned
  simp only [execution, Caller.execution, OwnedCall.execution]
  repeat first
    | exact record_erases _ _
    | exact Effect.Transport.pure Recorded.native _
    | apply Effect.Transport.bind Recorded.native
    | split
    | intro value

theorem finish_erases (external : External σ) (allocator : Nat) (result : Except Fault α) :
    Effect.Transport Recorded.native (finish external allocator result) (OwnedCall.finish external allocator result) := by
  intro before
  unfold finish OwnedCall.finish
  split
  · dsimp only [record]
    cases cleanup external allocator before.native with
    | mk result after => cases result <;> rfl
  · rfl

theorem invoke_erases (external : External σ) (allocator : Nat) {left : Action σ α} {right : OwnedCall.Action σ α}
    (body : Effect.Transport Recorded.native left right) (before : Recorded σ) :
    (let actual := right before.native; OwnedCall.finish external allocator actual.1 actual.2) =
      ((invoke external allocator left before).1, (invoke external allocator left before).2.native) := by
  rw [body before]
  exact finish_erases external allocator _ _

theorem find_erases (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request)
    (before : World σ) (leading : List ProtocolEvent) :
    let actual := find external budget allocator p q observations source buffer request ⟨⟨before, { lookup := none }⟩, {}, leading⟩
    Caller.find external budget allocator p q source buffer request before = (actual.1, actual.2.native) :=
  invoke_erases external allocator (findBody_erases external budget allocator p q observations source buffer request)
    ⟨⟨before, { lookup := none }⟩, {}, leading⟩

theorem force_erases (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (id : NodeId) (item : Item) (values : List NodeId) (before : World σ) (leading : List ProtocolEvent) :
    let actual := force external budget allocator p q observations source buffer id item values ⟨⟨before, { lookup := none }⟩, {}, leading⟩
    Caller.force external budget allocator p q source buffer id item values before = (actual.1, actual.2.native) :=
  invoke_erases external allocator (forceBody_erases external budget allocator p q observations source buffer id item values)
    ⟨⟨before, { lookup := none }⟩, {}, leading⟩

theorem findBody_prefix (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request)
    (leading : List ProtocolEvent) :
    Effect.Transport (prepend leading) (findBody external budget allocator p q observations source buffer request)
      (findBody external budget allocator p q observations source buffer request) := by
  unfold findBody Interner.FindCode.controlRun Interner.FindCode.controlOwned Interner.FindCode.controlMiss
  simp only [execution]
  repeat first
    | exact record_prefix _ _ _
    | exact Effect.Transport.pure (prepend leading) _
    | apply Effect.Transport.bind (prepend leading)
    | split
    | intro value

theorem forceBody_prefix (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (id : NodeId) (item : Item) (values : List NodeId) (leading : List ProtocolEvent) :
    Effect.Transport (prepend leading) (forceBody external budget allocator p q observations source buffer id item values)
      (forceBody external budget allocator p q observations source buffer id item values) := by
  unfold forceBody Interner.ForceCode.controlRun Interner.ForceCode.controlOwned
  simp only [execution]
  repeat first
    | exact record_prefix _ _ _
    | exact Effect.Transport.pure (prepend leading) _
    | apply Effect.Transport.bind (prepend leading)
    | split
    | intro value

theorem finish_prefix (external : External σ) (allocator : Nat) (result : Except Fault α) (leading : List ProtocolEvent) :
    Effect.Transport (prepend leading) (finish external allocator result) (finish external allocator result) := by
  intro before
  unfold finish
  split
  · rw [record_prefix _ _ leading before]
  · rfl

theorem invoke_prefix (external : External σ) (allocator : Nat) (action : Action σ α) (leading : List ProtocolEvent)
    (body : Effect.Transport (prepend leading) action action) :
    Effect.Transport (prepend leading) (invoke external allocator action) (invoke external allocator action) := by
  intro before
  unfold invoke
  rw [body before]
  exact finish_prefix external allocator _ leading _

/-- A source invocation supplies an actual child observation, including its
native result and reached locals. Earlier protocol history cannot influence it.
Graph observation validity is still a separate obligation of the three ports. -/
theorem find_segment (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request)
    (before : World σ) (leading : List ProtocolEvent) :
    let captured := find external budget allocator p q observations source buffer request ⟨⟨before, { lookup := none }⟩, {}, []⟩
    Caller.find external budget allocator p q source buffer request before = (captured.1, captured.2.native) ∧
      find external budget allocator p q observations source buffer request ⟨⟨before, { lookup := none }⟩, {}, leading⟩ =
        (captured.1, prepend leading captured.2) := by
  refine ⟨find_erases external budget allocator p q observations source buffer request before [], ?_⟩
  simpa only [prepend, List.append_nil] using
    invoke_prefix external allocator _ leading (findBody_prefix external budget allocator p q observations source buffer request leading)
      ⟨⟨before, { lookup := none }⟩, {}, []⟩

theorem force_segment (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View)
    (id : NodeId) (item : Item) (values : List NodeId) (before : World σ) (leading : List ProtocolEvent) :
    let captured := force external budget allocator p q observations source buffer id item values ⟨⟨before, { lookup := none }⟩, {}, []⟩
    Caller.force external budget allocator p q source buffer id item values before = (captured.1, captured.2.native) ∧
      force external budget allocator p q observations source buffer id item values ⟨⟨before, { lookup := none }⟩, {}, leading⟩ =
        (captured.1, prepend leading captured.2) := by
  refine ⟨force_erases external budget allocator p q observations source buffer id item values before [], ?_⟩
  simpa only [prepend, List.append_nil] using
    invoke_prefix external allocator _ leading (forceBody_prefix external budget allocator p q observations source buffer id item values leading)
      ⟨⟨before, { lookup := none }⟩, {}, []⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
