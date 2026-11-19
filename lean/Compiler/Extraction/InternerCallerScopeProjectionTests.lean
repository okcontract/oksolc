/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerScopedClose
import Compiler.Extraction.InternerCallerCloseTests
import Compiler.Extraction.InternerPhysicalDispatchPreservationTests
import Compiler.Extraction.InternerNativeDispatch

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ScopeProjection.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace Recursive Normalization.Tests
open OwnedCall.Tests (request world Search)
open Take.Tests (borrowed borrowed_ready)
open Close.Tests (taken lookup key take_succeeds)
open PreservationTests (counted counted_projects advanceModel)

/-- Reuse the existing counted graph/cursor fixtures to test control
correspondence. These counters are not a complete native allocation trace. -/
def model (search : Search) (publishFails insertFails : Bool) : Interner.Primitives :=
  { Compiler.Extraction.Recursive.Tests.primitives with
    simplify := fun _ => advanceModel (match search with
      | .fail => .error .outOfMemory | .found => .ok (some 11) | .unchanged => .ok none | .semantic => .error .unsupported)
    publish := fun _ _ => advanceModel (if publishFails then .error .outOfMemory else .ok ())
    insert := fun _ _ => advanceModel (if insertFails then .error .outOfMemory else .ok 11) }

def physical (model : Interner.Primitives) : Primitives Nat := {
  simplify := fun key _ => counted (model.simplify key)
  publish := fun key _ id => counted (model.publish key id)
  insert := fun key _ deterministic => counted (model.insert key deterministic) }

def cursor (world : World Nat) := world.graph.allocationCursor
def outerSlice : ArgumentSlice := ⟨4, items⟩
def predicate : World Nat → Prop := Held 7 source items outerSlice

theorem graph_contracts (model : Interner.Primitives) (key : Key) (slice : ArgumentSlice) (deterministic : Bool) :
    Graphs (cursorGraph cursor) predicate (physical model) model key slice deterministic := by
  exact ⟨counted_projects 7 source items outerSlice _, fun _ => counted_projects 7 source items outerSlice _,
    counted_projects 7 source items outerSlice _⟩

theorem memory_contracts (model : Interner.Primitives) : Contracts 7 source items (physical model) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro key slice id before _ held completed
    have kept := (counted_projects 7 source items slice (model.publish key id) before held completed).1
    exact ⟨kept.1, fun _ _ => kept.2.1⟩
  · intro key slice deterministic before _ held completed
    exact (counted_projects 7 source items slice (model.insert key deterministic) before held completed).1.1
  · intro key slice before _ held completed
    exact (counted_projects 7 source items slice (model.simplify key) before held completed).1

theorem initial : predicate taken.2.world := by
  have derived := (Take.verified success 7 .input source items borrowed world [] [] borrowed_ready (external_admitted _)).2
  have successPost := derived.2.2.2.2.2
  have succeeded := take_succeeds
  dsimp only [Close.Tests.taken] at succeeded
  rw [succeeded] at successPost
  obtain ⟨slice, remaining, locals, post⟩ := successPost
  have actual : taken.2.scope.slice = some outerSlice := by rfl'
  have same : slice = outerSlice := Option.some.inj ((congrArg Local.slice locals).symm.trans actual)
  subst slice
  exact ⟨⟨post.ready.valid, post.ready.source⟩, post.live, post.separate⟩

def native (search : Search) (publishFails insertFails deterministic : Bool) :=
  Interner.findCode.controlMiss (OwnedCall.execution success 7 (physical (model search publishFails insertFails)))
    request key deterministic taken.2

def logical (resources : Interner.Scoped.Resources) (search : Search) (publishFails insertFails deterministic : Bool) :=
  Interner.findCode.controlMiss (Interner.Scoped.execution resources (model search publishFails insertFails))
    request key deterministic (scopeAt (cursorGraph cursor) lookup items taken.2)

theorem ordinary_native (search : Search) (publishFails insertFails deterministic : Bool) (ordinarySearch : search ≠ .semantic) :
    ordinary (native search publishFails insertFails deterministic).1 = true := by
  cases search <;> cases publishFails <;> cases insertFails <;> cases deterministic <;> first | contradiction | rfl'

theorem matched (resources : Interner.Scoped.Resources) (search : Search) (publishFails insertFails deterministic : Bool)
    (ordinarySearch : search ≠ .semantic) :
    (native search publishFails insertFails deterministic).1 =
        (logical resources search publishFails insertFails deterministic).1.mapError Fault.language ∧
      (logical resources search publishFails insertFails deterministic).2 =
        scopeAt (cursorGraph cursor) lookup items (native search publishFails insertFails deterministic).2 := by
  have projected := miss (cursorGraph cursor) predicate success 7 (physical (model search publishFails insertFails))
    (model search publishFails insertFails) (resources) lookup items borrowed outerSlice request key deterministic
    (graph_contracts _ _ _ _) taken.2 ⟨by rfl', by rfl', initial⟩
    (ordinary_native search publishFails insertFails deterministic ordinarySearch)
  exact ⟨projected.2.1, projected.2.2.symm⟩

theorem failed_publication :
    (native .found true false true).1 = .error (.language .outOfMemory) ∧
    (native .found true false true).2.scope.handedOff = false ∧
    cursor (native .found true false true).2.world = 2 ∧
    (native .found true false true).2.world.memory.effects = 19 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem insertion_handoff :
    (native .unchanged false true true).1 = .error (.language .outOfMemory) ∧
    (native .unchanged false true true).2.scope.handedOff = true ∧
    cursor (native .unchanged false true true).2.world = 2 := ⟨by rfl', by rfl', by rfl'⟩

theorem nondeterministic_skips_search :
    (native .semantic false false false).1 = .ok 11 ∧
    (native .semantic false false false).2.scope.handedOff = true ∧
    cursor (native .semantic false false false).2.world = 1 := ⟨by rfl', by rfl', by rfl'⟩

theorem semantic_retains_state :
    let body := native .semantic false false true
    body.1 = .error (.language .unsupported) ∧ finish success 7 body.1 body.2 = body :=
  ⟨by rfl', finish_semantic success 7 _ _ (by rfl')⟩

attribute [local irreducible] Close.capture Take.capture

theorem verified_closed (search : Search) (publishFails insertFails deterministic : Bool) (ordinarySearch : search ≠ .semantic)
    (leading suffix : List (Event Failure)) (start : cursor (native search publishFails insertFails deterministic).2.world = leading.length) :
    let body := native search publishFails insertFails deterministic
    ∃ remaining after, finish success 7 body.1 body.2 = (body.1, after) ∧
      let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
      let execution := Close.capture success 7 lookup phase remaining body.2
      let resources := Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete)
      let projected := Interner.findCode.controlMiss (Interner.Scoped.execution resources (model search publishFails insertFails))
        request key deterministic (scopeAt (cursorGraph cursor) lookup remaining.values taken.2)
      body.1 = projected.1.mapError Fault.language ∧
      projected.2 = scopeAt (cursorGraph cursor) lookup remaining.values body.2 ∧
      after.world.memory = execution.2.effects.session ∧
      Close.checked execution leading suffix lookup projected.2.scope.phase projected.2.scope.items projected.2.heap =
        .ok (Interner.Scoped.close resources projected.2) := by
  obtain ⟨slice, remaining, after, _, _, finished, _, _, result, state, memory, closed⟩ :=
    closed_miss_after_take success 7 .input source items borrowed world borrowed_ready (external_admitted _)
      (physical (model search publishFails insertFails)) (memory_contracts _) cursor predicate (model search publishFails insertFails)
      request key deterministic rfl (fun slice _ => graph_contracts _ _ slice _) take_succeeds initial
      (ordinary_native search publishFails insertFails deterministic ordinarySearch) leading suffix start
  exact ⟨remaining, after, finished, result, state, memory, closed⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ScopeProjection.Tests
