/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolScope
import Compiler.Extraction.InternerCallerInitFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace

/-- Finishing an empty native scope preserves the complete reached record,
including host effects and history. No allocation or release is observed. -/
theorem finish_empty (external : External σ) (allocator : Nat) (result : Except Fault α) (before : Recorded σ)
    (empty : before.native.scope = { lookup := none }) (completed : ordinary result = true) :
    finish external allocator result before = (result, before) := by
  simp only [finish, completed, ↓reduceIte, record, cleanup, empty, Bool.false_eq_true, deinit, closing,
    List.append_nil, Option.isSome, Bool.not_false, Bool.true_and, Bool.or_false]

/-- Capacity failure returns before initialization or any graph operation.
Move the general source equation out of the regression module so production
composition does not depend on a fixture. -/
theorem capacity_recorded (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (source buffer : View) (request : Interner.Request)
    (before : World σ) (leading : List ProtocolEvent) (full : q.atCapacity before.graph = true) :
    find external budget allocator p q observations source buffer request ⟨⟨before, { lookup := none }⟩, {}, leading⟩ =
      (.error (.language .capacity), ⟨⟨before, { lookup := none }⟩, {}, leading⟩) := by
  unfold find invoke findBody Interner.FindCode.controlRun
  simp only [execution, bind, Effect.bind, record, unchanged, List.append_nil, full, ↓reduceIte, Except.mapError]
  exact finish_empty external allocator _ _ rfl rfl

/-- The actual capacity check and scoped source consume the same initial graph
and history. Scratch, initialization, classification and child work are absent. -/
theorem capacity_projected (external : External σ) (budget allocator : Nat) (p : Primitives σ)
    (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives) (source buffer : View)
    (request : Interner.Request) (before : World σ) (leading trailing : List ProtocolEvent)
    (good : Good source request.arguments before) (full : q.atCapacity before.graph = true)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph) :
    let actual := find external budget allocator p q observations source buffer request
      ⟨⟨before, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    actual.1 = .error (.language .capacity) ∧ Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧
      actual.2.tokens.incomplete = false := by
  intro actual logical
  have ran := capacity_recorded external budget allocator p q observations source buffer request before leading full
  change actual = _ at ran
  have modelRun : logical = (.error .capacity, ⟨{}, { before.graph with allocationCursor := leading.length }⟩) := by
    simp only [logical, Interner.Scoped.findDetailed, Interner.Scoped.finish, Interner.FindCode.controlRun,
      Interner.Scoped.execution, Interner.Scoped.liftGraph, Interner.get, Interner.lift, bind, Effect.bind,
      capacityQuery, full, ↓reduceIte, Interner.Scoped.close]
  rw [ran, modelRun]
  exact ⟨rfl, good, ⟨rfl, Or.inr rfl⟩, rfl, rfl⟩

/-- A failed scoped initializer skips all later source branches and closes its
actual reached scope. This control equation assumes no ownership postcondition. -/
theorem scoped_initialization_failed (r : Interner.Scoped.Resources) (model : Interner.Primitives)
    (request : Interner.Request) (before : Interner.Heap) (error : Interner.Error) (reached : Interner.Scoped.Session)
    (room : model.atCapacity before = false)
    (failed : Interner.Scoped.initScope r request ⟨{}, before⟩ = (.error error, reached)) :
    Interner.Scoped.findDetailed r model request before = (.error error, Interner.Scoped.close r reached) := by
  simp only [Interner.Scoped.findDetailed, Interner.Scoped.finish, Interner.FindCode.controlRun,
    Interner.Scoped.execution, Interner.Scoped.liftGraph, Interner.get, bind, Effect.bind,
    room, Bool.false_eq_true, ↓reduceIte, failed]

attribute [local irreducible] Initialization.capture

/-- Complete ordinary initialization failure uses the actual reached allocator
state and recorded refusal. Existing native failure preservation and scoped
initialization admission derive empty cleanup; no final scope is assumed. -/
theorem initialization_failed_projected (external : External σ) (budget allocator : Nat)
    (p : Primitives σ) (q : Queries) (observations : GraphObservations σ) (model : Interner.Primitives)
    (source buffer : View) (request : Interner.Request) (before : World σ) (fault : Fault) (reached : OwnedCall.State σ)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (bufferLength : buffer.length = 2) (admitted : Admitted external)
    (room : q.atCapacity before.graph = false)
    (failed : Caller.initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.error fault, reached))
    (completed : ordinary (.error fault : Except Fault NodeId) = true)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = q.atCapacity before.graph) :
    let actual := find external budget allocator p q observations source buffer request
      ⟨⟨before, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request
      { before.graph with allocationCursor := leading.length }
    actual.1 = .error fault ∧ actual.2.native = reached ∧
      Good source request.arguments actual.2.native.world ∧ Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧
      actual.2.tokens.incomplete = false := by
  intro actual logical
  obtain ⟨reachedGood, empty, graph, _, _⟩ := Caller.initialize_failed external budget allocator source buffer request
    before fault reached good scratch admitted failed completed
  cases decoded : Interner.Scoped.commutative request.item with
  | error error =>
    have native : ((Except.error (.language error) : Except Fault (List NodeId)),
        (⟨before, { lookup := none }⟩ : OwnedCall.State σ)) = (Except.error fault, reached) := by
      simpa only [Caller.initLookup, decoded] using failed
    have resultEq := Except.error.inj (congrArg Prod.fst native)
    have body : findBody external budget allocator p q observations source buffer request
        ⟨⟨before, { lookup := none }⟩, {}, leading⟩ = (.error fault, ⟨reached, {}, leading⟩) := by
      simp only [findBody, Interner.FindCode.controlRun, execution, bind, Effect.bind, record, unchanged,
        List.append_nil, room, Bool.false_eq_true, ↓reduceIte, failed, initialization, decoded]
    have ran : actual = (.error fault, ⟨reached, {}, leading⟩) := by
      simp only [actual, find, invoke, body]
      exact finish_empty external allocator _ _ empty completed
    have modelRun : logical = (.error error, ⟨{}, { before.graph with allocationCursor := leading.length }⟩) := by
      simp only [logical, Interner.Scoped.findDetailed, Interner.Scoped.finish, Interner.FindCode.controlRun,
        Interner.Scoped.execution, Interner.Scoped.liftGraph, Interner.get, bind, Effect.bind,
        capacityQuery, room, Bool.false_eq_true, ↓reduceIte, Interner.Scoped.initScope, decoded, Interner.Scoped.close]
    rw [ran, modelRun]
    refine ⟨rfl, rfl, reachedGood, ?_, ?_, rfl⟩
    · rw [empty]; exact ⟨rfl, Or.inr rfl⟩
    · simp only [scopeView, graph, Except.mapError, resultEq]
  | ok commutative =>
    let input : Recorded σ := ⟨⟨before, { lookup := none }⟩, {}, leading⟩
    let initialized := record (Caller.initLookup external budget allocator source buffer request)
      (initialization external budget allocator source buffer request) input
    let init := Initialization.capture external budget allocator commutative source buffer request.arguments before.memory
    let r := resources (initialized.2.events ++ trailing) (.preparation .incomplete)
    let initial := Interner.Scoped.initScope r request (scopeView input)
    have projected := initialization_projected external budget allocator commutative source buffer request before leading trailing
      other read sequence good.1 good.2 (scratch commutative) bufferLength decoded admitted
      (by rw [failed]; exact completed)
    have known : (initialized.1, scopeView initialized.2) = (initial.1.mapError Fault.language, initial.2) := projected.2.2.1
    have nativeResult : initialized.1 = .error fault := by simp only [initialized, record, input, failed]
    obtain ⟨lookup, captured, _, _, scopeResult, _, _⟩ := Initialization.checked_scope external budget allocator
      commutative source buffer request before.memory (scopeView input).heap (normalizations leading) (normalizations trailing)
      initial good.2.1 bufferLength decoded (by simp only [scopeView, input, normalizations_length]) projected.1
    cases lookup with
    | some lookup =>
      have impossible := congrArg Prod.fst known
      rw [nativeResult, scopeResult] at impossible
      cases impossible
    | none =>
      have normalized : initialized = (.error fault, ⟨reached, {}, leading ++ init.2.events.map Event.normalization⟩) := by
        simp only [initialized, record, input, failed, initialization, decoded, captured]
        rfl
      have body : findBody external budget allocator p q observations source buffer request input =
          (.error fault, initialized.2) := by
        simp only [findBody, Interner.FindCode.controlRun, execution, bind, Effect.bind, record, unchanged,
          initialized, input, List.append_nil, room, Bool.false_eq_true, ↓reduceIte, failed]
      have ran : actual = (.error fault, initialized.2) := by
        change finish external allocator (findBody external budget allocator p q observations source buffer request input).1
          (findBody external budget allocator p q observations source buffer request input).2 = _
        rw [body]
        exact finish_empty external allocator _ _ (by rw [normalized]; exact empty) completed
      have scopeEmpty : initial.2.scope = {} := by
        have shape := congrArg (fun pair : Except Fault (List NodeId) × Interner.Scoped.Session => pair.2.scope) known
        simpa only [normalized, scopeView] using shape.symm
      have modelRun : logical = (.error .outOfMemory, initial.2) := by
        change Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model request _ = _
        rw [ran]
        change Interner.Scoped.findDetailed r model request (scopeView input).heap = _
        rw [scoped_initialization_failed r model request (scopeView input).heap .outOfMemory initial.2
          (capacityQuery.trans room) (Prod.ext scopeResult rfl)]
        simp only [Interner.Scoped.close, scopeEmpty]
      rw [ran, modelRun]
      refine ⟨rfl, by rw [normalized], ?_, ?_, ?_, projected.2.2.2⟩
      · rw [normalized]; exact reachedGood
      · rw [normalized, empty]; exact ⟨rfl, Or.inr rfl⟩
      · have resultEq := congrArg Prod.fst known
        rw [nativeResult, scopeResult] at resultEq
        have faultEq : fault = .language .outOfMemory := Except.error.inj resultEq
        have scopeEq : scopeView initialized.2 = initial.2 := congrArg Prod.snd known
        exact Prod.ext (congrArg Except.error faultEq) scopeEq

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
