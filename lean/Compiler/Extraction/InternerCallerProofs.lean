/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerForce

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Compose only the owned continuation reached by actual initialization.
The capacity, initialization, classification and cache-hit paths stay shared. -/
theorem find_ready_at (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external)
    (owned : ∀ handle world deterministic,
      initLookup external budget allocator source buffer request ⟨before, {lookup := none}⟩ =
        (.ok handle.values, ⟨world, {lookup := some handle}⟩) →
      Ready allocator source request.arguments handle world.memory →
      let ran := body external allocator p request handle.values deterministic ⟨world, {lookup := some handle}⟩
      ordinary ran.1 = true → ReadyToClose allocator source request.arguments ran.2) :
    let execution := findBody external budget allocator p q source buffer request ⟨before, { lookup := none }⟩
    ordinary execution.1 = true → CanClose allocator source request.arguments execution.2 := by
  unfold findBody Interner.FindCode.controlRun
  simp only [execution, OwnedCall.execution, bind, Effect.bind]
  by_cases capacity : q.atCapacity before.graph = true
  · simp only [capacity, ↓reduceIte, Except.mapError]
    exact fun _ => CanClose.empty before good
  · simp only [capacity, Bool.false_eq_true, ↓reduceIte, Effect.bind]
    cases initialized : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ with
    | mk result after =>
      have checked := initialize_verified external budget allocator source buffer request before good scratch admitted
      rw [initialized] at checked
      cases result with
      | error fault => exact checked
      | ok args =>
        obtain ⟨handle, scope, ready, same, _⟩ := checked
        rcases after with ⟨world, localScope⟩
        dsimp only at scope ready
        subst localScope
        subst args
        cases deterministic : q.deterministic request.item with
        | error error =>
          simp only [Except.mapError]
          exact fun _ => CanClose.lookup world handle ready
        | ok flag =>
          simp only [Except.mapError]
          cases flag with
          | false =>
            exact fun completed => CanClose.taken _
              (owned handle world false initialized ready completed)
          | true =>
            simp only [↓reduceIte, Effect.bind]
            cases keyed : Interner.makeKey request handle.values with
            | error error =>
              dsimp only
              exact fun _ => CanClose.lookup world handle ready
            | ok key =>
              dsimp only
              cases found : before.graph.table key with
              | some id =>
                simp only [pure, Effect.pure]
                exact fun _ => CanClose.lookup world handle ready
              | none =>
                exact fun completed => CanClose.taken _
                  (owned handle world true initialized ready completed)

/-- Uniform graph contracts specialize the actual-prefix caller proof. -/
theorem find_ready (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (contracts : Contracts allocator source request.arguments p) :
    let execution := findBody external budget allocator p q source buffer request ⟨before, { lookup := none }⟩
    ordinary execution.1 = true → CanClose allocator source request.arguments execution.2 :=
  find_ready_at external budget allocator p q source buffer request before good scratch admitted
    (fun handle world deterministic _ ready =>
      body_ready external allocator p request deterministic handle source request.arguments world ready admitted contracts)

theorem force_ready (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (id : NodeId) (item : Item) (values : List NodeId) (before : World σ)
    (good : Good source values before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) (contracts : Contracts allocator source values p) :
    let execution := forceBody external budget allocator p q source buffer id item values ⟨before, { lookup := none }⟩
    ordinary execution.1 = true → CanClose allocator source values execution.2 := by
  unfold forceBody Interner.ForceCode.controlRun
  simp only [execution, OwnedCall.execution, bind, Effect.bind]
  cases validated : q.validate id before.graph with
  | error error =>
    simp only [Except.mapError]
    exact fun _ => CanClose.empty before good
  | ok returned =>
    cases returned
    simp only [Except.mapError]
    cases initialized : initLookup external budget allocator source buffer ⟨item, values, 0⟩ ⟨before, { lookup := none }⟩ with
    | mk result after =>
      have checked := initialize_verified external budget allocator source buffer ⟨item, values, 0⟩ before good scratch admitted
      rw [initialized] at checked
      cases result with
      | error fault => exact checked
      | ok args =>
        obtain ⟨handle, scope, ready, same, _⟩ := checked
        rcases after with ⟨world, localScope⟩
        dsimp only at scope ready
        subst localScope
        subst args
        cases keyed : Interner.makeKey ⟨item, values, 0⟩ handle.values with
        | error error =>
          simp only [keyed]
          exact fun _ => CanClose.lookup world handle ready
        | ok key =>
          simp only [keyed]
          cases found : before.graph.table key with
          | some existing =>
            simp only [pure, Effect.pure]
            exact fun _ => CanClose.lookup world handle ready
          | none =>
            exact fun completed => CanClose.taken _
              (force_owned_ready external allocator p ⟨item, values, 0⟩ id handle source values world ready admitted contracts completed)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
