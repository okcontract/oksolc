/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationEffects

/-! Preparation executes between destination selection and lookup/transfer.
An ordinary allocator failure is a normal Outcome. A preparation fault is a
separate semantic outcome retaining the provisional ownership token and exact
reached effects. No native cleanup or recoverable Zig error is invented for it.
Primitive allocator validity/pairing and native correspondence remain open. -/
namespace Compiler.Extraction.Cache.NormalizationOwnership

structure PreparedPrimitives (σ ε : Type) extends Primitives σ where
  prepare : State → σ → Except ε Unit × σ

abbrev PreparedResult (ε : Type) := Except (ε × State) (Outcome × State)

/-- Live initialization distinguishes ordinary allocation refusal from a
preparation fault. Success retains its token for intervening caller actions. -/
abbrev PreparedInit (ε : Type) := Except (ε × State) (Option State)

def Code.initPrepared (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (p : PreparedPrimitives σ ε) (effects : σ) : PreparedInit ε × σ :=
  let (lookup, selected) := code.initWith commutative length bufferLength (p.allocate .temporary) effects
  match lookup with
  | none => (.ok none, selected)
  | some state =>
    let (result, prepared) := if state.origin = .input then (.ok (), selected) else p.prepare state selected
    match result with
    | .error reason => (.error (reason, state), prepared)
    | .ok () => (.ok (some state), prepared)

def Code.runPrepared (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (p : PreparedPrimitives σ ε) (exit : Exit) (effects : σ) : PreparedResult ε × σ :=
  let (lookup, prepared) := code.initPrepared commutative length bufferLength p effects
  match lookup with
  | .error failure => (.error failure, prepared)
  | .ok none => (.ok (.allocationFailure, { dead := true }), prepared)
  | .ok (some state) =>
    let (result, after) := code.continueWith p.toPrimitives exit state prepared
    (.ok result, after)

/-- Compatibility equation for clients reasoning about the existing lifecycle.
The implementation itself shares the live prefix. -/
theorem run_prepared_expand (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (p : PreparedPrimitives σ ε) (exit : Exit) (effects : σ) :
    code.runPrepared commutative length bufferLength p exit effects =
      let (lookup, selected) := code.initWith commutative length bufferLength (p.allocate .temporary) effects
      match lookup with
      | none => (.ok (.allocationFailure, { dead := true }), selected)
      | some state =>
        let (result, prepared) := if state.origin = .input then (.ok (), selected) else p.prepare state selected
        match result with
        | .error reason => (.error (reason, state), prepared)
        | .ok () =>
          let (result, after) := code.continueWith p.toPrimitives exit state prepared
          (.ok result, after) := by
  cases initialized : code.initWith commutative length bufferLength (p.allocate .temporary) effects with
  | mk lookup selected =>
    cases lookup with
    | none => simp only [Code.runPrepared, Code.initPrepared, initialized]
    | some state =>
      by_cases borrowed : state.origin = .input
      · simp only [Code.runPrepared, Code.initPrepared, initialized, if_pos borrowed]
      · cases prepared : p.prepare state selected with
        | mk result reached =>
          cases result <;> simp only [Code.runPrepared, Code.initPrepared, initialized, if_neg borrowed, prepared]

/-- The former effect interpreter is exactly the identity-preparation instance.
This does not project stateful allocation decisions across nontrivial effects. -/
theorem run_prepared_identity (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (p : Primitives σ) (exit : Exit) (effects : σ) :
    code.runPrepared commutative length bufferLength
      ({ toPrimitives := p, prepare := fun _ state => (.ok (), state) } : PreparedPrimitives σ ε) exit effects =
      let (result, after) := code.runWith commutative length bufferLength p exit effects
      (.ok result, after) := by
  cases selected : code.initWith commutative length bufferLength (p.allocate .temporary) effects with
  | mk lookup after =>
    cases lookup with
    | none => simp only [run_prepared_expand, Code.runWith, selected]
    | some state =>
      by_cases borrowed : state.origin = .input <;>
        simp only [run_prepared_expand, Code.runWith, selected, borrowed, ↓reduceIte]

/-- Failed preparation keeps its exact effects and live provisional token.
Neither transfer nor deinit executes, and the fault is not ordinary allocator
OOM. Its token may still own storage; this is not a closed-lifetime claim. -/
theorem prepared_fault (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (p : PreparedPrimitives σ ε) (exit : Exit) (effects selected after : σ) (state : State) (reason : ε)
    (initialized : code.initWith commutative length bufferLength (p.allocate .temporary) effects = (some state, selected))
    (needed : state.origin ≠ .input) (failed : p.prepare state selected = (.error reason, after)) :
    code.runPrepared commutative length bufferLength p exit effects = (.error (reason, state), after) := by
  simp only [run_prepared_expand, initialized, if_neg needed, failed]

/-- Later allocations and releases use the effects returned by preparation. -/
theorem prepared_success (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (p : PreparedPrimitives σ ε) (exit : Exit) (effects selected prepared : σ) (state : State)
    (initialized : code.initWith commutative length bufferLength (p.allocate .temporary) effects = (some state, selected))
    (needed : state.origin ≠ .input) (done : p.prepare state selected = (.ok (), prepared)) :
    code.runPrepared commutative length bufferLength p exit effects =
      let (result, after) := code.continueWith p.toPrimitives exit state prepared
      (.ok result, after) := by
  simp only [run_prepared_expand, initialized, if_neg needed, done]

end Compiler.Extraction.Cache.NormalizationOwnership
