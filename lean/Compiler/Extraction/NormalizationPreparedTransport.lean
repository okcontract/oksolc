/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationPrepared

namespace Compiler.Extraction.Cache.NormalizationOwnership

/-- A projection of private effects, with equality of each actual primitive
result. This does not assume correctness of the ownership interpreter. -/
structure Transport (p : PreparedPrimitives σ ε) (q : PreparedPrimitives τ ε) (project : σ → τ) : Prop where
  allocate : ∀ site before,
    q.allocate site (project before) = ((p.allocate site before).1, project (p.allocate site before).2)
  release : ∀ lookup before, q.release lookup (project before) = project (p.release lookup before)
  prepare : ∀ lookup before,
    q.prepare lookup (project before) = ((p.prepare lookup before).1, project (p.prepare lookup before).2)

theorem init_transport (code : Code) (commutative : Bool) (length bufferLength : Nat)
    (allocate : σ → Bool × σ) (other : τ → Bool × τ) (project : σ → τ)
    (mapped : ∀ before, other (project before) = ((allocate before).1, project (allocate before).2)) (before : σ) :
    code.initWith commutative length bufferLength other (project before) =
      ((code.initWith commutative length bufferLength allocate before).1,
       project (code.initWith commutative length bufferLength allocate before).2) := by
  by_cases needed : !commutative || decide (length < code.threshold)
  · simp [Code.initWith, needed]
  · cases fits : code.useScratch.test length bufferLength <;>
      simp [Code.initWith, needed, fits, mapped]

theorem take_transport (code : Code) (duplicate : σ → Bool × σ) (other : τ → Bool × τ) (project : σ → τ)
    (mapped : ∀ before, other (project before) = ((duplicate before).1, project (duplicate before).2))
    (lookup : State) (before : σ) :
    code.takeWith other lookup (project before) =
      ((code.takeWith duplicate lookup before).1, project (code.takeWith duplicate lookup before).2) := by
  cases owned : lookup.owned <;> simp [Code.takeWith, owned, mapped]

theorem deinit_transport (code : Code) (release : State → σ → σ) (other : State → τ → τ) (project : σ → τ)
    (mapped : ∀ lookup before, other lookup (project before) = project (release lookup before))
    (lookup : State) (before : σ) :
    code.deinitWith other lookup (project before) =
      ((code.deinitWith release lookup before).1, project (code.deinitWith release lookup before).2) := by
  cases owned : code.freeOnDeinit && lookup.owned <;> simp [Code.deinitWith, owned, mapped]

theorem finish_transport (code : Code) (p : PreparedPrimitives σ ε) (q : PreparedPrimitives τ ε) (project : σ → τ)
    (mapped : Transport p q project) (outcome : Outcome) (lookup : State) (before : σ) :
    code.finishWith q.toPrimitives outcome lookup (project before) =
      ((code.finishWith p.toPrimitives outcome lookup before).1,
       project (code.finishWith p.toPrimitives outcome lookup before).2) := by
  simp only [Code.finishWith, deinit_transport code p.release q.release project mapped.release]

theorem continue_transport (code : Code) (p : PreparedPrimitives σ ε) (q : PreparedPrimitives τ ε) (project : σ → τ)
    (mapped : Transport p q project) (exit : Exit) (lookup : State) (before : σ) :
    code.continueWith q.toPrimitives exit lookup (project before) =
      ((code.continueWith p.toPrimitives exit lookup before).1,
       project (code.continueWith p.toPrimitives exit lookup before).2) := by
  cases exit with
  | lookup => exact finish_transport code p q project mapped .lookup lookup before
  | transfer | cleanup =>
    simp only [Code.continueWith, take_transport code (p.allocate .duplicate) (q.allocate .duplicate) project (mapped.allocate .duplicate)]
    cases taken : code.takeWith (p.allocate .duplicate) lookup before with
    | mk result reached =>
      rcases result with ⟨ok, after⟩
      cases ok <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          mapped.release, finish_transport code p q project mapped]

theorem init_prepared_transport (code : Code) (p : PreparedPrimitives σ ε) (q : PreparedPrimitives τ ε) (project : σ → τ)
    (mapped : Transport p q project) (commutative : Bool) (length bufferLength : Nat) (before : σ) :
    code.initPrepared commutative length bufferLength q (project before) =
      ((code.initPrepared commutative length bufferLength p before).1,
       project (code.initPrepared commutative length bufferLength p before).2) := by
  simp only [Code.initPrepared, init_transport code commutative length bufferLength
    (p.allocate .temporary) (q.allocate .temporary) project (mapped.allocate .temporary)]
  cases initialized : code.initWith commutative length bufferLength (p.allocate .temporary) before with
  | mk lookup selected =>
    cases lookup with
    | none => rfl
    | some lookup =>
      by_cases borrowed : lookup.origin = .input
      · simp only [borrowed, ↓reduceIte]
      · simp only [borrowed, ↓reduceIte, mapped.prepare]
        cases prepared : p.prepare lookup selected with
        | mk result reached =>
          cases result with
          | error error => rfl
          | ok returned => cases returned; rfl

theorem run_prepared_transport (code : Code) (p : PreparedPrimitives σ ε) (q : PreparedPrimitives τ ε) (project : σ → τ)
    (mapped : Transport p q project) (commutative : Bool) (length bufferLength : Nat) (exit : Exit) (before : σ) :
    code.runPrepared commutative length bufferLength q exit (project before) =
      ((code.runPrepared commutative length bufferLength p exit before).1,
       project (code.runPrepared commutative length bufferLength p exit before).2) := by
  simp only [Code.runPrepared, init_prepared_transport code p q project mapped]
  cases initialized : code.initPrepared commutative length bufferLength p before with
  | mk result reached =>
    cases result with
    | error failure => rfl
    | ok lookup =>
      cases lookup with
      | none => rfl
      | some lookup => simp only [continue_transport code p q project mapped]

end Compiler.Extraction.Cache.NormalizationOwnership
