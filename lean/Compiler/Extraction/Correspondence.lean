/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Program
import Compiler.Extraction.Proofs
import Compiler.Extraction.ConstructionProofs

namespace Compiler.Extraction.IR
open Compiler.Algebraic Contract.Yul

def matcherEnv (guard : Guard) (facts : Facts) : Env [.guard, .facts] :=
  Env.cons guard (Env.cons (t := .facts) facts Env.empty)

def evalMatcher (guard : Guard) (facts : Facts) : Bool :=
  matcher.eval (fun _ _ => false) (matcherEnv guard facts)

/-- Checked against the separate readable-code backend, not a source hash. -/
theorem matcher_correspondence (guard : Guard) (facts : Facts) :
    evalMatcher guard facts = zigMatches guard facts := by
  cases facts with
  | mk left right equal => cases left <;> cases right <;> cases guard <;> rfl

def selectionEnv (rules : List Rule) (opcode : BitVec 8) (stage : Stage) (facts : Facts) :
    Env [.opcode, .stage, .facts, .array .rule] :=
  Env.cons opcode (Env.cons (t := .stage) stage (Env.cons (t := .facts) facts
    (Env.cons (t := .array .rule) rules Env.empty)))

def Flow.fromOption : Option Replacement → Flow
  | none => .next
  | some value => .returned (some value)

theorem each_firstReturn (rules : List α) (select : α → Option Replacement) :
    (each rules (fun rule => Flow.fromOption (select rule))).thenDo (fun _ => .returned none) =
      .returned (firstReturn rules select none) := by
  induction rules with
  | nil => rfl
  | cons head rest ih =>
    cases h : select head <;> simp [each, firstReturn, h, Flow.fromOption, Flow.thenDo] at *
    exact ih

/-- The finite inline loop preserves early return and source order for arbitrary
rule lists; this is not a theorem just about the current 45 table entries. -/
theorem selection_correspondence (rules : List Rule) (opcode : BitVec 8)
    (stage : Stage) (facts : Facts) :
    selection.eval evalMatcher (selectionEnv rules opcode stage facts) =
      .returned (zigSelectFrom rules opcode stage facts) := by
  simp only [selection, Block.eval, Expr.eval, Env.cons, selectionEnv, EqType.equal,
    matcher_correspondence, zigSelectFrom]
  rw [← each_firstReturn]
  congr 1
  apply congrArg (each rules)
  funext rule
  by_cases ho : (productionOpcode rule.op == opcode) = true <;>
    by_cases hs : (stage == (if rule.guard == .equal then Stage.equal else .constants)) = true <;>
    by_cases hm : zigMatches rule.guard facts = true <;>
    simp_all [Flow.fromOption, Flow.thenDo]

def constructionEnv (replacement : Replacement) (left right : NodeId) :
    Env [.replacement, .node, .node] :=
  Env.cons replacement (Env.cons (t := .node) left (Env.cons (t := .node) right Env.empty))

/-- Every callback, opaque debug argument and error-continuation ordering agrees
for arbitrary monads. No allocator or successful-callback premise is needed. -/
theorem construction_correspondence {m : Type → Type} [Monad m]
    (classes : Builder m Debug) (debug : Debug) (replacement : Replacement)
    (left right : NodeId) :
    construction.eval classes debug evalMatcher (constructionEnv replacement left right) =
      zigApply replacement classes left right debug := by
  cases replacement <;> rfl

end Compiler.Extraction.IR
