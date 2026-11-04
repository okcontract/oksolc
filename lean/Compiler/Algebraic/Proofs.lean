/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Algebraic.Rules

namespace Compiler.Algebraic
open Contract.Yul

set_option linter.unusedSimpArgs false

private theorem max_sub (x : Word) : BitVec.allOnes 256 - x = ~~~x := by
  rw [← BitVec.neg_one_eq_allOnes, BitVec.sub_eq_add_neg,
    BitVec.not_eq_neg_add, BitVec.sub_eq_add_neg, BitVec.add_comm]

private theorem mul_max (x : Word) : x * BitVec.allOnes 256 = 0 - x := by
  rw [← BitVec.neg_one_eq_allOnes, BitVec.mul_neg, BitVec.mul_one]
  exact (BitVec.zero_sub x).symm

private theorem max_mul (x : Word) : BitVec.allOnes 256 * x = 0 - x := by
  rw [BitVec.mul_comm, mul_max]

private theorem positive_bool (x : Word) :
    boolWord ((0 : Word).ult x) = Unary.iszero.eval (Unary.iszero.eval x) := by
  by_cases h : x = 0
  · subst x; decide
  · have positive : 0 < x.toNat := Nat.pos_of_ne_zero (by
      intro zero
      exact h (BitVec.eq_of_toNat_eq zero))
    simp [boolWord, Unary.eval, BitVec.ult_eq_decide, positive]
    exact h

/-- Every entry exported from the production table preserves the EVM word value,
for every operand, under its stated guard. No sampled or bounded execution. -/
theorem production_rules_sound (rule : Rule) (member : rule ∈ productionRules) : rule.Sound := by
  simp only [productionRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro a b condition
    simp only [Guard.Holds] at condition
    subst_vars
    simp only [Replacement.eval, Binary.eval, max_sub, mul_max, max_mul, positive_bool,
      BitVec.and_allOnes, BitVec.allOnes_and, BitVec.or_allOnes, BitVec.allOnes_or]
  all_goals
    simp [Unary.eval, boolWord, BitVec.ult_eq_decide_lt, BitVec.not_allOnes_lt]
  all_goals first | exact BitVec.not_lt.mp BitVec.not_allOnes_lt | simp only [eq_comm]

/-- The production subset is value preserving whenever its caller's constant
and equality facts are correct. This does not certify other compiler passes. -/
theorem production_selection_sound (op : Binary) (stage : Stage) (facts : Facts)
    (a b : Word) (reliable : facts.Reliable a b) (replacement : Replacement)
    (selected : select productionRules op stage facts = some replacement) :
    op.eval a b = replacement.eval a b :=
  select_sound productionRules production_rules_sound op stage facts a b reliable replacement selected

/-- The rule theorem lifts to arbitrary pure Yul operand expressions, storage,
context and locals. Reliability is required at the actual evaluation point. -/
theorem production_expression_sound (op : Binary) (stage : Stage) (facts : Facts)
    (a b : Expression) (storage : Word → Word) (ctx : Contract.Context) (locals : String → Word)
    (reliable : facts.Reliable (a.eval storage ctx locals) (b.eval storage ctx locals))
    (replacement : Replacement)
    (selected : select productionRules op stage facts = some replacement) :
    (Expression.binary op a b).eval storage ctx locals =
      (replacement.expression a b).eval storage ctx locals := by
  rw [replacement_eval]
  exact production_selection_sound op stage facts _ _ reliable replacement selected

end Compiler.Algebraic
