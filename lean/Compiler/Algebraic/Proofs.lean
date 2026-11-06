/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Algebraic.Rules

/-! Kernel-checked soundness proofs for all 50 ordered rules exported from
`src/libevmasm/algebraic_rules.zig`, including `SDIV`, `SLT`, and `SGT`
two's-complement identities over 256-bit EVM words. -/
namespace Compiler.Algebraic
open Contract
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

private theorem sdiv_zero_right (x : Word) : Contract.evmSdiv x 0 = 0 := by
  simp [Contract.evmSdiv]

private theorem sdiv_zero_left (x : Word) : Contract.evmSdiv 0 x = 0 := by
  unfold Contract.evmSdiv
  by_cases h0 : x = 0#256
  · simp [h0]
  · have h0min : decide ((0 : Word) = 1#256 <<< 255) = false := by decide
    have hmsb0 : (0 : Word).msb = false := by decide
    have hneg0 : -(0 : Word) = 0 := by decide
    simp [h0, h0min, hmsb0, BitVec.zero_udiv, hneg0]

private theorem sdiv_one_right (x : Word) : Contract.evmSdiv x 1 = x := by
  unfold Contract.evmSdiv
  have h10 : (1 : Word) ≠ 0#256 := by decide
  have h1notmax : decide ((1 : Word) = ~~~0#256) = false := by decide
  have hmsb1 : (1 : Word).msb = false := by decide
  simp only [h10, h1notmax, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hmsb1]
  by_cases hx : x.msb
  · simp [hx, BitVec.udiv_one, BitVec.neg_neg]
  · simp [hx, BitVec.udiv_one]

private theorem slt_irrefl (x : Word) : Contract.boolWord (x.slt x) = 0 := by
  have h : x.slt x = false := by
    simp [BitVec.slt]
  simp [h, Contract.boolWord]

private theorem positive_bool (x : Word) :
    Contract.boolWord ((0 : Word).ult x) = Unary.iszero.eval (Unary.iszero.eval x) := by
  by_cases h : x = 0
  · subst x; decide
  · have positive : 0 < x.toNat := Nat.pos_of_ne_zero (by
      intro zero
      exact h (BitVec.eq_of_toNat_eq zero))
    simp [Contract.boolWord, Unary.eval, BitVec.ult_eq_decide, positive]
    exact h

/-- Every entry exported from `productionRules` (all 50 ordered rules) preserves
the exact 256-bit EVM word value for all operands satisfying its guard. -/
theorem production_rules_sound (rule : Rule) (member : rule ∈ productionRules) : rule.Sound := by
  simp only [productionRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    intro a b condition
    simp only [Guard.Holds] at condition
    subst_vars
    simp only [Replacement.eval, Binary.eval, Contract.evmDiv, Contract.evmMod,
      Contract.evmShl_eq_shiftLeft, Contract.evmShr_eq_ushiftRight,
      sdiv_zero_right, sdiv_zero_left, sdiv_one_right, slt_irrefl,
      max_sub, mul_max, max_mul, positive_bool,
      BitVec.and_allOnes, BitVec.allOnes_and, BitVec.or_allOnes, BitVec.allOnes_or]
  all_goals
    try simp [Unary.eval, Contract.boolWord, BitVec.ult_eq_decide_lt, BitVec.not_allOnes_lt]
  all_goals
    try first | exact BitVec.not_lt.mp BitVec.not_allOnes_lt | simp only [eq_comm]

theorem production_selection_sound (op : Binary) (stage : Stage) (facts : Facts)
    (a b : Word) (reliable : facts.Reliable a b) (replacement : Replacement)
    (selected : select productionRules op stage facts = some replacement) :
    op.eval a b = replacement.eval a b :=
  select_sound productionRules production_rules_sound op stage facts a b reliable replacement selected

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
