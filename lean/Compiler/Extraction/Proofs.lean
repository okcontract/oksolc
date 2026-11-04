/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Matcher
import Compiler.Algebraic.Proofs

namespace Compiler.Algebraic
open Contract.Yul

/-- This statement is about definitions extracted from the function body, not
an independently written implementation of the intended matching algorithm. -/
theorem zigMatches_eq (guard : Guard) (facts : Facts) :
    zigMatches guard facts = guard.matches facts := by
  cases guard <;> apply Bool.eq_iff_iff.mpr <;> simp [zigMatches, Guard.matches]

theorem productionOpcode_injective (a b : Binary) :
    productionOpcode a = productionOpcode b ↔ a = b := by
  cases a <;> cases b <;> decide

private theorem extracted_stage (guard : Guard) :
    (if guard = .equal then Stage.equal else .constants) = guard.stage := by
  cases guard <;> rfl

/-- Includes first-match precedence and both stages, for any finite rule list. -/
theorem zigSelectFrom_eq (rules : List Rule) (op : Binary) (stage : Stage) (facts : Facts) :
    zigSelectFrom rules (productionOpcode op) stage facts = select rules op stage facts := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
    simp only [zigSelectFrom, firstReturn, extracted_stage, zigMatches_eq,
      beq_iff_eq, productionOpcode_injective, Bool.and_eq_true, select] at *
    by_cases hop : rule.op = op
    · by_cases hs : rule.guard.stage = stage
      · by_cases hm : rule.guard.matches facts = true
        · simp [hop, hs, hm]
        · simpa [hop, hs, hm] using ih
      · simpa [hop, hs, Ne.symm hs] using ih
    · simpa [hop] using ih

/-- Unknown and unsupported opcode bytes cannot select any rule. -/
theorem zigSelectFrom_unknown (rules : List Rule) (opcode : BitVec 8)
    (stage : Stage) (facts : Facts)
    (unknown : ∀ rule ∈ rules, productionOpcode rule.op ≠ opcode) :
    zigSelectFrom rules opcode stage facts = none := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
    simp only [zigSelectFrom, firstReturn, beq_iff_eq]
    simp only [unknown rule (by simp), ↓reduceIte]
    simpa only [zigSelectFrom, beq_iff_eq] using ih (fun r hr => unknown r (by simp [hr]))

theorem zigSelect_sound (op : Binary) (stage : Stage) (facts : Facts)
    (a b : Word) (reliable : facts.Reliable a b) (replacement : Replacement)
    (selected : zigSelect (productionOpcode op) stage facts = some replacement) :
    op.eval a b = replacement.eval a b := by
  apply production_selection_sound op stage facts a b reliable replacement
  simpa only [zigSelect, zigSelectFrom_eq] using selected

end Compiler.Algebraic
