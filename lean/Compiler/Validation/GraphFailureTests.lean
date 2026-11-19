/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.GraphFailure

namespace Compiler.Validation.Failure.Tests
open Contract.Yul

def before : List Node := [.input "x", .literal 3, .binary .add 0 1, .literal 5, .binary .add 2 3]

/-- Reassociation allocated the folded constant before its outer call failed.
The reached graph need not equal the successfully completed prefix. -/
def reached : Attempt := ⟨.outOfMemory, before.take 4 ++ [.literal 8], [0, 1, 2, 3],
  [⟨.binary .add 0 1, 2⟩, ⟨.literal 8, 4⟩]⟩

theorem reached_growth : validateAttempt 8 before reached = true := by decide
theorem earlier_failure : validateAttempt 8 before ⟨.outOfMemory, [], [], []⟩ = true := by decide
theorem complete : validateAttempt 8 before ⟨.complete, before, [0, 1, 2, 3, 4], []⟩ = true := by decide
theorem wrong_old_result : validateAttempt 8 before { reached with ids := [0, 1, 1, 3] } = false := by decide
theorem poisoned_partial_cache : validateAttempt 8 before { reached with cache := [⟨.literal 9, 4⟩] } = false := by decide
theorem malformed_unused_node : validateAttempt 8 before { reached with after := before.take 4 ++ [.unary .bitnot 9] } = false := by decide
theorem failure_is_not_completion : validateAttempt 8 before { reached with outcome := .complete } = false := by decide
theorem completed_is_not_failure : validateAttempt 8 before ⟨.outOfMemory, before, [0, 1, 2, 3, 4], []⟩ = false := by decide
theorem no_missing_observations : validate 8 before [] = false := by decide
theorem partial_meaning (locals : String → Word) : Preserves before reached locals :=
  attempt_sound 8 before reached reached_growth locals

end Compiler.Validation.Failure.Tests
