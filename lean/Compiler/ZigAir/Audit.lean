/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.ScalarTests
import Compiler.ZigAir.WordBridge
import Compiler.ZigAir.ControlProofs
import Compiler.ZigAir.ControlSafety
import Compiler.ZigAir.ControlTests
import Contract.Check.Declarations
import Lean.Elab.Command

/-! Complete declaration closure audit; independent kernel replay is required
by the acceptance harness. This is not a source or native-code certificate. -/
open Lean Elab Command Contract.Check in
run_cmd do
  let roots := #[``Compiler.ZigAir.u2s_correct, ``Compiler.ZigAir.s2u_correct,
    ``Compiler.ZigAir.u2s_word, ``Compiler.ZigAir.s2u_word,
    ``Compiler.ZigAir.unsigned_roundtrip, ``Compiler.ZigAir.signed_roundtrip,
    ``Compiler.ZigAir.ScalarTests.dead_unchecked_overflow,
    ``Compiler.ZigAir.ScalarTests.dead_checked_overflow,
    ``Compiler.ZigAir.ScalarTests.dead_wrapping_continues,
    ``Compiler.ZigAir.ScalarTests.unsigned_wrap,
    ``Compiler.ZigAir.ScalarTests.signed_wrap,
    ``Compiler.ZigAir.ScalarTests.zero_width_wrap,
    ``Compiler.ZigAir.ScalarTests.checked_cast_negative,
    ``Compiler.ZigAir.ScalarTests.unchecked_cast_negative,
    ``Compiler.ZigAir.ScalarTests.signed_bitcast,
    ``Compiler.ZigAir.ScalarTests.signed_truncation,
    ``Compiler.ZigAir.ScalarTests.unselected_fault_is_not_executed,
    ``Compiler.ZigAir.ScalarTests.return_skips_continuation,
    ``Compiler.ZigAir.ScalarTests.outer_jump_propagates_and_binds,
    ``Compiler.ZigAir.ScalarTests.unmatched_jump_rejects,
    ``Compiler.ZigAir.ScalarTests.wrong_block_value_rejects,
    ``Compiler.ZigAir.ScalarTests.wrong_return_type_rejects,
    ``Compiler.ZigAir.ScalarTests.missing_argument_rejects,
    ``Compiler.ZigAir.ScalarTests.invalid_argument_rejects,
    ``Compiler.ZigAir.ScalarTests.wrong_argument_type_rejects,
    ``Compiler.ZigAir.ScalarTests.missing_local_rejects,
    ``Compiler.ZigAir.Scalar.ControlRefinement.eval_eq_embed,
    ``Compiler.ZigAir.Scalar.ControlRefinement.eval_eq_reference,
    ``Compiler.ZigAir.Control.Code.preserves,
    ``Compiler.ZigAir.ControlTests.failed_primitive_keeps_effects,
    ``Compiler.ZigAir.ControlTests.type_failure_keeps_effects,
    ``Compiler.ZigAir.ControlTests.unselected_branch_has_no_effects,
    ``Compiler.ZigAir.ControlTests.outer_jump_keeps_state_and_environment,
    ``Compiler.ZigAir.ControlTests.returned_state_skips_continuation,
    ``Compiler.ZigAir.ControlTests.branch_reads_effectful_binding,
    ``Compiler.ZigAir.ControlTests.invalid_block_result_keeps_effects,
    ``Compiler.ZigAir.ControlTests.reference_failure_keeps_prefix]
  let mut claims := #[]
  for root in roots do
    let .ok dependencies := Declarations.closure (← getEnv) #[root]
      | throwError "invalid dependency closure: {root}"
    let .ok axioms := Declarations.axioms dependencies
      | throwError "disallowed axiom: {root}"
    let some info := (← getEnv).find? root | throwError "missing theorem: {root}"
    unless info matches .thmInfo _ do throwError "not a theorem: {root}"
    claims := claims.push <| Json.mkObj [
      ("theorem", .str root.toString), ("statement", Declarations.expression info.type),
      ("axioms", toJson axioms), ("dependencies", toJson (dependencies.map (·.name.toString)))]
  liftIO <| IO.println (Json.mkObj [
    ("schema", .str "oksolc.scalar-air-audit.v1"), ("scope", .str "zigFreshAir"),
    ("sourceSafetyVerified", .bool false), ("wholeCompilerVerified", .bool false),
    ("claims", .arr claims)]).compress
