/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineRefinement
import Compiler.ZigAir.MemoryMachine
import Compiler.ZigAir.MemoryExecutionProofs
import Compiler.ZigAir.MemoryExecutionTests
import Compiler.ZigAir.MachineTests
import Contract.Check.Declarations
import Lean.Elab.Command

/-! Complete declaration closure audit; independent kernel replay is required
by the acceptance harness. This is not a source or native-code certificate. -/
open Lean Elab Command Contract.Check in
run_cmd do
  let roots := #[
    ``Compiler.ZigAir.Control.Machine.advance_finished,
    ``Compiler.ZigAir.Control.Machine.advance_add,
    ``Compiler.ZigAir.Control.Machine.finished_stable,
    ``Compiler.ZigAir.Control.Machine.Steps.trans,
    ``Compiler.ZigAir.Control.Machine.advance_steps,
    ``Compiler.ZigAir.Control.Machine.steps_iff_fuel,
    ``Compiler.ZigAir.Control.Machine.finished_unique,
    ``Compiler.ZigAir.Control.Machine.jump_state,
    ``Compiler.ZigAir.Control.Machine.backedge_state,
    ``Compiler.ZigAir.Control.Machine.step_preserves,
    ``Compiler.ZigAir.Control.Machine.Steps.preserves,
    ``Compiler.ZigAir.Control.Machine.run_preserves,
    ``Compiler.ZigAir.Control.Machine.finite_steps,
    ``Compiler.ZigAir.Control.Machine.finite_run,
    ``Compiler.ZigAir.Control.Machine.finite_result,
    ``Compiler.ZigAir.MemoryAir.machine_preserves_valid,
    ``Compiler.ZigAir.MemoryAir.machine_steps_preserve_valid,
    ``Compiler.ZigAir.MachineTests.zero_fuel_suspends,
    ``Compiler.ZigAir.MachineTests.repeated_effects_are_retained,
    ``Compiler.ZigAir.MachineTests.backedge_keeps_frame,
    ``Compiler.ZigAir.MachineTests.repeat_unwinds_inner_frames,
    ``Compiler.ZigAir.MachineTests.jump_exits_loop,
    ``Compiler.ZigAir.MachineTests.loop_return_skips_frames,
    ``Compiler.ZigAir.MachineTests.loop_fault_keeps_effects,
    ``Compiler.ZigAir.MachineTests.missing_repeat_target_rejects,
    ``Compiler.ZigAir.MachineTests.repeat_cannot_target_block,
    ``Compiler.ZigAir.MachineTests.jump_cannot_target_loop,
    ``Compiler.ZigAir.MachineTests.unselected_repeat_does_not_execute,
    ``Compiler.ZigAir.MachineTests.repeated_binding_observes_current_state,
    ``Compiler.ZigAir.MachineTests.resumed_loop_matches_uninterrupted,
    ``Compiler.ZigAir.MemoryAir.Invocation.resume_zero,
    ``Compiler.ZigAir.MemoryAir.Invocation.resume_finished,
    ``Compiler.ZigAir.MemoryAir.Invocation.resume_add,
    ``Compiler.ZigAir.MemoryAir.Invocation.finished_unique,
    ``Compiler.ZigAir.MemoryAir.Invocation.finish_state,
    ``Compiler.ZigAir.MemoryAir.Invocation.finish_preserves_valid,
    ``Compiler.ZigAir.MemoryAir.Invocation.resume_preserves_valid,
    ``Compiler.ZigAir.MemoryAir.Program.enableLoops_accepts,
    ``Compiler.ZigAir.MemoryAir.Program.start_state,
    ``Compiler.ZigAir.MemoryAir.Program.runFuel_preserves_valid,
    ``Compiler.ZigAir.MemoryAir.Program.runFuel_finite,
    ``Compiler.ZigAir.MemoryAir.Program.runFuel_finite_result,
    ``Compiler.ZigAir.MemoryExecutionTests.zero_budget_retains_valid_entry,
    ``Compiler.ZigAir.MemoryExecutionTests.zero_budget_rejects_bad_arguments,
    ``Compiler.ZigAir.MemoryExecutionTests.invalid_heap_rejects_before_execution,
    ``Compiler.ZigAir.MemoryExecutionTests.suspension_keeps_stack_allocation,
    ``Compiler.ZigAir.MemoryExecutionTests.return_cleans_only_current_invocation,
    ``Compiler.ZigAir.MemoryExecutionTests.resumption_keeps_original_mark,
    ``Compiler.ZigAir.MemoryExecutionTests.return_type_failure_cleans_stack,
    ``Compiler.ZigAir.MemoryExecutionTests.escaping_jump_cleans_stack,
    ``Compiler.ZigAir.MemoryExecutionTests.resumption_keeps_arguments,
    ``Compiler.ZigAir.MemoryExecutionTests.fault_keeps_prior_effects_and_cleans_current_stack,
    ``Compiler.ZigAir.MemoryExecutionTests.loop_suspension_keeps_stack,
    ``Compiler.ZigAir.MemoryExecutionTests.loop_budget_is_not_a_fault]
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
    ("schema", .str "oksolc.air-machine-audit.v1"), ("scope", .str "zigAirControlModel"),
    ("sourceSafetyVerified", .bool false), ("wholeCompilerVerified", .bool false),
    ("claims", .arr claims)]).compress
