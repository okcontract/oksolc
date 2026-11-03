/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryLoopTests
import Compiler.ZigAir.MemoryPointers
import Compiler.ZigAir.MemoryFillInvocationTests
import Contract.Check.Declarations
import Lean.Elab.Command

open Lean Elab Command Contract.Check in
run_cmd do
  let roots := #[
    ``Compiler.ZigAir.MemoryLoopTests.fill_zero,
    ``Compiler.ZigAir.MemoryLoopTests.fill_one,
    ``Compiler.ZigAir.MemoryLoopTests.fill_all,
    ``Compiler.ZigAir.MemoryLoopTests.copy_zero,
    ``Compiler.ZigAir.MemoryLoopTests.copy_same,
    ``Compiler.ZigAir.MemoryLoopTests.copy_forward_overlap,
    ``Compiler.ZigAir.MemoryLoopTests.copy_backward_overlap,
    ``Compiler.ZigAir.MemoryLoopTests.nested_no_rows,
    ``Compiler.ZigAir.MemoryLoopTests.nested_no_columns,
    ``Compiler.ZigAir.MemoryLoopTests.nested_immediate,
    ``Compiler.ZigAir.MemoryLoopTests.nested_continue,
    ``Compiler.ZigAir.MemoryLoopTests.nested_full,
    ``Compiler.ZigAir.MemoryLoopTests.fill_fault_keeps_prefix,
    ``Compiler.ZigAir.MemoryLoopTests.indexed_pointer_requires_complete_element,
    ``Compiler.ZigAir.MemoryLoopTests.indexed_pointer_preserves_readonly,
    ``Compiler.ZigAir.MemoryLoopTests.fill_zero_does_not_dereference,
    ``Compiler.ZigAir.MemoryLoopTests.fill_dead_pointer_fault_cleans_stack,
    ``Compiler.ZigAir.MemoryLoopTests.fill_suspends_with_stack,
    ``Compiler.ZigAir.MemoryLoopTests.fill_resumes,
    ``Compiler.ZigAir.Memory.elementPointer_address,
    ``Compiler.ZigAir.MemoryAir.Program.runFuel_preserves_valid,
    ``Compiler.ZigAir.Control.Code.finite_enableLoops,
    ``Compiler.ZigAir.Control.Code.finite_sound,
    ``Compiler.ZigAir.MemoryFill.generated_loop_body,
    ``Compiler.ZigAir.MemoryFill.generated_head,
    ``Compiler.ZigAir.MemoryFill.head_continue,
    ``Compiler.ZigAir.MemoryFill.step_reads,
    ``Compiler.ZigAir.MemoryFill.loop_effects,
    ``Compiler.ZigAir.MemoryFill.entry_shape,
    ``Compiler.ZigAir.MemoryFill.initialized_fill_steps,
    ``Compiler.ZigAir.MemoryFill.initialized_fill_terminates,
    ``Compiler.ZigAir.MemoryFill.initialized_fill_result,
    ``Compiler.ZigAir.Memory.allocate_shape,
    ``Compiler.ZigAir.Memory.allocate_pointer,
    ``Compiler.ZigAir.Memory.load_after_allocate,
    ``Compiler.ZigAir.Memory.store_keeps_counters,
    ``Compiler.ZigAir.Memory.pointerCast_readonly_of_load,
    ``Compiler.ZigAir.Control.Machine.Steps.bind_ok,
    ``Compiler.ZigAir.Control.Machine.Steps.bind_fault,
    ``Compiler.ZigAir.MemoryFill.generated_prologue,
    ``Compiler.ZigAir.MemoryFill.fill_body_steps,
    ``Compiler.ZigAir.MemoryFill.fill_accepts,
    ``Compiler.ZigAir.MemoryFill.fill_terminates,
    ``Compiler.ZigAir.MemoryFill.fill_result,
    ``Compiler.ZigAir.MemoryFill.specification_cleanup,
    ``Compiler.ZigAir.MemoryFill.fill_nonempty_witness,
    ``Compiler.ZigAir.MemoryFill.fill_first_allocation_oom,
    ``Compiler.ZigAir.MemoryFill.fill_second_allocation_oom]
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
    ("schema", .str "oksolc.air-loop-audit.v1"), ("scope", .str "zigFreshAir"),
    ("sourceSafetyVerified", .bool false), ("wholeCompilerVerified", .bool false),
    ("claims", .arr claims)]).compress
