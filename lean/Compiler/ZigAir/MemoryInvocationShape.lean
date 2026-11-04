/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryShapePreservation
import Compiler.ZigAir.MemoryWordPair

namespace Compiler.ZigAir.MemoryAir
open Memory Control.Machine

/-- All original allocations retain their metadata at every invocation budget.
Terminal cleanup uses the original mark; suspension retains the reached heap.
No initialized arguments, successful result or termination premise is needed. -/
theorem Program.runFuel_retains_shape (program : Program true) (fuel : Nat) (args : List Value)
    (state : State) (initial : state.valid = true) :
    state.heap.RetainsShape (program.runFuel fuel args state).state.heap := by
  unfold Program.runFuel Program.start
  split
  · let config : Config Ty Prim Ref Value State := ⟨program.body, fun _ => none, state, []⟩
    have reached := advance_steps semantics args fuel (.suspended config)
    have retained := machine_steps_retain_shape args _ _ reached initial
    change state.heap.RetainsShape (Control.Machine.run semantics args fuel config).state.heap at retained
    change state.heap.RetainsShape (Invocation.resume fuel (.suspended program.returnType state.nextId args config)).state.heap
    cases ran : Control.Machine.run semantics args fuel config with
    | finished outcome =>
      have shape : state.heap.RetainsShape outcome.state.heap := by
        simpa only [ran, Execution.state] using retained
      simp only [Invocation.resume, ran, Invocation.finish_state]
      exact cleanup_retains_shape state outcome.state initial shape
    | suspended next =>
      simpa only [Invocation.resume, ran, Invocation.state, Execution.state] using retained
  · exact Heap.RetainsShape.refl _

theorem WordPairProgram.retains_shape (program : WordPairProgram) (fuel : Nat) (args : List Value)
    (state : State) (initial : state.valid = true) :
    state.heap.RetainsShape (program.runFuel fuel args state).state.heap := by
  cases checked : WordPair.validate state args with
  | error fault => rw [program.rejection_retains_state fuel args state fault checked]; exact Heap.RetainsShape.refl _
  | ok value =>
    cases value
    rw [program.accepted_run fuel args state checked]
    exact Program.runFuel_retains_shape program.program fuel args state initial

end Compiler.ZigAir.MemoryAir
