/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExecution
import Compiler.ZigAir.MemoryMachine
import Compiler.ZigAir.MachineRefinement

namespace Compiler.ZigAir.MemoryAir
open Memory Control.Machine

theorem Invocation.resume_zero (invocation : Invocation) : invocation.resume 0 = invocation := by
  cases invocation <;> rfl

theorem Invocation.resume_finished (fuel : Nat) (result : Except Fault Value) (state : State) :
    (Invocation.finished result state).resume fuel = .finished result state := rfl

/-- Resumption preserves the original invocation boundary across budget splits. -/
theorem Invocation.resume_add (first second : Nat) (invocation : Invocation) :
    invocation.resume (first + second) = (invocation.resume first).resume second := by
  cases invocation with
  | finished result state => rfl
  | suspended returnType mark args config =>
    simp only [Invocation.resume, run, advance_add]
    cases h : advance semantics args first (.suspended config) <;>
      simp only [advance_finished, Invocation.finish]

theorem Invocation.finished_unique (invocation : Invocation) (first second : Nat)
    (left right : Except Fault Value) (leftState rightState : State)
    (hleft : invocation.resume first = .finished left leftState)
    (hright : invocation.resume second = .finished right rightState) :
    (left, leftState) = (right, rightState) := by
  have leftDone : invocation.resume (first + second) = .finished left leftState := by
    rw [Invocation.resume_add, hleft, Invocation.resume_finished]
  have rightDone : invocation.resume (first + second) = .finished right rightState := by
    rw [Nat.add_comm, Invocation.resume_add, hright, Invocation.resume_finished]
  have same := leftDone.symm.trans rightDone
  injection same with values states
  exact Prod.ext values states

theorem Invocation.finish_state (returnType : Ty) (mark : Nat) (outcome : Control.Outcome Value Fault State) :
    (Invocation.finish returnType mark outcome).state = cleanup mark outcome.state := by
  cases outcome <;> rfl

theorem Invocation.finish_preserves_valid (returnType : Ty) (mark : Nat)
    (outcome : Control.Outcome Value Fault State) (initial : outcome.state.valid = true) :
    (Invocation.finish returnType mark outcome).state.valid = true := by
  rw [Invocation.finish_state]
  exact cleanup_preserves_valid mark _ initial

theorem Invocation.resume_preserves_valid (fuel : Nat) (invocation : Invocation)
    (initial : invocation.state.valid = true) : (invocation.resume fuel).state.valid = true := by
  cases invocation with
  | finished result state => exact initial
  | suspended returnType mark args config =>
    have valid := machine_preserves_valid args fuel config initial
    cases h : run semantics args fuel config with
    | finished outcome =>
      have afterValid : outcome.state.valid = true := by simpa only [h, Execution.state] using valid
      simpa only [Invocation.resume, h] using Invocation.finish_preserves_valid returnType mark outcome afterValid
    | suspended next => simpa only [Invocation.resume, h, Invocation.state] using valid

theorem Program.enableLoops_accepts (program : Program) (args : List Value) (state : State) :
    program.enableLoops.accepts args state = program.accepts args state := rfl

theorem Program.start_state (program : Program true) (args : List Value) (state : State) :
    (program.start args state).state = state := by
  unfold Program.start
  split <;> rfl

theorem Program.runFuel_preserves_valid (program : Program true) (fuel : Nat) (args : List Value)
    (state : State) (initial : state.valid = true) : (program.runFuel fuel args state).state.valid = true := by
  apply Invocation.resume_preserves_valid
  simpa only [Program.start_state] using initial

/-- Every finite invocation reaches exactly the original result and cleaned
heap, including invalid arguments, invalid initial heaps and all runtime faults. -/
theorem Program.runFuel_finite (program : Program) (args : List Value) (state : State) :
    ∃ fuel, program.enableLoops.runFuel fuel args state =
      .finished (program.run args state).1 (program.run args state).2 := by
  by_cases accepted : program.accepts args state = true
  · obtain ⟨fuel, done⟩ := finite_run semantics args program.body (fun _ => none) state
    refine ⟨fuel, ?_⟩
    simp only [Program.runFuel, Program.start, Program.enableLoops_accepts, accepted, ↓reduceIte,
      Invocation.resume]
    change (match Control.Machine.run semantics args fuel ⟨program.body.enableLoops, fun _ => none, state, []⟩ with
      | .finished outcome => Invocation.finish program.returnType state.nextId outcome
      | .suspended next => .suspended program.returnType state.nextId args next) = _
    rw [done]
    simp only [Invocation.finish, Program.run, accepted, ↓reduceIte]
  · refine ⟨0, ?_⟩
    simp only [Program.runFuel, Program.start, Program.enableLoops_accepts, if_neg accepted,
      Invocation.resume, Program.run]

/-- Any observed terminal result for finite code agrees with the original API;
a caller cannot change that result by selecting a different sufficient budget. -/
theorem Program.runFuel_finite_result (program : Program) (args : List Value) (state : State)
    (fuel : Nat) (result : Except Fault Value) (after : State)
    (done : program.enableLoops.runFuel fuel args state = .finished result after) :
    (result, after) = program.run args state := by
  obtain ⟨budget, expected⟩ := program.runFuel_finite args state
  exact Invocation.finished_unique (program.enableLoops.start args state) fuel budget
    result (program.run args state).1 after (program.run args state).2 done expected

end Compiler.ZigAir.MemoryAir
