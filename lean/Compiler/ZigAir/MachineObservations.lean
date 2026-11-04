/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineProofs

/-! Primitive observations of the existing machine, including failed attempts.
Each event retains the original operand environment and pre-state. Observation
uses Machine.step itself; it is not a second memory or control interpreter.
These are modeled primitive attempts, not native memory-access events. -/
namespace Compiler.ZigAir.Control.Machine

structure Observation (Ty Prim Value State : Type) where
  site : Nat × Ty × Prim
  env : Env Value
  state : State

/-- Exactly one event precedes every attempted primitive, even if it faults or
its result fails the binding's type check. Control-only steps emit none. -/
def observe (config : Config Ty Prim Ref Value State) : List (Observation Ty Prim Value State) :=
  match config.code with
  | .bind id ty prim _ => [⟨(id, ty, prim), config.env, config.state⟩]
  | .branch .. | .block .. | .loop .. | .repeat .. | .jump .. | .ret .. => []

def trace (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value) :
    Nat → Execution Ty Prim Ref Value Fault State →
      List (Observation Ty Prim Value State) × Execution Ty Prim Ref Value Fault State
  | 0, execution => ([], execution)
  | _ + 1, .finished outcome => ([], .finished outcome)
  | fuel + 1, .suspended config =>
    let next := trace sem args fuel (step sem args config)
    (observe config ++ next.1, next.2)

variable (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value)

theorem trace_erases (fuel : Nat) (execution : Execution Ty Prim Ref Value Fault State) :
    (trace sem args fuel execution).2 = advance sem args fuel execution := by
  induction fuel generalizing execution with
  | zero => rfl
  | succ fuel ih =>
    cases execution with
    | finished => rfl
    | suspended config => exact ih (step sem args config)

theorem trace_finished (fuel : Nat) (outcome : Outcome Value Fault State) :
    trace sem args fuel (.finished outcome) = ([], .finished outcome) := by
  cases fuel <;> rfl

/-- Suspension/resumption concatenates observations without repeating or losing
an attempt. Terminal executions contribute no new events. -/
theorem trace_add (first second : Nat) (execution : Execution Ty Prim Ref Value Fault State) :
    trace sem args (first + second) execution =
      let left := trace sem args first execution
      let right := trace sem args second left.2
      (left.1 ++ right.1, right.2) := by
  induction first generalizing execution with
  | zero => simp only [Nat.zero_add, trace, List.nil_append]
  | succ first ih =>
    cases execution with
    | finished outcome => simp only [trace_finished, List.nil_append]
    | suspended config => simp only [Nat.succ_add, trace, ih, List.append_assoc]

theorem trace_bind (fuel id : Nat) (ty : Ty) (prim : Prim) (next : Code Ty Prim Ref true)
    (env : Env Value) (state : State) (frames : List (Frame Ty Prim Ref)) :
    (trace sem args (fuel + 1) (.suspended ⟨.bind id ty prim next, env, state, frames⟩)).1 =
      ⟨(id, ty, prim), env, state⟩ ::
        (trace sem args fuel (step sem args ⟨.bind id ty prim next, env, state, frames⟩)).1 := rfl

theorem trace_bind_fault (fuel id : Nat) (ty : Ty) (prim : Prim) (next : Code Ty Prim Ref true)
    (env : Env Value) (state after : State) (frames : List (Frame Ty Prim Ref)) (fault : Fault)
    (evaluated : sem.evalPrim prim args env state = (.error fault, after)) :
    trace sem args (fuel + 1) (.suspended ⟨.bind id ty prim next, env, state, frames⟩) =
      ([⟨(id, ty, prim), env, state⟩], .finished (.fault fault after)) := by
  simp only [trace, step, evaluated, trace_finished, observe, List.append_nil]

theorem trace_bind_bad_type (fuel id : Nat) (ty : Ty) (prim : Prim) (next : Code Ty Prim Ref true)
    (env : Env Value) (state after : State) (frames : List (Frame Ty Prim Ref)) (value : Value)
    (evaluated : sem.evalPrim prim args env state = (.ok value, after)) (bad : sem.hasType value ty = false) :
    trace sem args (fuel + 1) (.suspended ⟨.bind id ty prim next, env, state, frames⟩) =
      ([⟨(id, ty, prim), env, state⟩], .finished (.fault sem.malformed after)) := by
  simp only [trace, step, evaluated, bad, Bool.false_eq_true, ↓reduceIte, trace_finished, observe, List.append_nil]

/-- Every retained environment/state belongs to an actual reachable primitive
attempt; neither unselected branches nor terminal padding manufacture events. -/
theorem trace_reachable (fuel : Nat) (execution : Execution Ty Prim Ref Value Fault State)
    (event : Observation Ty Prim Value State) (present : event ∈ (trace sem args fuel execution).1) :
    ∃ config, Steps sem args execution (.suspended config) ∧ observe config = [event] := by
  induction fuel generalizing execution with
  | zero => simp [trace] at present
  | succ fuel ih =>
    cases execution with
    | finished outcome => simp [trace] at present
    | suspended config =>
      have member : event ∈ observe config ∨ event ∈ (trace sem args fuel (step sem args config)).1 := by
        simpa only [trace, List.mem_append] using present
      rcases member with here | later
      · refine ⟨config, .refl _, ?_⟩
        cases code : config.code <;> simp_all [observe]
      · obtain ⟨next, reached, observed⟩ := ih (step sem args config) later
        exact ⟨next, .step config reached, observed⟩

end Compiler.ZigAir.Control.Machine
